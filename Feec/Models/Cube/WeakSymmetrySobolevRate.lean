module

public import Feec.Models.Cube.WeakSymmetryConvergence
public import Feec.Models.Cube.WeakSymmetryTangentialRate
public import Feec.Models.Cube.SobolevRate

/-!
# Sobolev-data rates for the BGG elements of Tables 5.1 / 6.1 with the thesis' boundary conditions

[QuennevilleBelair2015], Thm 5.5 and §6.3: rates for the static problem (5.3) and the
semi-discrete scheme (6.5) on `Q = (0, ½)³` with the elements of Tables 5.1 / 6.1 and the thesis'
boundary conditions, for data in relative-class Sobolev spaces `Hˢ` instead of `C²`.

**The class.** `SobRel s L k x`: the relative parity extension of the `k`-form `x` (vanishing
tangential traces, `Feec.Models.Cube.Sobolev.sobolevPar Finset.univ`) lies in `Hˢ(𝕋³)` with norm
`≤ L`. `IsSobolevStateTr` asks it of every field whose projection error enters the Strang data of
(6.4): `σ, dφₐ, uₐ, duₐ, M, ρₐ, S¹u`. `S¹u` is a separate field: `S¹` does not preserve the
relative class (it couples components of opposite parities).

**Rates.** The relative-class best approximation `infDist_polyPartial_le_sobolevPar_min` and the
uniformly bounded smoothed projections ([AFW2010], §5.4) give `CubeClose` with `h^{min(s,1)}`
(`cubeClose_of_isSobolevStateTr`), hence the static rate `staticFEM_rate_sobolev` (Thm 5.5) and the
rate `cubeWave_rate_sobolev` of (6.5), `K L (1 + t) h^{min(s,1)}`. The exponent `min(s, 1)` is
optimal for these elements: `P₁⁻Λ̊²` reproduces only constants (`r_eff = 1`); the lower bounds are
standard and not formalized.

**Gaffney on the cube.** Through `HQmin_eq_compress` (minimal complex of `Q` = compression of the
torus window along the relative parity), `x ∈ D(d) ∩ D(d*)` in degree `k` gives `x ∈ H¹_univ`
with `‖x‖²_{1,univ} = ‖x‖² + ‖dx‖² + ‖d*x‖²` (`gaffney_RT`, `gaffney_HQmin`, `sobRel_zero_of_mem`,
`sobRel_one_of_mem`, `sobRel_two_of_mem`).

**Non-vacuity below `H^{1/2}`.** The sawtooth 2-form `sawW2` (`f(y₀) dy₁ ∧ dy₂`, `f` the odd
`½`-periodic sawtooth) satisfies `d¹* sawW2 = 0`, lies in `Hˢ_univ` exactly for `s < ½`, and is not
in `H̊Λ²(Q)`. The stationary state `sawWave T` (`ρ = (sawW2, 0, 0)`) is a classical solution of
(6.2) satisfying every hypothesis of `cubeWave_rate_sobolev` for `0 ≤ s < ½`, outside every class
`IsSmoothStateTr` of `cubeWave_rate_tr` (`cubeWave_rate_sobolev_nonvacuous`).

## Main results

* `cubeClose_of_isSobolevStateTr`: projection errors `O(L h^{min(s,1)})`.
* **`staticFEM_rate_sobolev`**: Thm 5.5 for relative-class `Hˢ` data, with `‖λ‖ ≤ L` and
  `S¹u ∈ D(d¹*)` (`|⟪S¹u, d w⟫| ≤ L ‖w‖`) as hypotheses.
* **`cubeWave_rate_sobolev`**: the rate `K L (1 + t) h^{min(s,1)}` of (6.5); the hypotheses beyond
  `IsSobolevStateTr` (`M, M' ∈ D(d¹*)`, `L²`-bounded multipliers) are those of `cubeWave_rate_tr`.
* `gaffney_HQmin`, `sobRel_one_of_mem`, `sobRel_two_of_mem`: Gaffney's identity on the cube.
* **`cubeWave_rate_sobolev_nonvacuous`**: the rate `h^s`, `s < ½`, for the sawtooth solution, which
  is not in `H^{1/2}` and in no `C²` class.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 5.5 ((5.3), (5.6), Table 5.1), §6.3 ((6.4), (6.5), Table 6.1)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  Thm 3.9, §4.3 (Gaffney's inequality), §5.4
-/

open scoped InnerProductSpace RealInnerProductSpace LinearPMap
open MeasureTheory Set Filter

@[expose] public noncomputable section

namespace Feec.Models.Cube.WeakSymmetry

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex Feec.Models.Cube.FEM
open Feec.Models.Cube.Sobolev

/-! ### Relative-class Sobolev data -/

/-- **Relative-class `Hˢ` data with bound `L`** in degree `k` on the cube: the relative parity
extension (vanishing tangential traces) of `x` lies in `Hˢ(𝕋³)` and `‖x‖_{s,univ} ≤ L`
(`Sobolev.sobolevPar Finset.univ`, `Sobolev.parNorm`). -/
def SobRel (s L : ℝ) (k : ℕ) (x : L2F ℝ (cubeDomain 3) (formIdx 3 k)) : Prop :=
  toQ k x ∈ sobolevPar Finset.univ k s ∧ parNorm Finset.univ k s (toQ k x) ≤ L

theorem SobRel.norm_le {s L : ℝ} {k : ℕ} {x : L2F ℝ (cubeDomain 3) (formIdx 3 k)}
    (hx : SobRel s L k x) (hs : 0 ≤ s) : ‖x‖ ≤ L := by
  have h := norm_le_parNorm Finset.univ k hs hx.1
  rw [LinearIsometryEquiv.norm_map] at h
  exact h.trans hx.2

theorem SobRel.nonneg {s L : ℝ} {k : ℕ} {x : L2F ℝ (cubeDomain 3) (formIdx 3 k)}
    (hx : SobRel s L k x) : 0 ≤ L :=
  (parNorm_nonneg _ _ _ _).trans hx.2

theorem SobRel.mono {s L L' : ℝ} {k : ℕ} {x : L2F ℝ (cubeDomain 3) (formIdx 3 k)}
    (hx : SobRel s L k x) (h : L ≤ L') : SobRel s L' k x :=
  ⟨hx.1, hx.2.trans h⟩

theorem sobRel_zero {s L : ℝ} (hL : 0 ≤ L) (k : ℕ) :
    SobRel s L k (0 : L2F ℝ (cubeDomain 3) (formIdx 3 k)) := by
  refine ⟨by rw [map_zero]; exact Submodule.zero_mem _, ?_⟩
  rw [map_zero, parNorm, map_zero]
  simpa [sobSum, cf_zero] using hL

/-! ### Projection errors of the smoothed projections for relative-class data -/

section ProjSob

variable {S : PolySeq} {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}

/-- **Quasi-optimality of the smoothed projections for `Hˢ` data with vanishing tangential
traces**: `‖x − π x‖ ≤ (1 + 2C) C_S h_N^{min(s,1)} L` for `x ∈ Hˢ_univ` with `‖x‖_{s,univ} ≤ L`
(`norm_sub_π_le_infDist`, `infDist_polyPartial_le_sobolevPar_min` with `J = univ`). -/
theorem norm_sub_proj_le_of_sobRel (hE : PolySmoothingEstimatesMin 3 S p C) (N k : ℕ) {s L : ℝ}
    (hs0 : 0 ≤ s) {x : L2F ℝ (cubeDomain 3) (formIdx 3 k)} (hx : SobRel s L k x) :
    ‖x - (hE.proj N).π k x‖ ≤ (1 + 2 * C) * sobConstPar 3 S k * meshSize N ^ min s 1 * L := by
  have hA : 0 ≤ 1 + 2 * C := by linarith [hE.two_mul_nonneg]
  have h1 := norm_sub_π_le_infDist (hE.proj N) hE.two_mul_nonneg (hE.norm_proj_le N k) x
  have h2 := infDist_polyPartial_le_sobolevPar_min S Finset.univ k hs0 N x hx.1
  rw [polyPartial_univ_V] at h2
  have h3 : sobConstPar 3 S k * meshSize N ^ min s 1 * parNorm Finset.univ k s (toQ k x) ≤
      sobConstPar 3 S k * meshSize N ^ min s 1 * L :=
    mul_le_mul_of_nonneg_left hx.2
      (mul_nonneg (sobConstPar_nonneg S k) (Real.rpow_nonneg (meshSize_pos N).le _))
  calc ‖x - (hE.proj N).π k x‖ ≤ (1 + 2 * C) * Metric.infDist x ((polyMin 3 S N).V k) := h1
    _ ≤ (1 + 2 * C) * (sobConstPar 3 S k * meshSize N ^ min s 1 * L) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) hA
    _ = _ := by ring

end ProjSob

/-- `h_N ≤ h_N^{min(s,1)}` (`h_N ≤ ½`). -/
theorem meshSize_le_rpow_min (s : ℝ) (N : ℕ) : meshSize N ≤ meshSize N ^ min s 1 := by
  have hh := meshSize_pos N
  have h1 : meshSize N ≤ 1 := (meshSize_le_half N).trans (by norm_num)
  calc meshSize N = meshSize N ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ meshSize N ^ min s 1 := Real.rpow_le_rpow_of_exponent_ge hh h1 (min_le_right _ _)

theorem rpow_min_nonneg (s : ℝ) (N : ℕ) : 0 ≤ meshSize N ^ min s 1 :=
  Real.rpow_nonneg (meshSize_pos N).le _

/-! ### The Sobolev class of exact states and closeness to the projections -/

/-- **Relative-class `Hˢ` regularity of an exact state** `(σ, φ, u, M, ρ)` of (6.4)/(6.5)
(Table 6.1 with the thesis' boundary conditions): `σ`, `dφₐ`, `uₐ`, `duₐ`, `M`, `ρₐ` and `S¹u` lie
in the relative parity class `Hˢ_univ` (vanishing tangential traces) with norms `≤ L`. These are
exactly the fields whose projection errors make up the Strang data of (6.4) (`CubeClose`). -/
def IsSobolevStateTr (s L : ℝ) (σ : U0) (φ : Wv U0) (u : Wv U1) (M : W2) (ρ : Wv W2) : Prop :=
  SobRel s L 0 (σ : W0) ∧ (∀ a, SobRel s L 1 (D0 (φ a))) ∧ (∀ a, SobRel s L 1 (u a : W1)) ∧
    (∀ a, SobRel s L 2 (D1 (u a))) ∧ SobRel s L 2 M ∧ (∀ a, SobRel s L 2 (ρ a)) ∧
    SobRel s L 2 (bggSegment.S1 u)

theorem IsSobolevStateTr.mono {s L L' : ℝ} {σ : U0} {φ : Wv U0} {u : Wv U1} {M : W2}
    {ρ : Wv W2} (h : IsSobolevStateTr s L σ φ u M ρ) (hLL' : L ≤ L') :
    IsSobolevStateTr s L' σ φ u M ρ :=
  ⟨h.1.mono hLL', fun a => (h.2.1 a).mono hLL', fun a => (h.2.2.1 a).mono hLL',
    fun a => (h.2.2.2.1 a).mono hLL', h.2.2.2.2.1.mono hLL', fun a => (h.2.2.2.2.2.1 a).mono hLL',
    h.2.2.2.2.2.2.mono hLL'⟩

/-- The constant of `cubeClose_of_isSobolevStateTr`. -/
def sobStateConst (C : ℝ) : ℝ :=
  (1 + 2 * C) * ∑ k ∈ Finset.range 3,
    (sobConstPar 3 PolySeq.lowestOrder k + sobConstPar 3 PolySeq.lagrangeP2 k)

theorem sobConstPar_le_sum {S : PolySeq}
    (hS : S = PolySeq.lowestOrder ∨ S = PolySeq.lagrangeP2) {k : ℕ} (hk : k < 3) :
    sobConstPar 3 S k ≤ ∑ j ∈ Finset.range 3,
      (sobConstPar 3 PolySeq.lowestOrder j + sobConstPar 3 PolySeq.lagrangeP2 j) := by
  have h0 := sobConstPar_nonneg (n := 3) PolySeq.lowestOrder k
  have h1 := sobConstPar_nonneg (n := 3) PolySeq.lagrangeP2 k
  have hterm : sobConstPar 3 S k ≤
      sobConstPar 3 PolySeq.lowestOrder k + sobConstPar 3 PolySeq.lagrangeP2 k := by
    rcases hS with rfl | rfl <;> linarith
  refine hterm.trans (Finset.single_le_sum
    (f := fun j => sobConstPar 3 PolySeq.lowestOrder j + sobConstPar 3 PolySeq.lagrangeP2 j)
    (fun j _ => add_nonneg (sobConstPar_nonneg _ _) (sobConstPar_nonneg _ _))
    (Finset.mem_range.2 hk))

section CubeFEM

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

include hT in
theorem sobStateConst_nonneg : 0 ≤ sobStateConst C := by
  have := hT.two_mul_nonneg
  have : 0 ≤ ∑ k ∈ Finset.range 3,
      (sobConstPar 3 PolySeq.lowestOrder k + sobConstPar 3 PolySeq.lagrangeP2 k) :=
    Finset.sum_nonneg fun j _ => add_nonneg (sobConstPar_nonneg _ _) (sobConstPar_nonneg _ _)
  unfold sobStateConst; positivity

include hT in
theorem le_sobStateConst_mul {S : PolySeq} (hS : S = PolySeq.lowestOrder ∨ S = PolySeq.lagrangeP2)
    {k : ℕ} (hk : k < 3) (X : ℝ) (hX : 0 ≤ X) :
    (1 + 2 * C) * sobConstPar 3 S k * X ≤ sobStateConst C * X := by
  have hA : 0 ≤ 1 + 2 * C := by linarith [hT.two_mul_nonneg]
  unfold sobStateConst
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (sobConstPar_le_sum hS hk) hA) hX

include hT in
/-- The projection error of a relative-class field for one of the two element families of
Table 5.1, in degrees `0, 1, 2`. -/
theorem norm_sub_proj_le_sobStateConst {S : PolySeq} (hE : PolySmoothingEstimatesMin 3 S p C)
    (hS : S = PolySeq.lowestOrder ∨ S = PolySeq.lagrangeP2) (N : ℕ) {k : ℕ} (hk : k < 3)
    {s L : ℝ} (hs0 : 0 ≤ s) {x : L2F ℝ (cubeDomain 3) (formIdx 3 k)} (hx : SobRel s L k x) :
    ‖x - (hE.proj N).π k x‖ ≤ sobStateConst C * meshSize N ^ min s 1 * L := by
  have hX : 0 ≤ meshSize N ^ min s 1 * L := mul_nonneg (rpow_min_nonneg s N) hx.nonneg
  refine (norm_sub_proj_le_of_sobRel hE N k hs0 hx).trans ?_
  have := le_sobStateConst_mul hT hS hk (meshSize N ^ min s 1 * L) hX
  calc (1 + 2 * C) * sobConstPar 3 S k * meshSize N ^ min s 1 * L =
      (1 + 2 * C) * sobConstPar 3 S k * (meshSize N ^ min s 1 * L) := by ring
    _ ≤ sobStateConst C * (meshSize N ^ min s 1 * L) := this
    _ = _ := by ring

/-- **A relative-class `Hˢ` state is `δ`-close to its projections with
`δ = C h_N^{min(s,1)} L`** (`CubeClose`): every projection error of the Strang data of (6.4) is
bounded by the quasi-optimality of the uniformly bounded smoothed projections
(`norm_sub_proj_le_of_sobRel`). -/
theorem cubeClose_of_isSobolevStateTr (N : ℕ) {s L : ℝ} (hs0 : 0 ≤ s) {σ : U0} {φ : Wv U0}
    {u : Wv U1} {M : W2} {ρ : Wv W2} (h : IsSobolevStateTr s L σ φ u M ρ) :
    CubeClose hT hB N (sobStateConst C * meshSize N ^ min s 1 * L) σ φ u M ρ := by
  obtain ⟨hσ, hφ, hu, hdu, hM, hρ, hSu⟩ := h
  have lT : PolySeq.lowestOrder = PolySeq.lowestOrder ∨ PolySeq.lowestOrder = PolySeq.lagrangeP2 :=
    Or.inl rfl
  have lB : PolySeq.lagrangeP2 = PolySeq.lowestOrder ∨ PolySeq.lagrangeP2 = PolySeq.lagrangeP2 :=
    Or.inr rfl
  exact ⟨norm_sub_proj_le_sobStateConst hT hT lT N (by norm_num) hs0 hσ,
    fun a => norm_sub_proj_le_sobStateConst hT hB lB N (by norm_num) hs0 (hφ a),
    fun a => norm_sub_proj_le_sobStateConst hT hB lB N (by norm_num) hs0 (hu a),
    fun a => norm_sub_proj_le_sobStateConst hT hB lB N (by norm_num) hs0 (hdu a),
    norm_sub_proj_le_sobStateConst hT hT lT N (by norm_num) hs0 hM,
    fun a => norm_sub_proj_le_sobStateConst hT hB lB N (by norm_num) hs0 (hρ a),
    norm_sub_proj_le_sobStateConst hT hT lT N (by norm_num) hs0 hSu⟩

/-! ### Graph-norm projection errors from closeness -/

theorem graphSq_P0_sub_le_of_close (N : ℕ) {δ : ℝ} (σ : U0)
    (h1 : ‖(σ : W0) - (hT.proj N).π 0 (σ : W0)‖ ≤ δ)
    (h2 : ‖D0 σ - (hT.proj N).π 1 (D0 σ)‖ ≤ δ) :
    Feec.BGG.graphSq bggSegment.d0 ((cubeFEM hT hB N).P0 σ - σ) ≤ 2 * δ ^ 2 := by
  have a1 : ‖(cubeFEM hT hB N).P0 σ - σ‖ ≤ δ := by
    change ‖(hT.proj N).π 0 (σ : W0) - (σ : W0)‖ ≤ δ
    rw [norm_sub_rev]; exact h1
  have a2 : ‖bggSegment.d0 ((cubeFEM hT hB N).P0 σ - σ)‖ ≤ δ := by
    have e : ‖bggSegment.d0 ((cubeFEM hT hB N).P0 σ - σ)‖ =
        ‖(hT.proj N).π 1 (D0 σ) - D0 σ‖ := by
      change ‖D0 (projU0 (hT.proj N) σ - σ)‖ = _
      rw [LinearPMap.map_sub]
      congr 2
      exact D0_π (hT.proj N) σ
    rw [e, norm_sub_rev]; exact h2
  unfold Feec.BGG.graphSq
  have := pow_le_pow_left₀ (norm_nonneg _) a1 2
  have := pow_le_pow_left₀ (norm_nonneg _) a2 2
  linarith

theorem graphSq_Pt0_sub_le_of_close (N : ℕ) {δ : ℝ} (φ : Wv U0)
    (h1 : ∀ a, ‖(φ a : W0) - (hB.proj N).π 0 (φ a : W0)‖ ≤ δ)
    (h2 : ∀ a, ‖D0 (φ a) - (hB.proj N).π 1 (D0 (φ a))‖ ≤ δ) :
    Feec.BGG.graphSq bggSegment.dt0 ((cubeFEM hT hB N).Pt0 φ - φ) ≤ 2 * (3 * δ ^ 2) := by
  have a1 : ‖(cubeFEM hT hB N).Pt0 φ - φ‖ ^ 2 ≤ 3 * δ ^ 2 := by
    rw [norm_sq_wv]
    refine sum_sq_le_three' fun a => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    change ‖(hB.proj N).π 0 (φ a : W0) - (φ a : W0)‖ ≤ _
    rw [norm_sub_rev]
    exact h1 a
  have a2 : ‖bggSegment.dt0 ((cubeFEM hT hB N).Pt0 φ - φ)‖ ^ 2 ≤ 3 * δ ^ 2 := by
    rw [norm_sq_wv]
    refine sum_sq_le_three' fun a => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    have e : ‖(bggSegment.dt0 ((cubeFEM hT hB N).Pt0 φ - φ)) a‖ =
        ‖(hB.proj N).π 1 (D0 (φ a)) - D0 (φ a)‖ := by
      change ‖D0 (projU0 (hB.proj N) (φ a) - φ a)‖ = _
      rw [LinearPMap.map_sub]
      congr 2
      exact D0_π (hB.proj N) (φ a)
    rw [e, norm_sub_rev]
    exact h2 a
  unfold Feec.BGG.graphSq
  linarith

theorem gnSq_Pt1_sub_le_of_close (N : ℕ) {δ : ℝ} (u : Wv U1)
    (h1 : ∀ a, ‖(u a : W1) - (hB.proj N).π 1 (u a : W1)‖ ≤ δ)
    (h2 : ∀ a, ‖D1 (u a) - (hB.proj N).π 2 (D1 (u a))‖ ≤ δ) :
    (cubeFEM hT hB N).gnSq ((cubeFEM hT hB N).Pt1 u - u) ≤ (1 + 8 * C ^ 2) * (2 * (3 * δ ^ 2)) := by
  have a1 : ‖(cubeFEM hT hB N).Pt1 u - u‖ ^ 2 ≤ 3 * δ ^ 2 := by
    rw [norm_sq_wv]
    refine sum_sq_le_three' fun a => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    change ‖(hB.proj N).π 1 (u a : W1) - (u a : W1)‖ ≤ _
    rw [norm_sub_rev]
    exact h1 a
  have a2 : ‖bggSegment.dt1 ((cubeFEM hT hB N).Pt1 u - u)‖ ^ 2 ≤ 3 * δ ^ 2 := by
    rw [norm_sq_wv]
    refine sum_sq_le_three' fun a => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    have e : ‖(bggSegment.dt1 ((cubeFEM hT hB N).Pt1 u - u)) a‖ =
        ‖(hB.proj N).π 2 (D1 (u a)) - D1 (u a)‖ := by
      change ‖D1 (projU1 (hB.proj N) (u a) - u a)‖ = _
      rw [LinearPMap.map_sub]
      congr 2
      exact D1_π (hB.proj N) (u a)
    rw [e, norm_sub_rev]
    exact h2 a
  have hg : Feec.BGG.graphSq bggSegment.dt1 ((cubeFEM hT hB N).Pt1 u - u) ≤ 2 * (3 * δ ^ 2) := by
    unfold Feec.BGG.graphSq; linarith
  exact (cubeFEM_gnSq_le hT hB N _).trans
    (mul_le_mul_of_nonneg_left hg (by positivity))

/-! ### Thm 5.5 for relative-class Sobolev data -/

/-- **Relative-class `Hˢ` regularity of a solution of (5.3)**: `σ`, `dσ`, `φₐ`, `dφₐ`, `uₐ`, `duₐ`
and `S¹u` lie in `Hˢ_univ` (vanishing tangential traces) with norms `≤ L` (the graph-norm
projection errors of Thm 5.5). -/
def IsSobolevStaticTr (s L : ℝ) (σ : U0) (φ : Wv U0) (u : Wv U1) : Prop :=
  SobRel s L 0 (σ : W0) ∧ SobRel s L 1 (D0 σ) ∧ (∀ a, SobRel s L 0 (φ a : W0)) ∧
    (∀ a, SobRel s L 1 (D0 (φ a))) ∧ (∀ a, SobRel s L 1 (u a : W1)) ∧
    (∀ a, SobRel s L 2 (D1 (u a))) ∧ SobRel s L 2 (bggSegment.S1 u)

set_option maxHeartbeats 8000000 in
/-- **Thm 5.5 on the cube with the elements of Table 5.1 for Sobolev data with the thesis'
boundary conditions** ([QuennevilleBelair2015], Thm 5.5, the static problem (5.3); unconditional:
the regularity hypothesis is `curlPotential`): there is `K`, independent of `N`, `s` and the
solution, such that for every `s ≥ 0`, every solution `(σ, φ, u, λ)` of (5.3) whose fields `σ, dσ,
φₐ, dφₐ, uₐ, duₐ, S¹u` are in the relative class `Hˢ_univ` with norms `≤ L` (`IsSobolevStaticTr`),
with `‖λ‖ ≤ L` and `|⟪S¹u, d w⟫| ≤ L ‖w‖` (`S¹u ∈ D(d¹*)`), every discrete solution of (5.6)
satisfies `‖σ − σₕ‖²_V + ‖φ − φₕ‖²_V + ‖u − uₕ‖²_{Γₕ} ≤ (K L h_N^{min(s,1)})²`. The projection
errors are those of `cubeClose_of_isSobolevStateTr` (quasi-optimality of the uniformly bounded
smoothed projections, [AFW2010], §5.4, with the relative-class best approximation
`infDist_polyPartial_le_sobolevPar_min`); the consistency terms are `O(h_N) ≤ O(h_N^{min(s,1)})`. -/
theorem staticFEM_rate_sobolev :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {σ : U0} {φ : Wv U0} {u : Wv U1} {lam : W1}
      {F : Wv U1 →ₗ[ℝ] ℝ} {s L : ℝ}, 0 ≤ s → 0 ≤ L →
      (∀ τ ψ, ⟪σ, τ⟫ - ⟪u, bggSegment.dt0 ψ⟫ -
        ⟪lam, ((bggSegment.d0 τ - bggSegment.S0 ψ : U1) : W1)⟫ = 0) →
      (∀ v, ⟪bggSegment.dt0 φ, v⟫ + ⟪bggSegment.S1 u, bggSegment.S1 v⟫ +
        ⟪bggSegment.dt1 u, bggSegment.dt1 v⟫ = F v) →
      bggSegment.d0 σ = bggSegment.S0 φ →
      IsSobolevStaticTr s L σ φ u → ‖lam‖ ≤ L →
      (∀ w : U1, |⟪bggSegment.S1 u, bggSegment.d1 w⟫| ≤ L * ‖w‖) →
      ∀ {σh : U0} {φh : Wv U0} {uh : Wv U1} {lh : U1},
      σh ∈ (cubeFEM hT hB N).V0h → φh ∈ (cubeFEM hT hB N).Vt0h →
      uh ∈ (cubeFEM hT hB N).Vt1h →
      (∀ τ ∈ (cubeFEM hT hB N).V0h, ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
        ⟪σh, τ⟫ - ⟪uh, bggSegment.dt0 ψ⟫ -
          ⟪lh, bggSegment.d0 τ - (cubeFEM hT hB N).S0h ψ⟫ = 0) →
      (∀ v ∈ (cubeFEM hT hB N).Vt1h, ⟪bggSegment.dt0 φh, v⟫ +
        ⟪(cubeFEM hT hB N).S1h uh, (cubeFEM hT hB N).S1h v⟫ +
          ⟪bggSegment.dt1 uh, bggSegment.dt1 v⟫ = F v) →
      (∀ μ ∈ (cubeFEM hT hB N).V1h, ⟪bggSegment.d0 σh - (cubeFEM hT hB N).S0h φh, μ⟫ = 0) →
      Feec.BGG.graphSq bggSegment.d0 (σ - σh) + Feec.BGG.graphSq bggSegment.dt0 (φ - φh) +
        (cubeFEM hT hB N).gnSq (u - uh) ≤ (K * L * meshSize N ^ min s 1) ^ 2 := by
  have hCR0 := curlPotentialConst_nonneg
  have hh0 := cubeFEM_happ0 hT hB
  obtain ⟨C0, hh1⟩ := hh0
  have hC00 := hh1.1
  have hhapp := hh1.2
  have hC := hT.two_mul_nonneg
  have hA : 0 ≤ 1 + 2 * C := by linarith
  have hreg := regConst_nonneg hT
  have ex_Capp : ∃ x : ℝ, x = C0 + regConst C := ⟨_, rfl⟩
  obtain ⟨Capp, hCapp_def⟩ := ex_Capp
  have hCapp0 : 0 ≤ Capp := by rw [hCapp_def]; linarith
  have ex_Cp : ∃ x : ℝ, x = (2 * Real.pi)⁻¹ := ⟨_, rfl⟩
  obtain ⟨Cp, hCp⟩ := ex_Cp
  have hCp0 : 0 ≤ Cp := by rw [hCp]; positivity
  have ex_E : ∃ x : ℝ,
      x = Feec.BGG.Discrete.errorConst Cp curlPotentialConst (Real.sqrt 2) (2 * C) Capp :=
    ⟨_, rfl⟩
  obtain ⟨E, hE_def⟩ := ex_E
  have hE0 : 0 ≤ E := by
    rw [hE_def]
    unfold Feec.BGG.Discrete.errorConst Feec.BGG.Discrete.Ca1 Feec.BGG.Discrete.Ca
      Feec.BGG.Discrete.KL Feec.BGG.Discrete.Cb
    positivity
  have ex_wa : ∃ x : ℝ, x = √(1 + Cp ^ 2) * (1 + 2 * C * (1 + 1 * curlPotentialConst)) :=
    ⟨_, rfl⟩
  obtain ⟨wa, hwa⟩ := ex_wa
  have ex_wb : ∃ x : ℝ, x = (1 + (1 + 2 * C) * Real.sqrt 2) * curlPotentialConst :=
    ⟨_, rfl⟩
  obtain ⟨wb, hwb⟩ := ex_wb
  have hwa0 : 0 ≤ wa := by rw [hwa]; positivity
  have hwb0 : 0 ≤ wb := by rw [hwb]; positivity
  have hsc := sobStateConst_nonneg hT
  have ex_Kd : ∃ x : ℝ, x = 2 * sobStateConst C ^ 2 + 2 * (3 * sobStateConst C ^ 2) +
      (1 + 8 * C ^ 2) * (2 * (3 * sobStateConst C ^ 2)) + 1 + (wa + wb) ^ 2 +
      sobStateConst C ^ 2 := ⟨_, rfl⟩
  obtain ⟨Kd, hKd⟩ := ex_Kd
  have hKd0 : 0 ≤ Kd := by rw [hKd]; positivity
  refine ⟨√(E * Kd), Real.sqrt_nonneg _, fun N σ φ u lam F s L hs0 hL0 c1 c2 c3 hsob hlam
    hz σh φh uh lh hσh hφh huh h1 h2 h3 => ?_⟩
  obtain ⟨hσ, hdσ, hφ, hdφ, hu, hdu, hSu⟩ := hsob
  have := cubeFEM_fdt1 hT hB N
  have hh : 0 ≤ meshSize N := (meshSize_pos N).le
  have H : Feec.BGG.Stability bggSegment Cp curlPotentialConst (Real.sqrt 2) := by
    rw [hCp]; exact bggStability_curlPotentialConst
  have Bd := cubeFEM_bounded hT hB N
  have h54 := cubeFEM_compatible hT hB N
  have happ : ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
      ‖bggSegment.S0 ψ - (cubeFEM hT hB N).S0h ψ‖ ^ 2 ≤
        (Capp * meshSize N) ^ 2 * Feec.BGG.graphSq bggSegment.dt0 ψ := fun ψ hψ => by
    refine (hhapp N ψ hψ).trans (mul_le_mul_of_nonneg_right ?_ (Feec.BGG.graphSq_nonneg _ _))
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right
      (by rw [hCapp_def]; linarith) hh) 2
  have Rg := cubeFEMReg hT hB N hCR0 exists_curlPotential_le
    (by rw [hCapp_def]; linarith : regConst C ≤ Capp)
  have hwc := Feec.BGG.Discrete.weakConsistency_of_regularPotential_of_bound H Bd hh hCapp0 Rg
    happ hL0 hz
  have hℓ : ∀ μ, |((innerSL ℝ lam).toLinearMap ∘ₗ D1.domain.subtype) μ| ≤ L * ‖μ‖ := fun μ =>
    (abs_real_inner_le_norm lam (μ : W1)).trans (mul_le_mul_of_nonneg_right hlam (norm_nonneg _))
  have hest := Feec.BGG.Discrete.error_estimate_of_weakConsistency H Bd h54 hh hCapp0 happ hwc
    ((innerSL ℝ lam).toLinearMap ∘ₗ D1.domain.subtype) hL0 hℓ F (fun τ _ ψ _ => c1 τ ψ)
    (fun v _ => c2 v) c3 hσh hφh huh h1 h2 h3
  have hm0 : 0 ≤ meshSize N ^ min s 1 := rpow_min_nonneg s N
  have hhm' : meshSize N ≤ meshSize N ^ min s 1 := meshSize_le_rpow_min s N
  refine hest.trans ?_
  have lT : PolySeq.lowestOrder = PolySeq.lowestOrder ∨ PolySeq.lowestOrder = PolySeq.lagrangeP2 :=
    Or.inl rfl
  have lB : PolySeq.lagrangeP2 = PolySeq.lowestOrder ∨ PolySeq.lagrangeP2 = PolySeq.lagrangeP2 :=
    Or.inr rfl
  have hD1 := graphSq_P0_sub_le_of_close hT hB N σ
    (norm_sub_proj_le_sobStateConst hT hT lT N (by norm_num) hs0 hσ)
    (norm_sub_proj_le_sobStateConst hT hT lT N (by norm_num) hs0 hdσ)
  have hD2 := graphSq_Pt0_sub_le_of_close hT hB N φ
    (fun a => norm_sub_proj_le_sobStateConst hT hB lB N (by norm_num) hs0 (hφ a))
    (fun a => norm_sub_proj_le_sobStateConst hT hB lB N (by norm_num) hs0 (hdφ a))
  have hD3 := gnSq_Pt1_sub_le_of_close hT hB N u
    (fun a => norm_sub_proj_le_sobStateConst hT hB lB N (by norm_num) hs0 (hu a))
    (fun a => norm_sub_proj_le_sobStateConst hT hB lB N (by norm_num) hs0 (hdu a))
  have hD6' : ‖bggSegment.S1 u - (cubeFEM hT hB N).S1h u‖ ≤
      sobStateConst C * meshSize N ^ min s 1 * L :=
    norm_sub_proj_le_sobStateConst hT hT lT N (by norm_num) hs0 hSu
  have hD6 := pow_le_pow_left₀ (norm_nonneg _) hD6' 2
  have hSun : ‖bggSegment.S1 u‖ ≤ L := hSu.norm_le hs0
  have hK0 : 0 ≤ Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1
      curlPotentialConst ‖bggSegment.S1 u‖ L := by
    unfold Feec.BGG.Discrete.weakConsistencyConst
    have := norm_nonneg (bggSegment.S1 u)
    positivity
  have hD5 : Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1 curlPotentialConst
      ‖bggSegment.S1 u‖ L ≤ (wa + wb) * L := by
    have e : Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1 curlPotentialConst
        ‖bggSegment.S1 u‖ L = L * wa + ‖bggSegment.S1 u‖ * wb := by
      rw [hwa, hwb]; unfold Feec.BGG.Discrete.weakConsistencyConst; ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hSun hwb0
    linarith
  have hhL : meshSize N * L ≤ meshSize N ^ min s 1 * L := mul_le_mul_of_nonneg_right hhm' hL0
  have hhL2 : (meshSize N * L) ^ 2 ≤ (meshSize N ^ min s 1 * L) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hh hL0) hhL 2
  have hD5' : meshSize N ^ 2 * Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1
      curlPotentialConst ‖bggSegment.S1 u‖ L ^ 2 ≤
        (wa + wb) ^ 2 * (meshSize N ^ min s 1 * L) ^ 2 := by
    have h1 := pow_le_pow_left₀ hK0 hD5 2
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (meshSize N))
    have h3 : meshSize N ^ 2 * ((wa + wb) * L) ^ 2 = (wa + wb) ^ 2 * (meshSize N * L) ^ 2 := by
      ring
    have h4 := mul_le_mul_of_nonneg_left hhL2 (sq_nonneg (wa + wb))
    linarith
  have hL2 : meshSize N ^ 2 * L ^ 2 ≤ (meshSize N ^ min s 1 * L) ^ 2 := by
    have e : meshSize N ^ 2 * L ^ 2 = (meshSize N * L) ^ 2 := by ring
    rw [e]; exact hhL2
  have hδ2 : (sobStateConst C * meshSize N ^ min s 1 * L) ^ 2 =
      sobStateConst C ^ 2 * (meshSize N ^ min s 1 * L) ^ 2 := by ring
  have hsum : Feec.BGG.graphSq bggSegment.d0 ((cubeFEM hT hB N).P0 σ - σ) +
      Feec.BGG.graphSq bggSegment.dt0 ((cubeFEM hT hB N).Pt0 φ - φ) +
      (cubeFEM hT hB N).gnSq ((cubeFEM hT hB N).Pt1 u - u) + meshSize N ^ 2 * L ^ 2 +
      meshSize N ^ 2 * Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1
        curlPotentialConst ‖bggSegment.S1 u‖ L ^ 2 +
      ‖bggSegment.S1 u - (cubeFEM hT hB N).S1h u‖ ^ 2 ≤ Kd * (meshSize N ^ min s 1 * L) ^ 2 := by
    have e1 := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hD1 hD2) hD3) hL2)
      hD5') hD6
    refine e1.trans (le_of_eq ?_)
    rw [hKd, hδ2]
    ring
  rw [← hE_def]
  calc E * (_ : ℝ) ≤ E * (Kd * (meshSize N ^ min s 1 * L) ^ 2) := mul_le_mul_of_nonneg_left hsum hE0
    _ = (√(E * Kd) * L * meshSize N ^ min s 1) ^ 2 := by
        rw [show (√(E * Kd) * L * meshSize N ^ min s 1) ^ 2 =
            √(E * Kd) ^ 2 * (meshSize N ^ min s 1 * L) ^ 2 by ring,
          Real.sq_sqrt (mul_nonneg hE0 hKd0)]
        ring


/-! ### The rate of (6.5) for relative-class Sobolev data -/

set_option maxHeartbeats 8000000 in
/-- **The Strang data of (6.4) for a relative-class `Hˢ` state**: with the consistency constants
`K₀ = L C₀ h_N` (an `L²`-bounded multiplier) and `K₁ = K h_N L` (`M ∈ D(d¹*)`), the Strang data
are `≤ (√Kd L h_N^{min(s,1)})²` with `Kd` independent of `N`, `s` and the state. -/
theorem cubeFEM_strangData_le_sobolev (N : ℕ) {s L : ℝ} (hs0 : 0 ≤ s) {σ : U0} {φ : Wv U0}
    {u : Wv U1} {M : W2} {ρ : Wv W2} (h : IsSobolevStateTr s L σ φ u M ρ) (C0 K1 : ℝ) :
    (cubeFEM hT hB N).strangData σ φ u M ρ (L * C0 * meshSize N) (K1 * meshSize N * L) ≤
      (√(cubeCloseConst C * sobStateConst C ^ 2 + C0 ^ 2 + K1 ^ 2) * L *
        meshSize N ^ min s 1) ^ 2 := by
  have hL0 : 0 ≤ L := h.1.nonneg
  have hc := cubeClose_of_isSobolevStateTr hT hB N hs0 h
  have h1 := cubeFEM_strangData_le_of_close hT hB N hc (L * C0 * meshSize N)
    (K1 * meshSize N * L)
  refine h1.trans ?_
  have hm0 : 0 ≤ meshSize N ^ min s 1 := rpow_min_nonneg s N
  have hh : 0 ≤ meshSize N := (meshSize_pos N).le
  have hhm : meshSize N ≤ meshSize N ^ min s 1 := meshSize_le_rpow_min s N
  have hcc := cubeCloseConst_nonneg C
  have hX : (meshSize N * L) ^ 2 ≤ (meshSize N ^ min s 1 * L) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hh hL0) (mul_le_mul_of_nonneg_right hhm hL0) 2
  have hKd0 : 0 ≤ cubeCloseConst C * sobStateConst C ^ 2 + C0 ^ 2 + K1 ^ 2 := by positivity
  rw [show (√(cubeCloseConst C * sobStateConst C ^ 2 + C0 ^ 2 + K1 ^ 2) * L *
      meshSize N ^ min s 1) ^ 2 = √(cubeCloseConst C * sobStateConst C ^ 2 + C0 ^ 2 + K1 ^ 2) ^ 2 *
      (L ^ 2 * (meshSize N ^ min s 1) ^ 2) by ring, Real.sq_sqrt hKd0]
  have e1 : (L * C0 * meshSize N) ^ 2 = C0 ^ 2 * (meshSize N * L) ^ 2 := by ring
  have e2 : (K1 * meshSize N * L) ^ 2 = K1 ^ 2 * (meshSize N * L) ^ 2 := by ring
  have e3 : cubeCloseConst C * (sobStateConst C * meshSize N ^ min s 1 * L) ^ 2 =
      cubeCloseConst C * sobStateConst C ^ 2 * (meshSize N ^ min s 1 * L) ^ 2 := by ring
  rw [e1, e2, e3]
  have f1 := mul_le_mul_of_nonneg_left hX (sq_nonneg C0)
  have f2 := mul_le_mul_of_nonneg_left hX (sq_nonneg K1)
  have e4 : (cubeCloseConst C * sobStateConst C ^ 2 + C0 ^ 2 + K1 ^ 2) * (L ^ 2 *
      (meshSize N ^ min s 1) ^ 2) = cubeCloseConst C * sobStateConst C ^ 2 *
        (meshSize N ^ min s 1 * L) ^ 2 + C0 ^ 2 * (meshSize N ^ min s 1 * L) ^ 2 +
        K1 ^ 2 * (meshSize N ^ min s 1 * L) ^ 2 := by ring
  rw [e4]
  linarith

set_option maxHeartbeats 8000000 in
/-- **The rate of the semi-discrete scheme (6.5) on the cube for relative-class Sobolev data**
([QuennevilleBelair2015], §6.3, (6.5), Table 6.1, with the thesis' boundary conditions; the
elliptic projection (6.4) as initial datum; new: the thesis states no rate for (6.5);
unconditional: `curlPotential`). There is `K`, independent of `N`, `T`, `s`, the data and the
solution, such that for every `s ≥ 0`, every `L²` source `f` continuous on `[0,T]` and every
classical solution `w` of (6.2) whose states and time derivatives are in the relative class
`Hˢ_univ` with norms `≤ L` (`IsSobolevStateTr`), whose skew fields satisfy
`|⟪M, d v⟫|, |⟪M', d v⟫| ≤ L ‖v‖` (`M, M' ∈ D(d¹*)`), and whose multiplier functionals are
`L²`-bounded, `|ℓ μ|, |ℓ' μ| ≤ L ‖μ‖` (as in the existing rates `cubeWave_rate_tr`), the scheme
(6.5) with source `P_{Ṽₕ¹} f` has a solution from the dynamic part of the elliptic projection of
the exact initial state with, on `[0,T]`,
`(‖σ − σₕ‖² + ‖u − uₕ‖² + ‖M − Mₕ‖² + ‖ρ − ρₕ‖²)^{1/2}(t) ≤ K L (1 + t) h_N^{min(s,1)}`.
Proof: `Feec.BGG.ExactWave.exists_discreteSolution_rate` with `h = h_N^{min(s,1)}`, the Strang data
`cubeFEM_strangData_le_sobolev`, `K₀` from `consistency_S0_of_approx` and `K₁` from
`exists_cubeFEM_K1`.

**The exponent `min(s, 1)` is optimal for these elements**: the top row `P₁Λ̊⁰ → P₁⁻Λ̊¹ → P₁⁻Λ̊²`
reproduces only the constants in degrees `1, 2` (`r_eff = 1`), so `dist(M, P₁⁻Λ̊²)` is of exact
order `h` for smooth `M` with nonzero gradient, and no rate beyond `h¹` holds even for smooth
data; for `s ≤ 1` the rate `hˢ` of the best approximation is sharp ([AFW2010], §5.4 and the table of
`Feec.Models.Cube.SobolevRate`). The lower bounds are standard and not formalized. -/
theorem cubeWave_rate_sobolev :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {T : ℝ} (_hT0 : 0 < T) {f : ℝ → Wv W1}
      (_hf : ContinuousOn f (Icc 0 T)) (w : Feec.BGG.ExactWave bggSegment T (srcFun f))
      {s L : ℝ}, 0 ≤ s → 0 ≤ L →
      (∀ t ∈ Icc 0 T, IsSobolevStateTr s L (w.σ t) (w.φ t) (w.u t) (w.M t) (w.ρ t) ∧
        IsSobolevStateTr s L (w.σ' t) (w.φ' t) (w.u' t) (w.M' t) (w.ρ' t)) →
      (∀ t ∈ Icc 0 T, ∀ v : U1, |⟪w.M t, bggSegment.d1 v⟫| ≤ L * ‖v‖ ∧
        |⟪w.M' t, bggSegment.d1 v⟫| ≤ L * ‖v‖) →
      (∀ t ∈ Icc 0 T, ∀ μ : U1, |w.ℓ t μ| ≤ L * ‖μ‖ ∧ |w.ℓ' t μ| ≤ L * ‖μ‖) →
      ∃ sh : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N f),
        (sh.σ 0, sh.u 0, sh.M 0, sh.ρ 0) =
          (Feec.BGG.ellipticProjection (cubeWave hT hB N) (cubeWave_dt0_injective hT hB N)
            (Feec.BGG.exists_sub_eq_of_surjective (cubeWave_S0_surjective hT hB N))
            (Feec.BGG.ellipticRhs ((cubeFEM hT hB N).ellipticDataH (w.σ 0) (w.φ 0) (w.u 0)
              (w.M 0) (w.ρ 0) (w.ℓ 0)) 0)).1.1 ∧
        ∀ t ∈ Icc 0 T, √(‖w.σ t - sh.σ t‖ ^ 2 + ‖w.u t - sh.u t‖ ^ 2 +
          ‖w.M t - sh.M t‖ ^ 2 + ‖w.ρ t - sh.ρ t‖ ^ 2) ≤
            K * L * (1 + t) * meshSize N ^ min s 1 := by
  have H := bggStability_curlPotentialConst
  have hh0 := cubeFEM_happ0 hT hB
  obtain ⟨C0, hh1⟩ := hh0
  have hC00 := hh1.1
  have hhapp := hh1.2
  have hk0 := exists_cubeFEM_K1 hT hB
  obtain ⟨K1, hk1⟩ := hk0
  have hK10 := hk1.1
  have hK1 := hk1.2
  have ex_Ks : ∃ x : ℝ, x = √(2 * (Feec.BGG.Discrete.strangConst (2 * Real.pi)⁻¹ + 1)) :=
    ⟨_, rfl⟩
  obtain ⟨Ks, hKs⟩ := ex_Ks
  have hKs0 : 0 ≤ Ks := hKs ▸ Real.sqrt_nonneg _
  have ex_Kd : ∃ x : ℝ, x = cubeCloseConst C * sobStateConst C ^ 2 + C0 ^ 2 + K1 ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨Kd, hKd⟩ := ex_Kd
  refine ⟨2 * Ks * √Kd, mul_nonneg (mul_nonneg zero_le_two hKs0) (Real.sqrt_nonneg _),
    fun N T hT0 f hf w s L hs0 hL0 hsob hMd hmult => ?_⟩
  have hh : 0 ≤ meshSize N := (meshSize_pos N).le
  have hm0 : 0 ≤ meshSize N ^ min s 1 := rpow_min_nonneg s N
  have hK0 : ∀ ℓ : U1 →ₗ[ℝ] ℝ, (∀ μ, |ℓ μ| ≤ L * ‖μ‖) → ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
      |ℓ ((bggSegment.S0 - (cubeFEM hT hB N).S0h) ψ)| ≤
        (L * C0 * meshSize N) * √(Feec.BGG.graphSq bggSegment.dt0 ψ) := fun ℓ hℓ =>
    Feec.BGG.Discrete.consistency_S0_of_approx hh hC00 hL0 ℓ hℓ (hhapp N)
  have hK1' : ∀ z : W2, SobRel s L 2 z → (∀ v : U1, |⟪z, bggSegment.d1 v⟫| ≤ L * ‖v‖) →
      ∀ v ∈ (cubeFEM hT hB N).Vt1h, |⟪z, (bggSegment.S1 - (cubeFEM hT hB N).S1h) v⟫| ≤
        (K1 * meshSize N * L) * √((cubeFEM hT hB N).gnSq v) := fun z hz hzd =>
    hK1 N z L hL0 (hz.norm_le hs0) hzd
  have hdata : ∀ {σ : U0} {φ : Wv U0} {u : Wv U1} {M : W2} {ρ : Wv W2},
      IsSobolevStateTr s L σ φ u M ρ →
      (cubeFEM hT hB N).strangData σ φ u M ρ (L * C0 * meshSize N) (K1 * meshSize N * L) ≤
        ((√Kd * L) * meshSize N ^ min s 1) ^ 2 := fun hst => by
    rw [hKd]; exact cubeFEM_strangData_le_sobolev hT hB N hs0 hst C0 K1
  have hrate := w.exists_discreteSolution_rate (cubeFEM hT hB N) H (cubeFEM_compatible hT hB N)
    (K0 := L * C0 * meshSize N) (K1 := K1 * meshSize N * L) (c := √Kd * L)
    (h := meshSize N ^ min s 1) (cubeWave_S0_surjective hT hB N) hT0
    (continuousOn_cubeSource hT hB N hf) (fun t _ v => (inner_cubeSource hT hB N f t v).symm)
    (fun t ht => hK0 (w.ℓ t) fun μ => (hmult t ht μ).1)
    (fun t ht => hK0 (w.ℓ' t) fun μ => (hmult t ht μ).2)
    (fun t ht => hK1' (w.M t) (hsob t ht).1.2.2.2.2.1 fun v => (hMd t ht v).1)
    (fun t ht => hK1' (w.M' t) (hsob t ht).2.2.2.2.2.1 fun v => (hMd t ht v).2)
    (fun t ht => hdata (hsob t ht).1) (fun t ht => hdata (hsob t ht).2)
  obtain ⟨sh, h0, hb⟩ := hrate
  refine ⟨sh, h0, fun t ht => (hb t ht).trans (le_of_eq ?_)⟩
  rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg Kd) hL0), abs_of_nonneg hm0, ← hKs]
  ring

end CubeFEM

/-! ### Gaffney's identity in the relative parity class -/

section Gaffney

open Feec.Models.Cube.DeRhamIdent
open Feec.Models.Cube.Geometry (Q)

variable {n : ℕ}

/-- **Gaffney's identity on the real torus window**: a sequence in the domains of the outgoing
differential and of the adjoint of the incoming one lies in `H¹(𝕋ⁿ)`, with
`Σ_m (1 + |ξ_m|²) |y(m)|² = ‖y‖² + ‖d y‖² + ‖d* y‖²` (the fibre Cartan identity
`|ξ|² |v|² = |ξ ∧ v|² + |ι_ξ v|²`, `Feec.Models.Torus.DeRham.window_cartan`). -/
theorem gaffney_RT (a : Fin (Fintype.card (Fin n) + 1)) {y : TW n a}
    (h1 : y ∈ ((RT n).d a ((ComplexShape.window (Fintype.card (Fin n) + 1)).next a)).domain)
    (h2 : y ∈ (((RT n).d ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a)†).domain) :
    MemSob 1 (y : Seq n a) ∧
      sobSum 1 (y : Seq n a) = ‖y‖ ^ 2 +
        ‖(RT n).d a ((ComplexShape.window (Fintype.card (Fin n) + 1)).next a) ⟨y, h1⟩‖ ^ 2 +
        ‖((RT n).d ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a)† ⟨y, h2⟩‖ ^ 2 := by
  have h2' : y ∈ (((Torus.DeRham.window (Fin n)).d
      ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a)†).domain := by
    have := h2; rw [RT_adjoint] at this; exact this
  have eadj : ((RT n).d ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a)† ⟨y, h2⟩ =
      ((Torus.DeRham.window (Fin n)).d
        ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a)† ⟨y, h2'⟩ :=
    LinearPMap.apply_eq_of_eq (RT_adjoint _ a) ⟨y, h2⟩ ⟨y, h2'⟩ rfl
  have h2'' : y ∈ (Operator.mulOp (Measure.count : Measure (Fin n → ℤ)) fun k =>
      ContinuousLinearMap.adjoint ((Torus.DeRham.windowSymbol (Fin n)).m
        ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a k)).domain := by
    have := h2'; rw [Fourier.SymbolComplex.adjoint_d] at this; exact this
  have eadj2 : ((Torus.DeRham.window (Fin n)).d
      ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a)† ⟨y, h2'⟩ =
      Operator.mulOp (Measure.count : Measure (Fin n → ℤ)) (fun k =>
        ContinuousLinearMap.adjoint ((Torus.DeRham.windowSymbol (Fin n)).m
          ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a k)) ⟨y, h2''⟩ :=
    LinearPMap.apply_eq_of_eq (Fourier.SymbolComplex.adjoint_d _ _ a) _ _ rfl
  have hpt2 : ∀ m, cf (((RT n).d ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a)†
      ⟨y, h2⟩ : Seq n _) m = ContinuousLinearMap.adjoint ((Feec.Fourier.Exterior.deRham (Fin n)).m
        ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a (Fourier.Torus.freq m))
          (cf (y : Seq n a) m) := by
    intro m
    change ((((RT n).d _ a)† ⟨y, h2⟩ : TW n _) : (Fin n → ℤ) → _) m = _
    rw [eadj, eadj2]
    exact Operator.coeFn_mulOp_count _ ⟨y, h2''⟩ m
  have hpt1 : ∀ m, cf ((RT n).d a ((ComplexShape.window (Fintype.card (Fin n) + 1)).next a)
      ⟨y, h1⟩ : Seq n _) m = (Feec.Fourier.Exterior.deRham (Fin n)).m a
        ((ComplexShape.window (Fintype.card (Fin n) + 1)).next a) (Fourier.Torus.freq m)
          (cf (y : Seq n a) m) := fun m => RT_d_apply ⟨y, h1⟩ m
  have hc : ∀ m, weight 1 m * ‖cf (y : Seq n a) m‖ ^ 2 = ‖cf (y : Seq n a) m‖ ^ 2 +
      ‖cf ((RT n).d a ((ComplexShape.window (Fintype.card (Fin n) + 1)).next a)
        ⟨y, h1⟩ : Seq n _) m‖ ^ 2 +
      ‖cf (((RT n).d ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a)†
        ⟨y, h2⟩ : Seq n _) m‖ ^ 2 := by
    intro m
    rw [weight_one, hpt1, hpt2]
    have := Torus.DeRham.window_cartan a (Fourier.Torus.freq m) (cf (y : Seq n a) m)
    linear_combination -this
  have hs : Summable fun m => ‖cf (y : Seq n a) m‖ ^ 2 +
      ‖cf ((RT n).d a ((ComplexShape.window (Fintype.card (Fin n) + 1)).next a)
        ⟨y, h1⟩ : Seq n _) m‖ ^ 2 +
      ‖cf (((RT n).d ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a)†
        ⟨y, h2⟩ : Seq n _) m‖ ^ 2 :=
    ((summable_norm_sq _).add (summable_norm_sq _)).add (summable_norm_sq _)
  refine ⟨?_, ?_⟩
  · exact hs.congr fun m => (hc m).symm
  · unfold sobSum
    rw [tsum_congr hc, ((summable_norm_sq _).add (summable_norm_sq _)).tsum_add
      (summable_norm_sq _), (summable_norm_sq _).tsum_add (summable_norm_sq _),
      ← norm_sq_eq_tsum, ← norm_sq_eq_tsum, ← norm_sq_eq_tsum]

/-- **Gaffney's identity in the relative class `H̊Λ(Q)`** (window form): a form on `Q` in the
domain of the outgoing minimal differential and of the adjoint of the incoming one lies in
`H¹_univ` with `‖x‖²_{1,univ} = ‖x‖² + ‖d x‖² + ‖d* x‖²`. Through the identification of `H̊Λ(Q)`
with the relative parity class of the torus (`HQmin_eq_compress`) this is `gaffney_RT`. -/
theorem gaffney_HQmin (a : Fin (Fintype.card (Fin n) + 1)) {x : WQ n a}
    (h1 : x ∈ ((HQmin n).d a ((ComplexShape.window (Fintype.card (Fin n) + 1)).next a)).domain)
    (h2 : x ∈ (((HQmin n).d ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a)†).domain) :
    x ∈ sobolevPar Finset.univ (a : ℕ) 1 ∧
      parNorm Finset.univ (a : ℕ) 1 x ^ 2 = ‖x‖ ^ 2 +
      ‖(HQmin n).d a ((ComplexShape.window (Fintype.card (Fin n) + 1)).next a) ⟨x, h1⟩‖ ^ 2 +
      ‖((HQmin n).d ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a)† ⟨x, h2⟩‖ ^ 2 := by
  have e := HQmin_eq_compress (n := n)
  have h1' := h1
  have h2' := h2
  rw [e] at h1' h2'
  have hJ1 := (Feec.HilbertComplex.mem_compress_domain_iff two_pow_pos (inner_J true)
    (reducing_range true)).1 h1'
  have hJ2 := (Feec.HilbertComplex.mem_adjoint_compress_iff two_pow_pos (inner_J true)
    (reducing_range true)).1 h2'
  obtain ⟨hm, hsum⟩ := gaffney_RT a hJ1 hJ2
  have ev1 : (HQmin n).d a ((ComplexShape.window (Fintype.card (Fin n) + 1)).next a) ⟨x, h1⟩ =
      ((RT n).compress (J true) two_pow_pos (inner_J true) (reducing_range true)).d a
        ((ComplexShape.window (Fintype.card (Fin n) + 1)).next a) ⟨x, h1'⟩ :=
    LinearPMap.apply_eq_of_eq (congrArg (fun H : Feec.HilbertComplex ℝ
      (ComplexShape.window (Fintype.card (Fin n) + 1)) (WQ n) =>
        H.d a ((ComplexShape.window (Fintype.card (Fin n) + 1)).next a)) e) _ _ rfl
  have ev2 : ((HQmin n).d ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a)† ⟨x, h2⟩ =
      (((RT n).compress (J true) two_pow_pos (inner_J true) (reducing_range true)).d
        ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a)† ⟨x, h2'⟩ :=
    LinearPMap.apply_eq_of_eq (congrArg (fun H : Feec.HilbertComplex ℝ
      (ComplexShape.window (Fintype.card (Fin n) + 1)) (WQ n) =>
        (H.d ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a)†) e) _ _ rfl
  have j1 := Feec.HilbertComplex.J_compress_d two_pow_pos (inner_J true) (reducing_range true)
    (i := a) (j := (ComplexShape.window (Fintype.card (Fin n) + 1)).next a) ⟨x, h1'⟩
  have j2 := Feec.HilbertComplex.J_adjoint_compress_d two_pow_pos (inner_J true)
    (reducing_range true) (i := (ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) (j := a)
    ⟨x, h2'⟩
  have hn : ∀ (b : Fin (Fintype.card (Fin n) + 1)) (z : WQ n b),
      ‖J true b z‖ ^ 2 = 2 ^ n * ‖z‖ ^ 2 := fun b z => by
    rw [Feec.HilbertComplex.norm_apply_of_inner two_pow_pos (inner_J true), mul_pow,
      Real.sq_sqrt (two_pow_pos (n := n)).le]
  have eJ : JfJ (Finset.univ : Finset (Fin n)) (a : ℕ) x = J true a x := by
    rw [JfJ_univ]; rfl
  refine ⟨by rw [mem_sobolevPar, eJ]; exact hm, ?_⟩
  rw [parNorm_sq, eJ, hsum, ev1, ev2]
  have k1 := hn _ ((((RT n).compress (J true) two_pow_pos (inner_J true) (reducing_range true)).d a
    ((ComplexShape.window (Fintype.card (Fin n) + 1)).next a)) ⟨x, h1'⟩)
  have k2 := hn _ ((((RT n).compress (J true) two_pow_pos (inner_J true) (reducing_range true)).d
    ((ComplexShape.window (Fintype.card (Fin n) + 1)).prev a) a)† ⟨x, h2'⟩)
  rw [j1] at k1
  rw [j2] at k2
  rw [hn a x, k1, k2]
  field_simp

theorem gaffney_HQmin' (a b c : Fin (Fintype.card (Fin n) + 1))
    (hb : (ComplexShape.window (Fintype.card (Fin n) + 1)).next a = b)
    (hc : (ComplexShape.window (Fintype.card (Fin n) + 1)).prev a = c) {x : WQ n a}
    (h1 : x ∈ ((HQmin n).d a b).domain) (h2 : x ∈ (((HQmin n).d c a)†).domain) :
    x ∈ sobolevPar Finset.univ (a : ℕ) 1 ∧
      parNorm Finset.univ (a : ℕ) 1 x ^ 2 = ‖x‖ ^ 2 + ‖(HQmin n).d a b ⟨x, h1⟩‖ ^ 2 +
        ‖((HQmin n).d c a)† ⟨x, h2⟩‖ ^ 2 := by
  subst hb hc
  exact gaffney_HQmin a h1 h2

theorem adjoint_apply_eq_zero_of_eq_zero {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E]
    {A : E →ₗ.[ℝ] F} (hA : A = 0) (y : (A†).domain) : A† y = 0 := by
  subst hA; exact adjoint_zero_apply y

/-- The window indices of `Λ⁰ → Λ¹ → Λ² → Λ³` on the cube. -/
abbrev W4 : Type := Fin (Fintype.card (Fin 3) + 1)

/-- The window index `k ≤ 3`. -/
abbrev wi (k : ℕ) (hk : k < 4) : W4 := ⟨k, by simpa using hk⟩

theorem window_next_wi (k : ℕ) (hk : k + 1 < 4) :
    (ComplexShape.window (Fintype.card (Fin 3) + 1)).next (wi k (by omega)) = wi (k + 1) hk :=
  ComplexShape.next_eq' _ (by change k + 1 = k + 1; rfl)

theorem window_prev_wi (k : ℕ) (hk : k + 1 < 4) :
    (ComplexShape.window (Fintype.card (Fin 3) + 1)).prev (wi (k + 1) hk) = wi k (by omega) :=
  ComplexShape.prev_eq' _ (by change k + 1 = k + 1; rfl)

theorem window_prev_wi_zero :
    (ComplexShape.window (Fintype.card (Fin 3) + 1)).prev (wi 0 (by norm_num)) =
      wi 0 (by norm_num) :=
  ComplexShape.prev_eq_self' _ _ fun k hk => by
    change (k : ℕ) + 1 = 0 at hk
    omega

theorem HQmin_d_wi (k : ℕ) (hk : k + 1 < 4) :
    (HQmin 3).d (wi k (by omega)) (wi (k + 1) hk) = (extDerivOp ℝ 3 k).minimal (Q (Fin 3)) :=
  HQmin_d_succ (n := 3) (wi k (by omega)) (by simpa using hk)

theorem HQmin_d_wi_zero_zero : (HQmin 3).d (wi 0 (by norm_num)) (wi 0 (by norm_num)) = 0 :=
  (HQmin 3).shape _ _ (by change ¬ 0 + 1 = 0; omega)

/-- **Gaffney on `Q` in degrees `k + 1 ≤ 2`**: `x ∈ D(d_min) ∩ D(d_min*)` (the outgoing minimal
differential and the adjoint of the incoming one; `H̊(curl) ∩ H(div)` in degree `1`) gives
`x ∈ H¹_univ` with `‖x‖²_{1,univ} = ‖x‖² + ‖dx‖² + ‖d*x‖²`. -/
theorem gaffney_Q (k : ℕ) (hk : k + 2 < 4) {x : L2F ℝ (Q (Fin 3)) (formIdx 3 ((k + 1 : ℕ) : ℤ))}
    (h1 : x ∈ ((HQmin 3).d (wi (k + 1) (by omega)) (wi (k + 2) hk)).domain)
    (h2 : x ∈ (((HQmin 3).d (wi k (by omega)) (wi (k + 1) (by omega)))†).domain) :
    x ∈ sobolevPar Finset.univ (k + 1) 1 ∧
      parNorm Finset.univ (k + 1) 1 x ^ 2 = ‖x‖ ^ 2 +
        ‖(HQmin 3).d (wi (k + 1) (by omega)) (wi (k + 2) hk) ⟨x, h1⟩‖ ^ 2 +
        ‖((HQmin 3).d (wi k (by omega)) (wi (k + 1) (by omega)))† ⟨x, h2⟩‖ ^ 2 :=
  gaffney_HQmin' (n := 3) (wi (k + 1) (by omega)) (wi (k + 2) hk) (wi k (by omega))
    (window_next_wi (k + 1) hk) (window_prev_wi k (by omega)) h1 h2

/-- **Gaffney on `Q` in degree `0`**: `H̊Λ⁰(Q) ⊆ H¹_univ`, `‖x‖²_{1,univ} = ‖x‖² + ‖dx‖²`. -/
theorem gaffney_Q_zero {x : L2F ℝ (Q (Fin 3)) (formIdx 3 ((0 : ℕ) : ℤ))}
    (h1 : x ∈ ((HQmin 3).d (wi 0 (by norm_num)) (wi 1 (by norm_num))).domain) :
    x ∈ sobolevPar Finset.univ 0 1 ∧
      parNorm Finset.univ 0 1 x ^ 2 = ‖x‖ ^ 2 +
        ‖(HQmin 3).d (wi 0 (by norm_num)) (wi 1 (by norm_num)) ⟨x, h1⟩‖ ^ 2 := by
  have h2 : x ∈ (((HQmin 3).d (wi 0 (by norm_num)) (wi 0 (by norm_num)))†).domain := by
    rw [HQmin_d_wi_zero_zero]; exact mem_adjoint_zero_domain x
  obtain ⟨hm, hn⟩ := gaffney_HQmin' (n := 3) (wi 0 (by norm_num)) (wi 1 (by norm_num))
    (wi 0 (by norm_num)) (window_next_wi 0 (by norm_num)) window_prev_wi_zero h1 h2
  refine ⟨hm, hn.trans ?_⟩
  have h0 : ((HQmin 3).d (wi 0 (by norm_num)) (wi 0 (by norm_num)))† ⟨x, h2⟩ = 0 :=
    adjoint_apply_eq_zero_of_eq_zero HQmin_d_wi_zero_zero ⟨x, h2⟩
  rw [h0, norm_zero]
  ring

theorem mem_domain_of_eq_op {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] {A B : E →ₗ.[ℝ] F} (h : A = B) {x : E} (hx : x ∈ B.domain) : x ∈ A.domain := by
  subst h; exact hx

theorem mem_adjoint_domain_of_eq_op {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] {A B : E →ₗ.[ℝ] F}
    (h : A = B) {y : F} (hy : y ∈ (B†).domain) : y ∈ (A†).domain := by
  subst h; exact hy

theorem norm_apply_of_eq_op {E F : Type*} [AddCommGroup E] [Module ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {A B : E →ₗ.[ℝ] F} (h : A = B) {x : E} (hx : x ∈ B.domain) :
    ‖A ⟨x, mem_domain_of_eq_op h hx⟩‖ = ‖B ⟨x, hx⟩‖ := by
  subst h; rfl

theorem norm_adjoint_apply_of_eq_op {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] {A B : E →ₗ.[ℝ] F}
    (h : A = B) {y : F} (hy : y ∈ (B†).domain) :
    ‖A† ⟨y, mem_adjoint_domain_of_eq_op h hy⟩‖ = ‖B† ⟨y, hy⟩‖ := by
  subst h; rfl

/-- **Gaffney's identity on a copy of `Q`, degrees `k + 1 ≤ 2`**, for the minimal differentials
(`h : Ω = Q` transports along `castL2F`). -/
theorem gaffney_of_eq (k : ℕ) (hk : k + 2 < 4) {Ω : Set (Fin 3 → ℝ)} (h : Ω = Q (Fin 3))
    {x : L2F ℝ Ω (formIdx 3 ((k + 1 : ℕ) : ℤ))}
    (h1 : x ∈ ((extDerivOp ℝ 3 ((k + 1 : ℕ) : ℤ)).minimal Ω).domain)
    (h2 : x ∈ (((extDerivOp ℝ 3 (k : ℤ)).minimal Ω)†).domain) :
    castL2F h _ x ∈ sobolevPar Finset.univ (k + 1) 1 ∧
      parNorm Finset.univ (k + 1) 1 (castL2F h _ x) ^ 2 = ‖x‖ ^ 2 +
        ‖(extDerivOp ℝ 3 ((k + 1 : ℕ) : ℤ)).minimal Ω ⟨x, h1⟩‖ ^ 2 +
        ‖((extDerivOp ℝ 3 (k : ℤ)).minimal Ω)† ⟨x, h2⟩‖ ^ 2 := by
  subst h
  have e1 := HQmin_d_wi (k + 1) hk
  have e2 := HQmin_d_wi k (by omega)
  obtain ⟨hm, hn⟩ := gaffney_Q k hk (x := x) (mem_domain_of_eq_op e1 h1)
    (mem_adjoint_domain_of_eq_op e2 h2)
  refine ⟨hm, hn.trans ?_⟩
  rw [norm_apply_of_eq_op e1 h1, norm_adjoint_apply_of_eq_op e2 h2]

/-- **Gaffney's identity on a copy of `Q`, degree `0`**. -/
theorem gaffney_of_eq_zero {Ω : Set (Fin 3 → ℝ)} (h : Ω = Q (Fin 3))
    {x : L2F ℝ Ω (formIdx 3 ((0 : ℕ) : ℤ))}
    (h1 : x ∈ ((extDerivOp ℝ 3 ((0 : ℕ) : ℤ)).minimal Ω).domain) :
    castL2F h _ x ∈ sobolevPar Finset.univ 0 1 ∧
      parNorm Finset.univ 0 1 (castL2F h _ x) ^ 2 = ‖x‖ ^ 2 +
        ‖(extDerivOp ℝ 3 ((0 : ℕ) : ℤ)).minimal Ω ⟨x, h1⟩‖ ^ 2 := by
  subst h
  have e1 := HQmin_d_wi 0 (by norm_num)
  obtain ⟨hm, hn⟩ := gaffney_Q_zero (x := x) (mem_domain_of_eq_op e1 h1)
  refine ⟨hm, hn.trans ?_⟩
  rw [norm_apply_of_eq_op e1 h1]

/-- The minimal `d` on `2`-forms of the cube (`H̊(div)`, `H̊Λ²(Q)`). -/
abbrev D2min : W2 →ₗ.[ℝ] L2F ℝ (cubeDomain 3) (formIdx 3 3) :=
  (extDerivOp ℝ 3 2).minimal (cubeDomain 3)

theorem sobRel_of_sq_eq {s : ℝ} {k : ℕ} {x : L2F ℝ (cubeDomain 3) (formIdx 3 k)} {A : ℝ}
    (hm : toQ k x ∈ sobolevPar Finset.univ k s)
    (hn : parNorm Finset.univ k s (toQ k x) ^ 2 = A) : SobRel s (√A) k x :=
  ⟨hm, Real.le_sqrt_of_sq_le (le_of_eq hn)⟩

/-- **Gaffney on the cube, degree `0`**: `σ ∈ H̊Λ⁰(Q)` is in `H¹_univ` with
`‖σ‖²_{1,univ} = ‖σ‖² + ‖dσ‖²`. -/
theorem sobRel_zero_of_mem {x : W0} (h1 : x ∈ D0.domain) :
    SobRel 1 (√(‖x‖ ^ 2 + ‖D0 ⟨x, h1⟩‖ ^ 2)) 0 x :=
  sobRel_of_sq_eq (gaffney_of_eq_zero (cubeDomain_eq_Q 3) (x := x) h1).1
    (gaffney_of_eq_zero (cubeDomain_eq_Q 3) (x := x) h1).2

/-- **Gaffney on the cube, degree `1`** ([AFW2010], §4.3, Gaffney's inequality; here the identity
of the relative parity class): `x ∈ H̊(curl) ∩ H(div)` (`D(d¹) ∩ D(d⁰*)`) is in `H¹_univ` with
`‖x‖²_{1,univ} = ‖x‖² + ‖dx‖² + ‖d⁰*x‖²`. -/
theorem sobRel_one_of_mem {x : W1} (h1 : x ∈ D1.domain) (h2 : x ∈ (D0†).domain) :
    SobRel 1 (√(‖x‖ ^ 2 + ‖D1 ⟨x, h1⟩‖ ^ 2 + ‖D0† ⟨x, h2⟩‖ ^ 2)) 1 x :=
  sobRel_of_sq_eq (gaffney_of_eq 0 (by norm_num) (cubeDomain_eq_Q 3) (x := x) h1 h2).1
    (gaffney_of_eq 0 (by norm_num) (cubeDomain_eq_Q 3) (x := x) h1 h2).2

/-- **Gaffney on the cube, degree `2`**: `x ∈ D(d²) ∩ D(d¹*)` is in `H¹_univ` with
`‖x‖²_{1,univ} = ‖x‖² + ‖dx‖² + ‖d¹*x‖²`. -/
theorem sobRel_two_of_mem {x : W2} (h1 : x ∈ D2min.domain) (h2 : x ∈ (D1†).domain) :
    SobRel 1 (√(‖x‖ ^ 2 + ‖D2min ⟨x, h1⟩‖ ^ 2 + ‖D1† ⟨x, h2⟩‖ ^ 2)) 2 x :=
  sobRel_of_sq_eq (gaffney_of_eq 1 (by norm_num) (cubeDomain_eq_Q 3) (x := x) h1 h2).1
    (gaffney_of_eq 1 (by norm_num) (cubeDomain_eq_Q 3) (x := x) h1 h2).2

end Gaffney

/-! ### A relative-class witness below `H^{1/2}`: the sawtooth `2`-form -/

section Saw

open Feec.Models.Cube.DeRhamIdent
open Feec.Models.Cube.Geometry (Q)
open Feec.Fourier.Exterior (Form)

/-- The index `{1, 2}` of the `2`-form `dx₁ ∧ dx₂`. -/
def t12 : {s : Finset (Fin 3) // s.card = 2} := ⟨{1, 2}, by decide⟩

open scoped Classical in
/-- **The coefficients of the sawtooth `2`-form** `f(y₀) dx₁ ∧ dx₂`, `f(y₀) = Σ_{c ≠ 0}
(i/c) e^{2πi c y₀} = −2 Σ_{c > 0} sin(2πc y₀)/c` (the sawtooth `π(2y₀ − 1)` on `(0, 1)`; not
formalized): `i/c` at the frequencies `c e₀`, `c ≠ 0`, in the component `{1, 2}`. -/
def sawCoeff (m : Fin 3 → ℤ) : Form ℂ (Fin 3) 2 :=
  if OnAxis m ∧ m 0 ≠ 0 then EuclideanSpace.single t12 (Complex.I * (((m 0 : ℝ)⁻¹ : ℝ) : ℂ))
  else 0

open scoped Classical in
theorem norm_sawCoeff (m : Fin 3 → ℤ) : ‖sawCoeff m‖ = ‖logCoeff (n := 3) m‖ := by
  have hl : ‖logCoeff (n := 3) m‖ ^ 2 = ‖sawCoeff m‖ ^ 2 := by
    rw [norm_logCoeff_sq, sawCoeff]
    split_ifs with h
    · rw [PiLp.norm_single, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_inv]
    · simp
  exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hl).symm

theorem summable_norm_sawCoeff_sq : Summable fun m => ‖sawCoeff m‖ ^ 2 := by
  simp only [norm_sawCoeff]; exact summable_norm_logCoeff_sq

/-- The coefficient sequence of the sawtooth form. -/
def sawSeq : Seq 3 2 := (memLp_of_summable summable_norm_sawCoeff_sq).toLp sawCoeff

theorem cf_sawSeq (m : Fin 3 → ℤ) : cf sawSeq m = sawCoeff m := by
  change ((memLp_of_summable summable_norm_sawCoeff_sq).toLp sawCoeff :
    (Fin 3 → ℤ) → Form ℂ (Fin 3) 2) m = _
  rw [MemLp.coeFn_toLp_count]

theorem memSob_sawSeq_iff (s : ℝ) : MemSob s sawSeq ↔ Summable (axisTerm (n := 3) s) := by
  rw [← summable_weight_logCoeff_iff]
  simp only [MemSob, cf_sawSeq, norm_sawCoeff]

theorem onAxis_neg_iff (m : Fin 3 → ℤ) : OnAxis (-m) ↔ OnAxis m := by
  simp only [OnAxis, Pi.neg_apply, neg_eq_zero]

theorem onAxis_flipAt_iff (j : Fin 3) (m : Fin 3 → ℤ) :
    OnAxis (Feec.Models.Cube.DeRham.flipAt j m) ↔ OnAxis m := by
  simp only [OnAxis, Feec.Models.Cube.DeRham.flipAt]
  refine forall_congr' fun a => imp_congr_right fun _ => ?_
  split_ifs <;> simp

open scoped Classical in
/-- **The sawtooth coefficients are real and in the relative class** (odd in `y₀`, even in `y₁, y₂`
for the component `{1, 2}`: `RealParJ univ 2`). -/
theorem realParJ_sawSeq : RealParJ (Finset.univ : Finset (Fin 3)) 2 sawSeq := by
  refine ⟨fun m t => ?_, fun j m t => ?_⟩
  · change cf sawSeq (-m) t = (starRingEnd ℂ) (cf sawSeq m t)
    rw [cf_sawSeq, cf_sawSeq, sawCoeff, sawCoeff]
    simp only [onAxis_neg_iff, Pi.neg_apply, ne_eq, neg_eq_zero]
    split_ifs with h
    · rw [PiLp.single_apply, PiLp.single_apply]
      split_ifs
      · rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
        push_cast
        rw [inv_neg]; ring
      · simp
    · simp
  · change cf sawSeq (Feec.Models.Cube.DeRham.flipAt j m) t =
      Feec.Models.Cube.DeRham.mixedSign Finset.univ j * Feec.Models.Cube.DeRham.reflSign j t.1 *
        cf sawSeq m t
    rw [cf_sawSeq, cf_sawSeq, sawCoeff, sawCoeff]
    simp only [onAxis_flipAt_iff]
    by_cases hm : OnAxis m ∧ m 0 ≠ 0
    · have hf : Feec.Models.Cube.DeRham.flipAt j m 0 = if j = 0 then -m 0 else m 0 := by
        simp only [Feec.Models.Cube.DeRham.flipAt]
        by_cases hj : j = 0
        · subst hj; simp
        · simp [Ne.symm hj, hj]
      have hc : OnAxis m ∧ Feec.Models.Cube.DeRham.flipAt j m 0 ≠ 0 := ⟨hm.1, by
        rw [hf]; split_ifs <;> simp [hm.2]⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_left_of_eq_true _ _ (eq_true hm),
        PiLp.single_apply, PiLp.single_apply, hf]
      by_cases ht : t = t12
      · subst ht
        simp only [↓reduceIte, Feec.Models.Cube.DeRham.mixedSign, Finset.mem_univ,
          Feec.Models.Cube.DeRham.reflSign, t12]
        fin_cases j <;> simp
      · simp [ht]
    · have hc : ¬ (OnAxis m ∧ Feec.Models.Cube.DeRham.flipAt j m 0 ≠ 0) := by
        rintro ⟨h1, h2⟩
        refine hm ⟨h1, fun h0 => h2 ?_⟩
        simp only [Feec.Models.Cube.DeRham.flipAt]
        split_ifs with hj
        · subst hj; simp [h0]
        · exact h0
      rw [ite_eq_right_of_eq_false _ _ (eq_false hc), ite_eq_right_of_eq_false _ _ (eq_false hm)]
      simp

/-- **The sawtooth witness** `f(y₀) dx₁ ∧ dx₂ ∈ L²Λ²(Q)` (an `L²` Fourier series). -/
def sawWitness : L2F ℝ (Q (Fin 3)) (formIdx 3 ((2 : ℕ) : ℤ)) := Jinvf 2 sawSeq

theorem JfJ_sawWitness : JfJ (Finset.univ : Finset (Fin 3)) 2 sawWitness = sawSeq :=
  JfJ_Jinvf realParJ_sawSeq

theorem sawWitness_mem_sobolevPar {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 1 / 2) :
    sawWitness ∈ sobolevPar Finset.univ 2 s := by
  rw [mem_sobolevPar, JfJ_sawWitness, memSob_sawSeq_iff]
  exact summable_axisTerm hs0 hs

/-- **The sawtooth witness is not in `H^{1/2}_univ`**: its tangential trace on `{y₀ = 0}` does
not vanish (the odd extension in `y₀` jumps). -/
theorem sawWitness_not_mem_sobolevPar_half : sawWitness ∉ sobolevPar Finset.univ 2 (1 / 2) := by
  rw [mem_sobolevPar, JfJ_sawWitness, memSob_sawSeq_iff]
  exact not_summable_axisTerm_half

theorem sawWitness_ne_zero : sawWitness ≠ 0 := by
  intro h
  have h1 := sawWitness_not_mem_sobolevPar_half
  rw [h] at h1
  exact h1 (Submodule.zero_mem _)

open Feec.Fourier.Exterior in
/-- **`ι_ξ` kills the sawtooth coefficients**: at `ξ = 2πc e₀` the contraction of `dx₁ ∧ dx₂`
vanishes (`ξ` has no component along `e₁, e₂`). -/
theorem contr_ext_sawCoeff (m : Fin 3 → ℤ) :
    contr (Fourier.Torus.freq m) (ext 2 (sawCoeff m)) = 0 := by
  classical
  ext s
  rw [contr_apply]
  change ∑ j ∈ sᶜ, _ = (0 : ℂ)
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hm : OnAxis m ∧ m 0 ≠ 0
  · by_cases hj : j = 0
    · subst hj
      have h0 : ext 2 (sawCoeff m) (insert 0 s) = 0 := by
        rw [sawCoeff, ite_eq_left_of_eq_true _ _ (eq_true hm)]
        by_cases hc : (insert 0 s).card = 2
        · rw [ext_apply 2 _ hc, PiLp.single_apply, ite_eq_right_of_eq_false _ _ (eq_false ?_)]
          intro h
          have h' : insert 0 s = ({1, 2} : Finset (Fin 3)) := congrArg Subtype.val h
          have h0 : (0 : Fin 3) ∈ insert 0 s := Finset.mem_insert_self 0 s
          rw [h'] at h0
          simp at h0
        · rw [ext_apply_of_ne 2 _ hc]
      rw [h0, mul_zero]
    · have hξ : (Fourier.Torus.freq m) j = 0 := by
        rw [Fourier.Torus.freq_apply, hm.1 j hj]; simp
      rw [hξ]; simp
  · rw [sawCoeff, ite_eq_right_of_eq_false _ _ (eq_false hm), map_zero]
    simp

open Feec.Fourier.Exterior in
/-- At the axis frequencies the de Rham symbol has norm `|ξ| |v| = 2π` on the sawtooth
coefficients. -/
theorem norm_deRham_sawCoeff_axis (c : ℤ) (hc : c ≠ 0) :
    ‖(deRham (Fin 3)).m 2 (2 + 1) (Fourier.Torus.freq (axis (n := 3) c))
      (sawCoeff (axis (n := 3) c))‖ ^ 2 = (2 * Real.pi) ^ 2 := by
  rw [norm_deRham_apply]
  have h := norm_koszulDeg_sq_add (𝕜 := ℂ) 2 (Fourier.Torus.freq (axis (n := 3) c))
    (sawCoeff (axis (n := 3) c))
  rw [contr_ext_sawCoeff, norm_zero] at h
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero] at h
  rw [h, norm_freq_axis_sq, norm_sawCoeff, norm_logCoeff_sq]
  have hax : OnAxis (axis (n := 3) c) := (onAxis_iff_mem_range _).2 ⟨c, rfl⟩
  have h0 : axis (n := 3) c 0 = c := by simp [axis]
  rw [h0]
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  simp only [hax, ne_eq, hc, not_false_eq_true, and_self, ↓reduceIte]
  rw [inv_pow, sq_abs]
  field_simp

open Feec.Fourier.Exterior in
/-- `ι_ξ` kills the sawtooth sequence at every frequency: the adjoint of the de Rham symbol
`Λ¹ → Λ²` vanishes on it. -/
theorem adjoint_symbol_sawSeq (k : Fin 3 → ℤ) :
    ContinuousLinearMap.adjoint
      ((Torus.DeRham.windowSymbol (Fin 3)).m (wi 1 (by norm_num)) (wi 2 (by norm_num)) k)
        ((sawSeq : TW 3 (wi 2 (by norm_num))) k) = 0 := by
  change ContinuousLinearMap.adjoint ((deRham (Fin 3)).m 1 (1 + 1) (Fourier.Torus.freq k))
    (cf sawSeq k) = 0
  rw [adjoint_deRham, cf_sawSeq, smul_apply]
  change -Complex.I • res 1 (contr (Fourier.Torus.freq k) (ext 2 (sawCoeff k))) = 0
  rw [contr_ext_sawCoeff, map_zero, smul_zero]

/-- **The sawtooth sequence is in the kernel of the adjoint of the torus `d¹`.** -/
theorem sawSeq_mem_ker_adjoint :
    (sawSeq : TW 3 (wi 2 (by norm_num))) ∈
      (((RT 3).d (wi 1 (by norm_num)) (wi 2 (by norm_num)))†).ker := by
  have hk : (sawSeq : TW 3 (wi 2 (by norm_num))) ∈
      (((Torus.DeRham.window (Fin 3)).d (wi 1 (by norm_num)) (wi 2 (by norm_num)))†).ker := by
    rw [Fourier.SymbolComplex.ker_adjoint_d, Operator.mem_fibreSub]
    exact Filter.Eventually.of_forall fun k => LinearMap.mem_ker.2 (adjoint_symbol_sawSeq k)
  rw [RT_adjoint]
  obtain ⟨y, hy, h0⟩ := LinearPMap.mem_ker_iff.1 hk
  exact LinearPMap.mem_ker_iff.2 ⟨⟨y.1, y.2⟩, hy, h0⟩

/-- **The sawtooth form is co-closed**: `sawWitness ∈ N((d¹_min)*)` on `Q`, i.e.
`⟪f(y₀) dx₁ ∧ dx₂, d w⟫ = 0` for every `w ∈ H̊Λ¹(Q)` (`ι_ξ` kills its coefficients). -/
theorem sawWitness_mem_ker_adjoint :
    (sawWitness : WQ 3 (wi 2 (by norm_num))) ∈
      (((HQmin 3).d (wi 1 (by norm_num)) (wi 2 (by norm_num)))†).ker := by
  rw [HQmin_eq_compress, Feec.HilbertComplex.mem_ker_adjoint_compress_iff two_pow_pos
    (inner_J true) (reducing_range true)]
  have eJ : J true (wi 2 (by norm_num)) sawWitness = sawSeq := by
    rw [J_apply]
    change Jf true 2 sawWitness = sawSeq
    rw [← JfJ_univ, JfJ_sawWitness]
  rw [eJ]
  exact sawSeq_mem_ker_adjoint

/-- **The sawtooth form is not in `H̊Λ²(Q)`**: `sawWitness ∉ D(d²_min)` (at the axis frequencies
`|ξ ∧ x̂(m)| = 2π`, not square summable). -/
theorem sawWitness_not_mem_domain :
    (sawWitness : WQ 3 (wi 2 (by norm_num))) ∉
      ((HQmin 3).d (wi 2 (by norm_num)) (wi 3 (by norm_num))).domain := by
  intro hx
  obtain ⟨h, -⟩ := mapsTo_comm_min (wi 2 (by norm_num)) (wi 3 (by norm_num)) ⟨_, hx⟩
  have eJ : J true (wi 2 (by norm_num)) sawWitness = sawSeq := by
    rw [J_apply]
    change Jf true 2 sawWitness = sawSeq
    rw [← JfJ_univ, JfJ_sawWitness]
  have hs := summable_norm_sq ((RT 3).d (wi 2 (by norm_num)) (wi 3 (by norm_num)) ⟨_, h⟩ :
    Seq 3 3)
  have hpt : ∀ m, cf ((RT 3).d (wi 2 (by norm_num)) (wi 3 (by norm_num)) ⟨_, h⟩ : Seq 3 3) m =
      (Feec.Fourier.Exterior.deRham (Fin 3)).m 2 (2 + 1) (Fourier.Torus.freq m) (sawCoeff m) := by
    intro m
    rw [← cf_sawSeq, ← eJ]
    exact RT_d_apply ⟨_, h⟩ m
  have hc := (hs.comp_injective (axis_injective (n := 3))).tendsto_cofinite_zero
  have hev : (fun c : ℤ => ‖cf ((RT 3).d (wi 2 (by norm_num)) (wi 3 (by norm_num)) ⟨_, h⟩ :
      Seq 3 3) (axis c)‖ ^ 2) =ᶠ[Filter.cofinite] fun _ => (2 * Real.pi) ^ 2 := by
    refine (Set.finite_singleton (0 : ℤ)).eventually_cofinite_notMem.mono fun c hc => ?_
    change ‖cf _ (axis c)‖ ^ 2 = _
    rw [hpt]
    exact norm_deRham_sawCoeff_axis c hc
  have hlim := (hc.congr' hev)
  have := tendsto_nhds_unique hlim tendsto_const_nhds
  have hpi := Real.pi_pos
  nlinarith

theorem mem_HQmin_of_eq (k : ℕ) (hk : k + 1 < 4) {Ω : Set (Fin 3 → ℝ)} (h : Ω = Q (Fin 3))
    {x : L2F ℝ Ω (formIdx 3 k)} (hx : x ∈ ((extDerivOp ℝ 3 k).minimal Ω).domain) :
    castL2F h _ x ∈ ((HQmin 3).d (wi k (by omega)) (wi (k + 1) hk)).domain := by
  subst h; exact mem_domain_of_eq_op (HQmin_d_wi k hk) hx

theorem inner_minimal_one_eq_zero_of_eq {Ω : Set (Fin 3 → ℝ)} (h : Ω = Q (Fin 3))
    (y : L2F ℝ Ω (formIdx 3 ((1 : ℕ) + 1 : ℕ)))
    (w : ((extDerivOp ℝ 3 ((1 : ℕ) : ℤ)).minimal Ω).domain)
    (hy : castL2F h _ y ∈ (((HQmin 3).d (wi 1 (by norm_num)) (wi 2 (by norm_num)))†).ker) :
    ⟪y, (extDerivOp ℝ 3 ((1 : ℕ) : ℤ)).minimal Ω w⟫ = 0 := by
  subst h
  obtain ⟨z, hz, h0⟩ := LinearPMap.mem_ker_iff.1 hy
  have hw : (w : L2F ℝ (Q (Fin 3)) (formIdx 3 ((1 : ℕ) : ℤ))) ∈
      ((HQmin 3).d (wi 1 (by norm_num)) (wi 2 (by norm_num))).domain :=
    mem_domain_of_eq_op (HQmin_d_wi 1 (by norm_num)) w.2
  have hadj := LinearPMap.adjoint_isFormalAdjoint ((HQmin 3).dense _ _) z ⟨_, hw⟩
  rw [h0, inner_zero_left] at hadj
  have e : (HQmin 3).d (wi 1 (by norm_num)) (wi 2 (by norm_num)) ⟨_, hw⟩ =
      (extDerivOp ℝ 3 ((1 : ℕ) : ℤ)).minimal (Q (Fin 3)) w :=
    LinearPMap.apply_eq_of_eq (HQmin_d_wi 1 (by norm_num)) ⟨_, hw⟩ w rfl
  have hz' : (z : WQ 3 (wi 2 (by norm_num))) = y := hz.symm
  rw [e, hz'] at hadj
  exact hadj.symm

/-- **The sawtooth `2`-form on the cube**, `f(y₀) dx₁ ∧ dx₂ ∈ L²Λ²(Q)`. -/
def sawW2 : W2 := (toQ ((2 : ℕ) : ℤ)).symm sawWitness

theorem toQ_sawW2 : toQ ((2 : ℕ) : ℤ) sawW2 = sawWitness := LinearIsometryEquiv.apply_symm_apply _ _

/-- **The sawtooth form is co-closed with no boundary condition**: `⟪f(y₀) dx₁ ∧ dx₂, d w⟫ = 0`
for every `w ∈ H̊Λ¹(Q)`, i.e. `sawW2 ∈ N((d¹)*)`. -/
theorem inner_sawW2_D1 (w : U1) : ⟪sawW2, D1 w⟫ = 0 :=
  inner_minimal_one_eq_zero_of_eq (cubeDomain_eq_Q 3) sawW2 w
    (by change toQ ((2 : ℕ) : ℤ) sawW2 ∈ _; rw [toQ_sawW2]; exact sawWitness_mem_ker_adjoint)

/-- **The sawtooth form is not in `H̊Λ²(Q)`** (its tangential trace on `{y₀ = 0}` does not
vanish). -/
theorem sawW2_not_mem_D2min : sawW2 ∉ D2min.domain := fun hx => by
  have h := mem_HQmin_of_eq 2 (by norm_num) (cubeDomain_eq_Q 3) hx
  change toQ ((2 : ℕ) : ℤ) sawW2 ∈ _ at h
  rw [toQ_sawW2] at h
  exact sawWitness_not_mem_domain h

theorem sobRel_sawW2 {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 1 / 2) :
    SobRel s (parNorm Finset.univ 2 s sawWitness) 2 sawW2 := by
  refine ⟨?_, ?_⟩ <;> rw [toQ_sawW2]
  · exact sawWitness_mem_sobolevPar hs0 hs

theorem not_sobRel_sawW2_half (L : ℝ) : ¬ SobRel (1 / 2) L 2 sawW2 := fun h => by
  have h1 := h.1
  rw [toQ_sawW2] at h1
  exact sawWitness_not_mem_sobolevPar_half h1

end Saw

/-! ### Non-vacuity: a stationary solution of (6.2) below `H^{1/2}` -/

section SawWave

/-- The magnetic field `ρ = (f(y₀) dx₁ ∧ dx₂, 0, 0)` of the sawtooth solution. -/
def sawRho : Wv W2 := WithLp.toLp 2 (Pi.single 0 sawW2)

theorem sawRho_apply_zero : sawRho 0 = sawW2 := by
  change (Pi.single (0 : Fin 3) sawW2 : Fin 3 → W2) 0 = _
  exact Pi.single_eq_same _ _

theorem sawRho_apply_of_ne {a : Fin 3} (ha : a ≠ 0) : sawRho a = 0 := by
  change (Pi.single (0 : Fin 3) sawW2 : Fin 3 → W2) a = 0
  exact Pi.single_eq_of_ne ha _

theorem inner_sawRho_dt1 (v : Wv U1) : ⟪sawRho, bggSegment.dt1 v⟫ = 0 := by
  rw [inner_Vt, Fin.sum_univ_three, sawRho_apply_zero,
    sawRho_apply_of_ne (by decide : (1 : Fin 3) ≠ 0),
    sawRho_apply_of_ne (by decide : (2 : Fin 3) ≠ 0), inner_zero_left, inner_zero_left, add_zero,
    add_zero]
  exact inner_sawW2_D1 (v 0)

/-- **A stationary classical solution of (6.2) whose magnetic field is the sawtooth form**:
`σ = φ = u = M = 0`, `ρ = (f(y₀) dx₁ ∧ dx₂, 0, 0)`, `ℓ = 0`, source `0`; (6.2b) holds because
`ρ` is co-closed (`inner_sawW2_D1`). `ρ` has a nonzero tangential trace on `{y₀ = 0}` (it is in
`Hˢ_univ` exactly for `s < ½`). -/
def sawWave (T : ℝ) : Feec.BGG.ExactWave bggSegment T (srcFun 0) where
  σ _ := 0
  φ _ := 0
  u _ := 0
  M _ := 0
  ρ _ := sawRho
  ℓ _ := 0
  σ' _ := 0
  φ' _ := 0
  u' _ := 0
  M' _ := 0
  ρ' _ := 0
  ℓ' _ := 0
  cσ := continuousOn_const
  cu := continuousOn_const
  cM := continuousOn_const
  cρ := continuousOn_const
  cdφ := continuousOn_const
  cSu := continuousOn_const
  cdu := continuousOn_const
  cℓ _ := continuousOn_const
  cσ' := continuousOn_const
  cu' := continuousOn_const
  cM' := continuousOn_const
  cρ' := continuousOn_const
  cdφ' := continuousOn_const
  cSu' := continuousOn_const
  cdu' := continuousOn_const
  cℓ' _ := continuousOn_const
  dσ t _ := hasDerivWithinAt_const _ _ _
  du t _ := hasDerivWithinAt_const _ _ _
  dM t _ := hasDerivWithinAt_const _ _ _
  dρ t _ := hasDerivWithinAt_const _ _ _
  ddφ t _ := by simpa using hasDerivWithinAt_const t (Ici t) (bggSegment.dt0 (0 : Wv U0))
  dSu t _ := by simpa using hasDerivWithinAt_const t (Ici t) (bggSegment.S1 (0 : Wv U1))
  ddu t _ := by simpa using hasDerivWithinAt_const t (Ici t) (bggSegment.dt1 (0 : Wv U1))
  dℓ t _ μ := by simpa using hasDerivWithinAt_const t (Ici t) (0 : ℝ)
  ea _ _ τ ψ := by
    simp only [inner_zero_left, LinearMap.zero_apply, sub_zero]
  eb t _ v := by
    rw [srcFun_apply]
    simp only [map_zero, inner_zero_left, zero_add, Pi.zero_apply]
    exact inner_sawRho_dt1 v
  ec _ _ N := by simp
  ed _ _ μ := by simp
  ee _ _ := by rw [map_zero, map_zero]
  ee' _ _ := by rw [map_zero, map_zero]

theorem sawWave_isSobolevStateTr (T : ℝ) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 1 / 2) (t : ℝ) :
    IsSobolevStateTr s (parNorm Finset.univ 2 s sawWitness) ((sawWave T).σ t) ((sawWave T).φ t)
        ((sawWave T).u t) ((sawWave T).M t) ((sawWave T).ρ t) ∧
      IsSobolevStateTr s (parNorm Finset.univ 2 s sawWitness) ((sawWave T).σ' t)
        ((sawWave T).φ' t) ((sawWave T).u' t) ((sawWave T).M' t) ((sawWave T).ρ' t) := by
  have hL := parNorm_nonneg Finset.univ 2 s sawWitness
  have z0 := sobRel_zero (s := s) hL 0
  have z1 := sobRel_zero (s := s) hL 1
  have z2 := sobRel_zero (s := s) hL 2
  have hS : bggSegment.S1 (0 : Wv U1) = 0 := map_zero _
  have hd0 : ∀ a, D0 ((0 : Wv U0) a) = 0 := fun a => by
    change D0 (0 : U0) = 0; exact LinearPMap.map_zero _
  have hd1 : ∀ a, D1 ((0 : Wv U1) a) = 0 := fun a => by
    change D1 (0 : U1) = 0; exact LinearPMap.map_zero _
  have w0 : ∀ a, SobRel s (parNorm Finset.univ 2 s sawWitness) 1 (D0 ((0 : Wv U0) a)) :=
    fun a => by rw [hd0 a]; exact z1
  have w1 : ∀ a, SobRel s (parNorm Finset.univ 2 s sawWitness) 2 (D1 ((0 : Wv U1) a)) :=
    fun a => by rw [hd1 a]; exact z2
  have w2 : SobRel s (parNorm Finset.univ 2 s sawWitness) 2 (bggSegment.S1 (0 : Wv U1)) := by
    rw [hS]; exact z2
  refine ⟨⟨z0, w0, fun a => z1, w1, z2, fun a => ?_, w2⟩, ⟨z0, w0, fun a => z1, w1, z2,
    fun a => z2, w2⟩⟩
  change SobRel s _ 2 (sawRho a)
  by_cases ha : a = 0
  · subst ha; rw [sawRho_apply_zero]; exact sobRel_sawW2 hs0 hs
  · rw [sawRho_apply_of_ne ha]; exact z2

/-- **The sawtooth solution is outside the `C²` class of `cubeWave_rate_tr`**: its magnetic field
is in no class `IsCsFormTr 0 2 L` (it is not in `H̊Λ²(Q)`, `sawW2_not_mem_D2min`). -/
theorem not_isSmoothStateTr_sawWave (T t L : ℝ) :
    ¬ IsSmoothStateTr L ((sawWave T).σ t) ((sawWave T).φ t) ((sawWave T).u t) ((sawWave T).M t)
      ((sawWave T).ρ t) := fun h => by
  have h0 := (h.2.2.2.2 0).mem_domain
  change sawRho 0 ∈ _ at h0
  rw [sawRho_apply_zero, deRham_minimalComplex_d (isOpen_cubeDomain 3) 2] at h0
  exact sawW2_not_mem_D2min h0

set_option maxHeartbeats 2000000 in
/-- **Non-vacuity of `cubeWave_rate_sobolev` beyond the `C²` class** (and of the exponent
`h^{min(s,1)}` with `s < 1`): for every `0 ≤ s < ½` the stationary sawtooth solution `sawWave T`
of (6.2) satisfies all hypotheses of `cubeWave_rate_sobolev` with `L = ‖f dx₁ ∧ dx₂‖_{s,univ}`, so
(6.5) converges to it at the rate `h_N^s`; its magnetic field is not in `H^{1/2}_univ` and the
solution is in no class `IsSmoothStateTr` (`cubeWave_rate_tr` does not apply to it). -/
theorem cubeWave_rate_sobolev_nonvacuous {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
    (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
    (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C) {T : ℝ} (hT0 : 0 < T) {s : ℝ}
    (hs0 : 0 ≤ s) (hs : s < 1 / 2) :
    (∀ L, ¬ SobRel (1 / 2) L 2 ((sawWave T).ρ 0 0)) ∧
    (∀ t L, ¬ IsSmoothStateTr L ((sawWave T).σ t) ((sawWave T).φ t) ((sawWave T).u t)
      ((sawWave T).M t) ((sawWave T).ρ t)) ∧
    ∃ K, 0 ≤ K ∧ ∀ N, ∃ sh : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T
        (cubeSource hT hB N 0),
      ∀ t ∈ Icc 0 T, √(‖(sawWave T).σ t - sh.σ t‖ ^ 2 + ‖(sawWave T).u t - sh.u t‖ ^ 2 +
        ‖(sawWave T).M t - sh.M t‖ ^ 2 + ‖(sawWave T).ρ t - sh.ρ t‖ ^ 2) ≤
          K * (1 + t) * meshSize N ^ min s 1 := by
  refine ⟨fun L h => ?_, fun t L => not_isSmoothStateTr_sawWave T t L, ?_⟩
  · change SobRel (1 / 2) L 2 (sawRho 0) at h
    rw [sawRho_apply_zero] at h
    exact not_sobRel_sawW2_half L h
  have hrate := cubeWave_rate_sobolev hT hB
  obtain ⟨K, hK⟩ := hrate
  have hK0 := hK.1
  have hL := parNorm_nonneg Finset.univ 2 s sawWitness
  refine ⟨K * parNorm Finset.univ 2 s sawWitness, mul_nonneg hK0 hL, fun N => ?_⟩
  have h := hK.2 N hT0 continuousOn_const (sawWave T) hs0 hL
    (fun t _ => sawWave_isSobolevStateTr T hs0 hs t)
    (fun t _ v => ⟨by
        change |⟪(0 : W2), bggSegment.d1 v⟫| ≤ _
        rw [inner_zero_left, abs_zero]; exact mul_nonneg hL (norm_nonneg _), by
        change |⟪(0 : W2), bggSegment.d1 v⟫| ≤ _
        rw [inner_zero_left, abs_zero]; exact mul_nonneg hL (norm_nonneg _)⟩)
    (fun t _ μ => ⟨by
        change |(0 : U1 →ₗ[ℝ] ℝ) μ| ≤ _
        rw [LinearMap.zero_apply, abs_zero]; exact mul_nonneg hL (norm_nonneg _), by
        change |(0 : U1 →ₗ[ℝ] ℝ) μ| ≤ _
        rw [LinearMap.zero_apply, abs_zero]; exact mul_nonneg hL (norm_nonneg _)⟩)
  obtain ⟨sh, -, hb⟩ := h
  exact ⟨sh, hb⟩

end SawWave

end Feec.Models.Cube.WeakSymmetry
