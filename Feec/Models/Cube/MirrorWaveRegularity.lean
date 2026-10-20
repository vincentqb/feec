module

public import Feec.Models.Cube.MirrorWeakSymmetryTSD
public import Feec.Models.Cube.SobolevRate
public import Feec.Models.Cube.Sobolev

/-!
# Regularity of the mirror TSD wave and the unconditional rate of the mirror scheme (6.5)

`Feec.Models.Cube.MirrorWeakSymmetryTSD.mirror_waveFEM_rate` gives the `O(h)` rate of the mirror
scheme (6.5) of [QuennevilleBelair2015], §6.3, under the hypothesis that the forms states of the
TSD solution are `C²` up to `∂Q` (`IsSmoothStateMirror`). This file removes that hypothesis: the
rate holds for every TSD datum of `D(L³)`, and `O(hˢ)` holds for Sobolev data, `0 ≤ s ≤ 1`.

**The parity model.** The BGG complex on `Q = (0, ½)³` with mirror boundary conditions is the
compression of the torus complex along the mirror extensions `MirrorBGG.J` ([QuennevilleBelair2015],
§4.10: the cube by the method of images), so its wave group is the restriction of the torus wave
group, a Fourier multiplier. For a state `x` on `Q` let `e_x(m) = Σᵢ |(J x)ᵢ^(m)|²` be the energy of
its mirror extension at the frequency `m` (`fibreEnergy`) and
`‖x‖²_s = 8⁻¹ Σ_m ⟨ξ_m⟩^{2s} e_x(m)` its Sobolev norm (`sobState`, the `Hˢ(𝕋³)` norm of `J x`; the
factor `8⁻¹ = 2⁻³` makes `‖x‖_0 = ‖x‖`).

* **Invariance.** Each frequency `{m}` and its complement are reducing for the torus complex
  (`freqIn_reducing`, `freqOut_reducing`), so `e_{e^{tL}x}(m) = e_x(m)` for every `t ∈ ℝ`
  (`fibreEnergy_waveGroupQ`): every Sobolev norm of the mirror extension is conserved
  (`sobState_waveGroupQ`; the torus symbol is skew-Hermitian at each frequency). The wave group
  maps `D(L)` into `D(L)` and commutes with `L` for all `t ∈ ℝ` (`waveGroupQ_mem_domain_wave`), and
  preserves `D(Lᵏ)` with `‖Lʲ e^{tL} x‖ = ‖Lʲ x‖`, `j ≤ k` (`waveGroupQ_mem_domain_pow`,
  `norm_pow_waveGroupQ_eq`).
* **Identification on TSD states.** On the constraint `{0} × L²(TSD) × ({0} × L²(TSD))`,
  `e_{Lx}(m) = |ξ_m|² e_x(m)` (`fibreEnergy_waveQ_of_tsd`): `(L x)₁^(m) = -curl_ξ B̂(m)`,
  `(L x)₂^(m) = (0, curl_ξ Ê(m))`, and `|curl_ξ A| = |ξ| |A|` on symmetric matrices with `A ξ = 0`
  (`|ξ × a| = |ξ| |a|` when `ξ · a = 0`, row-wise). Hence `‖Lᵏ x‖² = 8⁻¹ Σ_m |ξ_m|^{2k} e_x(m)`
  (`norm_wavePow_sq_of_tsd`), `D(Lᵏ) ∩ TSD = Hᵏ ∩ TSD` (`mem_domain_pow_iff_sobolev_of_tsd`) with
  `‖Lᵏ x‖² ≤ ‖x‖²_k ≤ 2ᵏ (‖x‖² + ‖Lᵏ x‖²)` (`norm_wavePow_sq_le_sobState`), and
  `‖x‖²_1 = ‖x‖² + ‖L x‖²` (`sobState_one_of_tsd`). The compatibility conditions of `D(Lᵏ)` at
  `∂Q` are exactly the mirror parities.
* **Rows in the parity classes.** For `J x ∈ Hˢ(𝕋³)` the rows `(Re E)_a` (`1`-forms) and
  `(⋆Re B)_a` (`2`-forms) lie in the parity Sobolev classes `Hˢ_{a}(Q)` of the bottom row of
  `MirrorClose`, with `‖·‖_{s,{a}} ≤ ‖x‖_s` (`rowRe_sobolevPar`, `rowRe2_sobolevPar`; the
  coefficients of the parity extension are `½ (Ê(m) + conj Ê(-m))`, `coeff_JfJ_rowRe`).
* **Closeness.** The parity-smoothed projections approximate `Hˢ_{a}` data at the rate `hˢ`:
  `‖y − π y‖ ≤ (1 + 2C) dist(y, V_{h,Γ_{a}}) ≤ (1 + 2C) C_s hˢ ‖y‖_{s,{a}}` (`norm_sub_projB_le`,
  from `infDist_polyPartial_le_sobolevPar`, [AFW2010], §5.4), so the TSD forms states and their
  time derivatives are `MirrorClose` at level `C hˢ (‖U₀‖_s + ‖LU₀‖_s + ‖L²U₀‖_s)`
  (`mirrorClose_of_sobolev`, `TSDDatum.mirrorClose_state`, `TSDDatum.mirrorClose_deriv`;
  `σ ≡ 0`, `φ ≡ 0`, `M ≡ 0` and `S¹u = 0` for TSD states).

## Main results

* **`mirror_waveFEM_rate_of_mem_domain`**: for every TSD datum with `L² U₀ ∈ D(L)` (i.e.
  `U₀ ∈ D(L³)`), the conclusion of `mirror_waveFEM_rate` with the bound
  `K (‖U₀‖ + ‖LU₀‖ + ‖L²U₀‖ + ‖L³U₀‖)(1 + t) h_N`, no smoothness hypothesis.
* **`mirror_waveFEM_rate_sobolev`**: the bound `K (‖U₀‖_s + ‖LU₀‖_s + ‖L²U₀‖_s)(1 + t) h_Nˢ` for
  TSD data whose mirror extensions `J U₀`, `J LU₀`, `J L²U₀` lie in `Hˢ(𝕋³)`, `0 ≤ s ≤ 1`.
* `mirror_waveFEM_rate_of_mem_domain_nonvacuous`: the cos datum of `mirror_waveFEM_nonvacuous`
  lies in `D(L³)` (`cosDatum_LLU₀_mem`) and in every `Hˢ`, `s ≤ 1`.
* `sobState_waveGroupQ`, `waveGroupQ_mem_domain_pow`, `norm_pow_waveGroupQ_eq`,
  `norm_wavePow_sq_of_tsd`, `mem_domain_pow_iff_sobolev_of_tsd`, `norm_wavePow_sq_le_sobState`,
  `rowRe_sobolevPar`, `rowRe2_sobolevPar`, `mirrorClose_of_sobolev`.

No hypothesis is assumed. **The data class.** The Strang data of (6.4) contain `d u'`, the rows of
`⋆Re B''`, so the proof needs `J L² U₀ ∈ Hˢ`: `U₀ ∈ D(L³)` for `O(h)` (on TSD data,
`D(L³) = H³` of the mirror extension), and `J L² U₀ ∈ Hˢ` (roughly `H^{2+s}` data) for `O(hˢ)`.
Not formalized: a TSD datum of `D(L³)` that is not `C²` (expected, since `H³(𝕋³) ⊄ C²(𝕋³)`; the
embedding `Hˢ ⊆ C²` needs `s > 7/2`), and whether a sharper analysis of (6.5) needs less than
`D(L³)` for `O(h)`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 6 (§6.3, (6.5); §6.2, (6.4)), §4.10 (the cube by the method of images)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.4 (smoothed projections)
-/

open scoped InnerProductSpace ComplexConjugate LinearPMap
open Set MeasureTheory Filter Finset

@[expose] public noncomputable section

namespace Feec.Models.Cube.MirrorWeakSymmetry

open Feec.Fourier.GradCurl (Mat Vec curl curl_apply)
open Feec.Fourier.BGG (VM bgg bgg_apply bggFamily tsdB mem_tsdB)
open Feec.ShortHilbertComplex (W3)
open Feec.HilbertComplex (totalSub totalJ)
open Feec.Models.Cube.Mirror (MQ VQ)
open Feec.Models.Cube.DeRhamIdent (cjForm cjForm_apply)

/-! ### `ℓ²` on the lattice -/

section Lattice

variable {E : Type*} [NormedAddCommGroup E]

theorem norm_sq_eq_tsum_count [NormedSpace ℂ E] (f : Lp E 2 (Measure.count : Measure (Fin 3 → ℤ))) :
    ‖f‖ ^ 2 = ∑' m, ‖(f : (Fin 3 → ℤ) → E) m‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    ((lp.equivLpCount ℂ (Fin 3 → ℤ) E 2).symm f)
  rw [LinearIsometryEquiv.norm_map] at h
  simp only [lp.equivLpCount_symm_apply, ENNReal.toReal_ofNat] at h
  simpa only [Real.rpow_two] using h

theorem summable_norm_sq_count (f : Lp E 2 (Measure.count : Measure (Fin 3 → ℤ))) :
    Summable fun m => ‖(f : (Fin 3 → ℤ) → E) m‖ ^ 2 := by
  have h := (lp.memℓp_count (Fin 3 → ℤ) E 2 f).summable (by norm_num)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

theorem memLp_count_of_summable {f : (Fin 3 → ℤ) → E} (hf : Summable fun m => ‖f m‖ ^ 2) :
    MemLp f 2 (Measure.count : Measure (Fin 3 → ℤ)) :=
  (memLp_count_iff (by norm_num)).2 (memℓp_gen (by simpa using hf))

open Classical in
/-- The restriction of a coefficient sequence to the frequency `m`. -/
def singleCount (m : Fin 3 → ℤ) (f : Lp E 2 (Measure.count : Measure (Fin 3 → ℤ))) :
    Lp E 2 (Measure.count : Measure (Fin 3 → ℤ)) :=
  (memLp_count_of_summable (f := fun k => if k = m then (f : (Fin 3 → ℤ) → E) k else 0)
    (summable_of_ne_finset_zero (s := {m}) fun k hk => by
      simp [Finset.mem_singleton.not.1 hk])).toLp _

open Classical in
theorem singleCount_apply (m : Fin 3 → ℤ) (f : Lp E 2 (Measure.count : Measure (Fin 3 → ℤ)))
    (k : Fin 3 → ℤ) :
    (singleCount m f : (Fin 3 → ℤ) → E) k = if k = m then (f : (Fin 3 → ℤ) → E) k else 0 :=
  Measure.ae_count_iff.1 (MemLp.coeFn_toLp _) k

end Lattice

/-! ### The energy of a torus state at one frequency -/

/-- **The energy of a torus state at the frequency `m`**: `Σᵢ |X̂ᵢ(m)|²`. -/
def fibreEnergy (X : PiLp 2 Models.Torus.BGG.Space) (m : Fin 3 → ℤ) : ℝ :=
  ∑ i : Fin 3, ‖(X i : (Fin 3 → ℤ) → W3 ℂ Mat VM i) m‖ ^ 2

theorem fibreEnergy_nonneg (X : PiLp 2 Models.Torus.BGG.Space) (m : Fin 3 → ℤ) :
    0 ≤ fibreEnergy X m :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The scalar coefficient `X̂₀(m)`. -/
abbrev tc0 (X : PiLp 2 Models.Torus.BGG.Space) (m : Fin 3 → ℤ) : ℂ :=
  (X 0 : (Fin 3 → ℤ) → W3 ℂ Mat VM 0) m

/-- The matrix coefficient `X̂₁(m)`. -/
abbrev tc1 (X : PiLp 2 Models.Torus.BGG.Space) (m : Fin 3 → ℤ) : Mat :=
  (X 1 : (Fin 3 → ℤ) → W3 ℂ Mat VM 1) m

/-- The pair coefficient `X̂₂(m)`. -/
abbrev tc2 (X : PiLp 2 Models.Torus.BGG.Space) (m : Fin 3 → ℤ) : VM :=
  (X 2 : (Fin 3 → ℤ) → W3 ℂ Mat VM 2) m

theorem fibreEnergy_eq (X : PiLp 2 Models.Torus.BGG.Space) (m : Fin 3 → ℤ) :
    fibreEnergy X m = ‖tc0 X m‖ ^ 2 + ‖tc1 X m‖ ^ 2 + ‖tc2 X m‖ ^ 2 := by
  rw [fibreEnergy, Fin.sum_univ_three]
  rfl

theorem summable_fibreEnergy (X : PiLp 2 Models.Torus.BGG.Space) :
    Summable (fibreEnergy X) := by
  unfold fibreEnergy
  exact summable_sum fun i _ => summable_norm_sq_count (X i)

/-- **Parseval on the torus**: `‖X‖² = Σ_m Σᵢ |X̂ᵢ(m)|²`. -/
theorem norm_sq_eq_tsum_fibreEnergy (X : PiLp 2 Models.Torus.BGG.Space) :
    ‖X‖ ^ 2 = ∑' m, fibreEnergy X m := by
  rw [PiLp.norm_sq_eq_of_L2]
  unfold fibreEnergy
  rw [Summable.tsum_finsetSum fun i _ => summable_norm_sq_count (X i)]
  exact Finset.sum_congr rfl fun i _ => norm_sq_eq_tsum_count (X i)

/-! ### Conservation of the energy at each frequency -/

open Classical in
/-- The fibres of the frequency `m`: everything at `m`, nothing elsewhere. -/
def freqIn (m : Fin 3 → ℤ) (i : Fin 3) (k : Fin 3 → ℤ) : Submodule ℂ (W3 ℂ Mat VM i) :=
  if k = m then ⊤ else ⊥

open Classical in
/-- The fibres off the frequency `m`. -/
def freqOut (m : Fin 3 → ℤ) (i : Fin 3) (k : Fin 3 → ℤ) : Submodule ℂ (W3 ℂ Mat VM i) :=
  if k = m then ⊥ else ⊤

instance (m : Fin 3 → ℤ) (i : Fin 3) (k : Fin 3 → ℤ) : (freqIn m i k).HasOrthogonalProjection := by
  unfold freqIn; split <;> infer_instance

instance (m : Fin 3 → ℤ) (i : Fin 3) (k : Fin 3 → ℤ) : (freqOut m i k).HasOrthogonalProjection := by
  unfold freqOut; split <;> infer_instance

theorem freqIn_reducing (m : Fin 3 → ℤ) :
    Fourier.FibreReducing (Fourier.Torus.symbolComplex bggFamily) (freqIn m) where
  map i j k := by
    unfold freqIn; split_ifs
    · exact le_top
    · rw [Submodule.map_bot]
  map_adj i j k := by
    unfold freqIn; split_ifs
    · exact le_top
    · rw [Submodule.map_bot]
  meas _ := AEStronglyMeasurable.of_discrete

theorem freqOut_reducing (m : Fin 3 → ℤ) :
    Fourier.FibreReducing (Fourier.Torus.symbolComplex bggFamily) (freqOut m) where
  map i j k := by
    unfold freqOut; split_ifs
    · rw [Submodule.map_bot]
    · exact le_top
  map_adj i j k := by
    unfold freqOut; split_ifs
    · rw [Submodule.map_bot]
    · exact le_top
  meas _ := AEStronglyMeasurable.of_discrete

theorem coeFn_add_count {E : Type*} [NormedAddCommGroup E]
    (f g : Lp E 2 (Measure.count : Measure (Fin 3 → ℤ))) (n : Fin 3 → ℤ) :
    ((f + g : Lp E 2 _) : (Fin 3 → ℤ) → E) n = (f : (Fin 3 → ℤ) → E) n + (g : (Fin 3 → ℤ) → E) n :=
  Measure.ae_count_iff.1 (Lp.coeFn_add f g) n

/-- The restriction of a torus state to the frequency `m`. -/
def singleState (m : Fin 3 → ℤ) (X : PiLp 2 Models.Torus.BGG.Space) :
    PiLp 2 Models.Torus.BGG.Space :=
  WithLp.toLp 2 fun i => singleCount m (X i)

theorem singleState_apply (m : Fin 3 → ℤ) (X : PiLp 2 Models.Torus.BGG.Space) (i : Fin 3)
    (k : Fin 3 → ℤ) :
    ((singleState m X i : Models.Torus.BGG.Space i) : (Fin 3 → ℤ) → W3 ℂ Mat VM i) k =
      if k = m then (X i : (Fin 3 → ℤ) → W3 ℂ Mat VM i) k else 0 := by
  classical
  exact singleCount_apply m (X i) k

theorem singleState_mem (m : Fin 3 → ℤ) (X : PiLp 2 Models.Torus.BGG.Space) :
    singleState m X ∈ totalSub fun i => Operator.fibreSub Measure.count (freqIn m i) := fun i =>
  Operator.mem_fibreSub.2 (Measure.ae_count_iff.2 fun k => by
    rw [singleState_apply]
    by_cases hk : k = m
    · simp [freqIn, hk]
    · simp [freqIn, hk])

theorem sub_singleState_mem (m : Fin 3 → ℤ) (X : PiLp 2 Models.Torus.BGG.Space) :
    X - singleState m X ∈ totalSub fun i => Operator.fibreSub Measure.count (freqOut m i) :=
  fun i => Operator.mem_fibreSub.2 (Measure.ae_count_iff.2 fun k => by
    rw [PiLp.sub_apply, coeFn_sub_count, singleState_apply]
    by_cases hk : k = m
    · simp [freqOut, hk]
    · simp [freqOut, hk])

/-- A state concentrated at the frequency `m` has `‖Y‖² = Σᵢ |Ŷᵢ(m)|²`. -/
theorem norm_sq_eq_fibreEnergy_of_mem {m : Fin 3 → ℤ} {Y : PiLp 2 Models.Torus.BGG.Space}
    (hY : Y ∈ totalSub fun i => Operator.fibreSub Measure.count (freqIn m i)) :
    ‖Y‖ ^ 2 = fibreEnergy Y m := by
  rw [norm_sq_eq_tsum_fibreEnergy]
  refine tsum_eq_single m fun k hk => Finset.sum_eq_zero fun i _ => ?_
  have h := Measure.ae_count_iff.1 (Operator.mem_fibreSub.1 (hY i)) k
  simp only [freqIn, hk, ite_false, Submodule.mem_bot] at h
  rw [h, norm_zero, zero_pow two_ne_zero]

/-- **The energy at each frequency is conserved by the torus wave group**: the frequency `m`
and its complement are reducing (`freqIn_reducing`, `freqOut_reducing`). -/
theorem fibreEnergy_waveGroup_torus (t : ℝ) (X : PiLp 2 Models.Torus.BGG.Space)
    (m : Fin 3 → ℤ) :
    fibreEnergy (Models.Torus.BGG.complex.waveGroup.S t X) m = fibreEnergy X m := by
  have : ∀ i, (Operator.fibreSub (Measure.count : Measure (Fin 3 → ℤ))
      (freqIn m i)).HasOrthogonalProjection := (freqIn_reducing m).hasOrthogonalProjection
  have : ∀ i, (Operator.fibreSub (Measure.count : Measure (Fin 3 → ℤ))
      (freqOut m i)).HasOrthogonalProjection := (freqOut_reducing m).hasOrthogonalProjection
  set A := singleState m X
  have hSA : Models.Torus.BGG.complex.waveGroup.S t A ∈
      totalSub fun i => Operator.fibreSub Measure.count (freqIn m i) :=
    (freqIn_reducing m).waveGroup_mem t (singleState_mem m X)
  have hSB : Models.Torus.BGG.complex.waveGroup.S t (X - A) ∈
      totalSub fun i => Operator.fibreSub Measure.count (freqOut m i) :=
    (freqOut_reducing m).waveGroup_mem t (sub_singleState_mem m X)
  have e : Models.Torus.BGG.complex.waveGroup.S t X =
      Models.Torus.BGG.complex.waveGroup.S t A +
        Models.Torus.BGG.complex.waveGroup.S t (X - A) := by
    rw [← map_add, add_sub_cancel]
  have hcoef : ∀ i, ((Models.Torus.BGG.complex.waveGroup.S t X) i :
      (Fin 3 → ℤ) → W3 ℂ Mat VM i) m =
        ((Models.Torus.BGG.complex.waveGroup.S t A) i : (Fin 3 → ℤ) → W3 ℂ Mat VM i) m := by
    intro i
    have h0 := Measure.ae_count_iff.1 (Operator.mem_fibreSub.1 (hSB i)) m
    simp only [freqOut, ite_true, Submodule.mem_bot] at h0
    rw [e, PiLp.add_apply, coeFn_add_count, h0, add_zero]
  have hA : ∀ i, ((A i : Models.Torus.BGG.Space i) : (Fin 3 → ℤ) → W3 ℂ Mat VM i) m =
      (X i : (Fin 3 → ℤ) → W3 ℂ Mat VM i) m := fun i => by
    rw [singleState_apply]; simp
  calc fibreEnergy (Models.Torus.BGG.complex.waveGroup.S t X) m =
        fibreEnergy (Models.Torus.BGG.complex.waveGroup.S t A) m := by
          unfold fibreEnergy; exact Finset.sum_congr rfl fun i _ => by rw [hcoef i]
    _ = ‖Models.Torus.BGG.complex.waveGroup.S t A‖ ^ 2 :=
          (norm_sq_eq_fibreEnergy_of_mem hSA).symm
    _ = ‖A‖ ^ 2 := by rw [Models.Torus.BGG.complex.isIsometric_waveGroup t A]
    _ = fibreEnergy A m := norm_sq_eq_fibreEnergy_of_mem (singleState_mem m X)
    _ = fibreEnergy X m := by
          unfold fibreEnergy; exact Finset.sum_congr rfl fun i _ => by rw [hA i]

/-! ### States on `Q` through the mirror extensions -/

/-- The mirror extension of a state on `Q` to the torus. -/
abbrev extState (x : PiLp 2 MirrorBGG.SpaceQ) : PiLp 2 Models.Torus.BGG.Space :=
  totalJ MirrorBGG.J x

theorem norm_J_sq (i : Fin 3) (y : MirrorBGG.SpaceQ i) :
    ‖MirrorBGG.J i y‖ ^ 2 = 8 * ‖y‖ ^ 2 := by
  rw [HilbertComplex.norm_apply_of_inner Mirror.eight_pos MirrorBGG.inner_J i y, mul_pow,
    Real.sq_sqrt (by norm_num)]

/-- `‖J x‖² = 8 ‖x‖²` (the mirror extensions have scale `8 = 2³`). -/
theorem norm_extState_sq (x : PiLp 2 MirrorBGG.SpaceQ) :
    ‖extState x‖ ^ 2 = 8 * ‖x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => norm_J_sq i (x i)

/-- **Parseval for states on `Q`**: `‖x‖² = 8⁻¹ Σ_m Σᵢ |(J x)ᵢ^(m)|²`. -/
theorem norm_sq_eq_tsum_extState (x : PiLp 2 MirrorBGG.SpaceQ) :
    ‖x‖ ^ 2 = 8⁻¹ * ∑' m, fibreEnergy (extState x) m := by
  rw [← norm_sq_eq_tsum_fibreEnergy, norm_extState_sq]; ring

/-- **The energy at each frequency of the mirror extension is conserved by the wave group on
`Q`** (the wave group on `Q` is the compression of the torus wave group). -/
theorem fibreEnergy_waveGroupQ (t : ℝ) (x : PiLp 2 MirrorBGG.SpaceQ) (m : Fin 3 → ℤ) :
    fibreEnergy (extState (MirrorBGG.complexQ.waveGroup.S t x)) m =
      fibreEnergy (extState x) m := by
  rw [extState, HilbertComplex.waveGroup_compress Mirror.eight_pos MirrorBGG.inner_J
    MirrorBGG.reducingSubcomplex_range]
  exact fibreEnergy_waveGroup_torus t _ m

/-! ### Sobolev norms of states through the torus weights -/

open Feec.Models.Cube.Sobolev (weight weight_nonneg weight_pos weight_zero weight_one)

/-- **The Sobolev norm of a state on `Q`**: `‖x‖²_s = 8⁻¹ Σ_m ⟨ξ_m⟩^{2s} Σᵢ |(J x)ᵢ^(m)|²`, the
`Hˢ(𝕋³)` norm of the mirror extension (the factor `8⁻¹` makes it the `L²(Q)` norm for `s = 0`). -/
def sobState (s : ℝ) (x : PiLp 2 MirrorBGG.SpaceQ) : ℝ :=
  8⁻¹ * ∑' m, weight s m * fibreEnergy (extState x) m

/-- `x ∈ Hˢ`: the mirror extension of the state lies in `Hˢ(𝕋³)`. -/
def MemSobState (s : ℝ) (x : PiLp 2 MirrorBGG.SpaceQ) : Prop :=
  Summable fun m => weight s m * fibreEnergy (extState x) m

theorem sobState_nonneg (s : ℝ) (x : PiLp 2 MirrorBGG.SpaceQ) : 0 ≤ sobState s x :=
  mul_nonneg (by norm_num) (tsum_nonneg fun m =>
    mul_nonneg (weight_nonneg s m) (fibreEnergy_nonneg _ m))

theorem sobState_zero (x : PiLp 2 MirrorBGG.SpaceQ) : sobState 0 x = ‖x‖ ^ 2 := by
  simp [sobState, norm_sq_eq_tsum_extState]

theorem memSobState_zero (x : PiLp 2 MirrorBGG.SpaceQ) : MemSobState 0 x := by
  simpa [MemSobState] using summable_fibreEnergy (extState x)

/-- **The wave group preserves every Sobolev norm of states**: `‖e^{tL} x‖_s = ‖x‖_s`, for every
`s` and every `t` (the torus symbol is skew-Hermitian at each frequency). -/
theorem sobState_waveGroupQ (s t : ℝ) (x : PiLp 2 MirrorBGG.SpaceQ) :
    sobState s (MirrorBGG.complexQ.waveGroup.S t x) = sobState s x := by
  unfold sobState
  simp_rw [fibreEnergy_waveGroupQ]

theorem memSobState_waveGroupQ_iff (s t : ℝ) (x : PiLp 2 MirrorBGG.SpaceQ) :
    MemSobState s (MirrorBGG.complexQ.waveGroup.S t x) ↔ MemSobState s x := by
  unfold MemSobState
  simp_rw [fibreEnergy_waveGroupQ]

/-! ### `L` on TSD states, one frequency at a time -/

open Feec.Fourier.GradCurl (tsd norm_curl_of_mem_tsd)

/-- `(S₁, curl)_ξ† (0, N) = curl_ξ N`. -/
theorem adjoint_bgg_inr (ξ : Fourier.GradCurl.Freq) (N : Mat) :
    ContinuousLinearMap.adjoint (bgg ξ) (WithLp.toLp 2 ((0 : Vec), N)) = curl ξ N := by
  refine ext_inner_left ℂ fun M => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, bgg_apply, WithLp.prod_inner_apply,
    WithLp.ofLp_toLp, WithLp.ofLp_toLp, inner_zero_right, zero_add,
    Fourier.GradCurl.inner_curl]

theorem norm_sq_VM (w : VM) : ‖w‖ ^ 2 = ‖(WithLp.ofLp w).1‖ ^ 2 + ‖(WithLp.ofLp w).2‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 w

/-- **The torus wave operator on a TSD state, at one frequency**: for `X ∈ D(L)` in the
constraint `{0} × L²(TSD) × ({0} × L²(TSD))`, `Σᵢ |(L X)ᵢ^(m)|² = |ξ_m|² Σᵢ |X̂ᵢ(m)|²`
(`(L X)₁^(m) = -curl_ξ B̂(m)`, `(L X)₂^(m) = (0, curl_ξ Ê(m))`, and `|curl_ξ A| = |ξ| |A|` on
`tsd ξ`, since `|ξ × x| = |ξ| |x|` when `ξ · x = 0`). -/
theorem fibreEnergy_wave_torus (X : Models.Torus.BGG.complex.wave.domain)
    (hX : (X : PiLp 2 Models.Torus.BGG.Space) ∈ totalSub Models.Torus.BGG.constraint)
    (m : Fin 3 → ℤ) :
    fibreEnergy (Models.Torus.BGG.complex.wave X) m =
      ‖Fourier.Torus.freq m‖ ^ 2 * fibreEnergy X m := by
  have hL : Models.Torus.BGG.complex.wave X ∈ totalSub Models.Torus.BGG.constraint :=
    Models.Torus.BGG.reducingSubcomplex.isReducing_wave.mapsTo X hX
  have h0 : ((X : PiLp 2 Models.Torus.BGG.Space) 0 : Models.Torus.BGG.Space 0) = 0 :=
    Models.Torus.BGG.mem_constraint_zero_iff.1 (hX 0)
  have hL0 : ((Models.Torus.BGG.complex.wave X) 0 : Models.Torus.BGG.Space 0) = 0 :=
    Models.Torus.BGG.mem_constraint_zero_iff.1 (hL 0)
  have hE : tc1 X m ∈ tsd (Fourier.Torus.freq m) :=
    Measure.ae_count_iff.1 (Operator.mem_fibreSub.1 (hX 1)) m
  obtain ⟨hB0, hB⟩ := Models.Torus.BGG.mem_constraint_two_iff.1 (hX 2) m
  have hB0' : (WithLp.ofLp (tc2 X m)).1 = 0 := hB0
  have hB' : (WithLp.ofLp (tc2 X m)).2 ∈ tsd (Fourier.Torus.freq m) := hB
  have hw : tc2 X m = WithLp.toLp 2 ((0 : Vec), (WithLp.ofLp (tc2 X m)).2) := by
    rw [← hB0']; rfl
  -- `(L X)₂`
  have e2 : tc2 (Models.Torus.BGG.complex.wave X) m = bgg (Fourier.Torus.freq m) (tc1 X m) := by
    change (((Models.Torus.BGG.complex.wave X) 2 : Models.Torus.BGG.Space 2) :
      (Fin 3 → ℤ) → W3 ℂ Mat VM 2) m = _
    rw [Models.Torus.BGG.wave_apply_two]
    exact Operator.coeFn_mulOp_count (fun n => bggFamily.m 1 2 (Fourier.Torus.freq n)) _ m
  -- `(L X)₁`
  have hd0 : Models.Torus.BGG.complex.d 0 1
      ⟨(X : PiLp 2 Models.Torus.BGG.Space) 0, X.2.1 0 1⟩ = 0 := by
    rw [LinearPMap.apply_congr' _ _ (Submodule.zero_mem _) h0]
    exact LinearPMap.map_zero _
  have eadj : (Models.Torus.BGG.complex.d 1 2)† = Operator.mulOp Measure.count fun n =>
      ContinuousLinearMap.adjoint (bggFamily.m 1 2 (Fourier.Torus.freq n)) :=
    (Fourier.Torus.symbolComplex bggFamily).adjoint_d 1 2
  have hy' : ((X : PiLp 2 Models.Torus.BGG.Space) 2 : Models.Torus.BGG.Space 2) ∈
      (Operator.mulOp Measure.count fun n =>
        ContinuousLinearMap.adjoint (bggFamily.m 1 2 (Fourier.Torus.freq n))).domain :=
    eadj ▸ X.2.2 2 1
  have hneg : ((Models.Torus.BGG.complex.wave X) 1 : Models.Torus.BGG.Space 1) =
      -(Models.Torus.BGG.complex.d 1 2)† ⟨(X : PiLp 2 Models.Torus.BGG.Space) 2, X.2.2 2 1⟩ := by
    rw [Models.Torus.BGG.wave_apply_one, hd0, zero_sub]
  have hadj : (((Models.Torus.BGG.complex.d 1 2)†
      ⟨(X : PiLp 2 Models.Torus.BGG.Space) 2, X.2.2 2 1⟩ : Models.Torus.BGG.Space 1) :
        (Fin 3 → ℤ) → W3 ℂ Mat VM 1) m =
      ContinuousLinearMap.adjoint (bgg (Fourier.Torus.freq m)) (tc2 X m) := by
    rw [LinearPMap.apply_eq_of_eq eadj ⟨_, X.2.2 2 1⟩ ⟨_, hy'⟩ rfl]
    exact Operator.coeFn_mulOp_count (𝕜 := ℂ) _ ⟨_, hy'⟩ m
  have hadj' : ContinuousLinearMap.adjoint (bgg (Fourier.Torus.freq m)) (tc2 X m) =
      curl (Fourier.Torus.freq m) (WithLp.ofLp (tc2 X m)).2 := by
    conv_lhs => rw [hw]
    exact adjoint_bgg_inr _ _
  have e1 : tc1 (Models.Torus.BGG.complex.wave X) m =
      -curl (Fourier.Torus.freq m) (WithLp.ofLp (tc2 X m)).2 := by
    change (((Models.Torus.BGG.complex.wave X) 1 : Models.Torus.BGG.Space 1) :
      (Fin 3 → ℤ) → W3 ℂ Mat VM 1) m = _
    rw [hneg, Measure.ae_count_iff.1 (Lp.coeFn_neg _) m, Pi.neg_apply, hadj, hadj']
    rfl
  have n1 : ‖tc1 (Models.Torus.BGG.complex.wave X) m‖ =
      ‖Fourier.Torus.freq m‖ * ‖(WithLp.ofLp (tc2 X m)).2‖ :=
    (congrArg norm e1).trans ((norm_neg _).trans (norm_curl_of_mem_tsd hB'))
  have n2 : ‖tc2 (Models.Torus.BGG.complex.wave X) m‖ ^ 2 =
      ‖Fourier.Torus.freq m‖ ^ 2 * ‖tc1 X m‖ ^ 2 := by
    have haxial : Fourier.BGG.axialL (tc1 X m) = 0 := (mem_tsdB.1 (Fourier.BGG.bgg_mem_tsdB hE)).1
    rw [e2, norm_sq_VM]
    change ‖Fourier.BGG.axialL (tc1 X m)‖ ^ 2 + ‖curl (Fourier.Torus.freq m) (tc1 X m)‖ ^ 2 = _
    rw [haxial, norm_zero, norm_curl_of_mem_tsd hE]
    ring
  have n3 : ‖tc2 X m‖ ^ 2 = ‖(WithLp.ofLp (tc2 X m)).2‖ ^ 2 := by
    rw [norm_sq_VM, hB0', norm_zero]; ring
  have c0 : ∀ Y : PiLp 2 Models.Torus.BGG.Space,
      (Y 0 : Models.Torus.BGG.Space 0) = 0 → ‖tc0 Y m‖ ^ 2 = 0 := by
    intro Y hY
    change ‖((Y 0 : Models.Torus.BGG.Space 0) : (Fin 3 → ℤ) → ℂ) m‖ ^ 2 = 0
    rw [hY, Measure.ae_count_iff.1 (Lp.coeFn_zero _ 2 Measure.count) m]
    simp
  rw [fibreEnergy_eq, fibreEnergy_eq, c0 _ hL0, c0 _ h0, n1, n2, n3]
  ring

/-- `J` maps the constraint on `Q` into the torus constraint. -/
theorem extState_mem_constraint {x : PiLp 2 MirrorBGG.SpaceQ}
    (hx : x ∈ totalSub MirrorBGG.tsdQ) :
    extState x ∈ totalSub Models.Torus.BGG.constraint := fun i => hx i

theorem extState_mem_wave_domain {x : PiLp 2 MirrorBGG.SpaceQ}
    (hx : x ∈ MirrorBGG.complexQ.wave.domain) :
    extState x ∈ Models.Torus.BGG.complex.wave.domain :=
  (HilbertComplex.mem_wave_domain_compress_iff Mirror.eight_pos MirrorBGG.inner_J
    MirrorBGG.reducingSubcomplex_range).1 hx

/-- `J L = L J`. -/
theorem extState_wave (x : MirrorBGG.complexQ.wave.domain) :
    extState (MirrorBGG.complexQ.wave x) =
      Models.Torus.BGG.complex.wave ⟨extState x, extState_mem_wave_domain x.2⟩ :=
  ((HilbertComplex.wave_compress Mirror.eight_pos MirrorBGG.inner_J
    MirrorBGG.reducingSubcomplex_range).comm x).symm

/-- **`L` on TSD states on `Q`, one frequency at a time**:
`Σᵢ |(J L x)ᵢ^(m)|² = |ξ_m|² Σᵢ |(J x)ᵢ^(m)|²`. -/
theorem fibreEnergy_waveQ_of_tsd (x : MirrorBGG.complexQ.wave.domain)
    (hx : (x : PiLp 2 MirrorBGG.SpaceQ) ∈ totalSub MirrorBGG.tsdQ) (m : Fin 3 → ℤ) :
    fibreEnergy (extState (MirrorBGG.complexQ.wave x)) m =
      ‖Fourier.Torus.freq m‖ ^ 2 * fibreEnergy (extState x) m := by
  rw [extState_wave]
  exact fibreEnergy_wave_torus ⟨_, extState_mem_wave_domain x.2⟩ (extState_mem_constraint hx) m

theorem waveQ_mem_tsd (x : MirrorBGG.complexQ.wave.domain)
    (hx : (x : PiLp 2 MirrorBGG.SpaceQ) ∈ totalSub MirrorBGG.tsdQ) :
    MirrorBGG.complexQ.wave x ∈ totalSub MirrorBGG.tsdQ :=
  MirrorBGG.reducingSubcomplexQ.isReducing_wave.mapsTo x hx

/-- **`‖L x‖² = 8⁻¹ Σ_m |ξ_m|² Σᵢ |(J x)ᵢ^(m)|²` on TSD states.** -/
theorem norm_waveQ_sq_of_tsd (x : MirrorBGG.complexQ.wave.domain)
    (hx : (x : PiLp 2 MirrorBGG.SpaceQ) ∈ totalSub MirrorBGG.tsdQ) :
    ‖MirrorBGG.complexQ.wave x‖ ^ 2 =
      8⁻¹ * ∑' m, ‖Fourier.Torus.freq m‖ ^ 2 * fibreEnergy (extState x) m := by
  rw [norm_sq_eq_tsum_extState]
  simp_rw [fibreEnergy_waveQ_of_tsd x hx]

theorem summable_freq_sq_fibreEnergy_of_tsd (x : MirrorBGG.complexQ.wave.domain)
    (hx : (x : PiLp 2 MirrorBGG.SpaceQ) ∈ totalSub MirrorBGG.tsdQ) :
    Summable fun m => ‖Fourier.Torus.freq m‖ ^ 2 * fibreEnergy (extState x) m := by
  exact (summable_fibreEnergy _).congr fun m => fibreEnergy_waveQ_of_tsd x hx m

/-- **On TSD states of `D(L)`, the `H¹` norm is the graph norm**: `x ∈ H¹` and
`‖x‖²_1 = ‖x‖² + ‖L x‖²`. -/
theorem memSobState_one_of_tsd (x : MirrorBGG.complexQ.wave.domain)
    (hx : (x : PiLp 2 MirrorBGG.SpaceQ) ∈ totalSub MirrorBGG.tsdQ) :
    MemSobState 1 x :=
  ((summable_fibreEnergy _).add (summable_freq_sq_fibreEnergy_of_tsd x hx)).congr fun m => by
    rw [weight_one]; ring

theorem sobState_one_of_tsd (x : MirrorBGG.complexQ.wave.domain)
    (hx : (x : PiLp 2 MirrorBGG.SpaceQ) ∈ totalSub MirrorBGG.tsdQ) :
    sobState 1 x = ‖(x : PiLp 2 MirrorBGG.SpaceQ)‖ ^ 2 + ‖MirrorBGG.complexQ.wave x‖ ^ 2 := by
  rw [sobState, norm_sq_eq_tsum_extState, norm_waveQ_sq_of_tsd x hx, ← mul_add,
    ← Summable.tsum_add (summable_fibreEnergy _) (summable_freq_sq_fibreEnergy_of_tsd x hx)]
  congr 1
  refine tsum_congr fun m => ?_
  rw [weight_one]; ring

/-! ### The rows of the fields in the parity Sobolev classes -/

open Feec.Models.Cube.Sobolev (Seq cf sobSum MemSob sobolevPar parNorm parNorm_sq mem_sobolevPar)
open Feec.Models.Cube.DeRhamIdent (JfJ)
open Feec.Fourier.Exterior (Form)
open Feec.Models.Cube.MirrorExt (extF)

theorem weight_neg (s : ℝ) (m : Fin 3 → ℤ) : weight s (-m) = weight s m := by
  simp [weight, Fourier.Torus.freq_neg]

/-- **Sobolev bound from a dominated even energy**: if `|y(m)|² ≤ (F(m) + F(-m))/2` with
`Σ ⟨ξ_m⟩^{2s} F(m) < ∞`, then `y ∈ Hˢ(𝕋³)` and `Σ ⟨ξ_m⟩^{2s} |y(m)|² ≤ Σ ⟨ξ_m⟩^{2s} F(m)`. -/
theorem sobSum_le_of_even_bound {k : ℕ} {s : ℝ} (y : Seq 3 k) {F : (Fin 3 → ℤ) → ℝ}
    (hF : Summable fun m => weight s m * F m)
    (hy : ∀ m, ‖cf y m‖ ^ 2 ≤ (F m + F (-m)) / 2) :
    MemSob s y ∧ sobSum s y ≤ ∑' m, weight s m * F m := by
  have hFn : Summable fun m => weight s (-m) * F (-m) :=
    hF.comp_injective neg_injective
  have hG : Summable fun m => (weight s m * F m + weight s (-m) * F (-m)) / 2 :=
    (hF.add hFn).div_const 2
  have hle : ∀ m, weight s m * ‖cf y m‖ ^ 2 ≤
      (weight s m * F m + weight s (-m) * F (-m)) / 2 := fun m => by
    have h := mul_le_mul_of_nonneg_left (hy m) (weight_nonneg s m)
    rw [weight_neg] at *
    linarith
  have hsum : Summable fun m => weight s m * ‖cf y m‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (weight_nonneg s m) (sq_nonneg _)) hle hG
  refine ⟨hsum, (Summable.tsum_le_tsum hle hsum hG).trans (le_of_eq ?_)⟩
  have hneg := (Equiv.neg (Fin 3 → ℤ)).tsum_eq (fun m => weight s m * F m)
  simp only [Equiv.neg_apply] at hneg
  rw [tsum_div_const, Summable.tsum_add hF hFn, hneg]
  ring

theorem norm_cjForm {k : ℕ} (v : Form ℂ (Fin 3) k) : ‖cjForm v‖ = ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  simp [cjForm_apply]

theorem norm_half_add_sq_le {k : ℕ} (v w : Form ℂ (Fin 3) k) :
    ‖(1 / 2 : ℂ) • (v + cjForm w)‖ ^ 2 ≤ (‖v‖ ^ 2 + ‖w‖ ^ 2) / 2 := by
  rw [norm_smul]
  have h1 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h1]
  have h2 := norm_add_le v (cjForm w)
  rw [norm_cjForm] at h2
  have := norm_nonneg (v + cjForm w)
  nlinarith [sq_nonneg (‖v‖ - ‖w‖), norm_nonneg v, norm_nonneg w]

theorem norm_rowF_sq_le (M : Mat) (a : Fin 3) : ‖rowF M a‖ ^ 2 ≤ ‖M‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp only [rowF_apply]
  rw [Equiv.sum_comp e1.symm (fun b => ‖M (a, b)‖ ^ 2)]
  exact Finset.single_le_sum (f := fun a' => ∑ b, ‖M (a', b)‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ a)

theorem norm_rowF2_sq_le (M : Mat) (a : Fin 3) : ‖rowF2 M a‖ ^ 2 ≤ ‖M‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  have hs : ∀ i, ‖(sg2 i : ℂ)‖ = 1 := fun i => by unfold sg2; split_ifs <;> simp
  simp only [rowF2_apply, norm_mul, hs, one_mul]
  rw [Equiv.sum_comp e2.symm (fun b => ‖M (a, b)‖ ^ 2)]
  exact Finset.single_le_sum (f := fun a' => ∑ b, ‖M (a', b)‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ a)

/-- The magnetic slot of a state. -/
abbrev stB (x : PiLp 2 MirrorBGG.SpaceQ) : MQ := (WithLp.ofLp (stW2 x)).2

theorem norm_coeff_E_sq_le (x : PiLp 2 MirrorBGG.SpaceQ) (m : Fin 3 → ℤ) :
    ‖(MirrorBGG.J₁ (stE x) : (Fin 3 → ℤ) → Mat) m‖ ^ 2 ≤ fibreEnergy (extState x) m := by
  rw [fibreEnergy_eq]
  have h0 := sq_nonneg ‖tc0 (extState x) m‖
  have h2 := sq_nonneg ‖tc2 (extState x) m‖
  have e : tc1 (extState x) m = (MirrorBGG.J₁ (stE x) : (Fin 3 → ℤ) → Mat) m := rfl
  rw [e]
  linarith

theorem norm_coeff_B_sq_le (x : PiLp 2 MirrorBGG.SpaceQ) (m : Fin 3 → ℤ) :
    ‖(extF (c := Mirror.cB) Mirror.cB_sq (stB x) : (Fin 3 → ℤ) → Mat) m‖ ^ 2 ≤
      fibreEnergy (extState x) m := by
  rw [fibreEnergy_eq]
  have h0 := sq_nonneg ‖tc0 (extState x) m‖
  have h1 := sq_nonneg ‖tc1 (extState x) m‖
  have e : tc2 (extState x) m =
      WithLp.toLp 2 ((extF (c := Mirror.cPV) Mirror.cPV_sq (WithLp.ofLp (stW2 x)).1 :
        (Fin 3 → ℤ) → Vec) m, (extF (c := Mirror.cB) Mirror.cB_sq (stB x) :
          (Fin 3 → ℤ) → Mat) m) :=
    MirrorExt.pairLp_coeff _ _ (stW2 x) m
  have h3 := norm_sq_VM (tc2 (extState x) m)
  rw [e, WithLp.ofLp_toLp] at h3
  rw [e, h3]
  nlinarith [sq_nonneg ‖(extF (c := Mirror.cPV) Mirror.cPV_sq (WithLp.ofLp (stW2 x)).1 :
    (Fin 3 → ℤ) → Vec) m‖]

/-- **The rows of `Re E` lie in the parity Sobolev classes of the bottom row**: for a state with
`J x ∈ Hˢ(𝕋³)`, the row `a` of `Re E` (a `1`-form on `Q`) lies in `Hˢ_{a}(Q; Λ¹)` with
`‖(Re E)_a‖²_{s,{a}} ≤ ‖x‖²_s`. -/
theorem rowRe_sobolevPar {s : ℝ} {x : PiLp 2 MirrorBGG.SpaceQ} (hx : MemSobState s x)
    (a : Fin 3) :
    rowRe (stE x) a ∈ sobolevPar {a} 1 s ∧
      parNorm {a} 1 s (rowRe (stE x) a) ^ 2 ≤ sobState s x := by
  have h := sobSum_le_of_even_bound (s := s) (JfJ {a} 1 (rowRe (stE x) a))
    (F := fibreEnergy (extState x)) hx fun m => by
      change ‖(JfJ {a} 1 (rowRe (stE x) a) : (Fin 3 → ℤ) → Form ℂ (Fin 3) 1) m‖ ^ 2 ≤ _
      rw [coeff_JfJ_rowRe]
      refine (norm_half_add_sq_le _ _).trans ?_
      have h1 := (norm_rowF_sq_le _ a).trans (norm_coeff_E_sq_le x m)
      have h2 := (norm_rowF_sq_le _ a).trans (norm_coeff_E_sq_le x (-m))
      linarith
  refine ⟨h.1, ?_⟩
  rw [parNorm_sq, sobState]
  have h8 : ((2 : ℝ) ^ 3)⁻¹ = 8⁻¹ := by norm_num
  rw [h8]
  exact mul_le_mul_of_nonneg_left h.2 (by norm_num)

/-- **The rows of `⋆ Re B` lie in the parity Sobolev classes of the bottom `2`-forms**, with
`‖(⋆ Re B)_a‖²_{s,{a}} ≤ ‖x‖²_s`. -/
theorem rowRe2_sobolevPar {s : ℝ} {x : PiLp 2 MirrorBGG.SpaceQ} (hx : MemSobState s x)
    (a : Fin 3) :
    rowRe2 (stB x) a ∈ sobolevPar {a} 2 s ∧
      parNorm {a} 2 s (rowRe2 (stB x) a) ^ 2 ≤ sobState s x := by
  have h := sobSum_le_of_even_bound (s := s) (JfJ {a} 2 (rowRe2 (stB x) a))
    (F := fibreEnergy (extState x)) hx fun m => by
      change ‖(JfJ {a} 2 (rowRe2 (stB x) a) : (Fin 3 → ℤ) → Form ℂ (Fin 3) 2) m‖ ^ 2 ≤ _
      rw [coeff_JfJ_rowRe2]
      refine (norm_half_add_sq_le _ _).trans ?_
      have h1 := (norm_rowF2_sq_le _ a).trans (norm_coeff_B_sq_le x m)
      have h2 := (norm_rowF2_sq_le _ a).trans (norm_coeff_B_sq_le x (-m))
      linarith
  refine ⟨h.1, ?_⟩
  rw [parNorm_sq, sobState]
  have h8 : ((2 : ℝ) ^ 3)⁻¹ = 8⁻¹ := by norm_num
  rw [h8]
  exact mul_le_mul_of_nonneg_left h.2 (by norm_num)

/-! ### The domains of the powers of `L` -/

/-- `x ∈ D(Lᵏ)`. -/
def MemDomainPow : ℕ → PiLp 2 MirrorBGG.SpaceQ → Prop
  | 0, _ => True
  | k + 1, x => ∃ h : x ∈ MirrorBGG.complexQ.wave.domain,
      MemDomainPow k (MirrorBGG.complexQ.wave ⟨x, h⟩)

open Classical in
/-- `Lᵏ x` (`0` off `D(Lᵏ)`). -/
def wavePow : ℕ → PiLp 2 MirrorBGG.SpaceQ → PiLp 2 MirrorBGG.SpaceQ
  | 0, x => x
  | k + 1, x => if h : x ∈ MirrorBGG.complexQ.wave.domain then
      wavePow k (MirrorBGG.complexQ.wave ⟨x, h⟩) else 0

theorem wavePow_zero (x : PiLp 2 MirrorBGG.SpaceQ) : wavePow 0 x = x := rfl

theorem wavePow_succ {k : ℕ} {x : PiLp 2 MirrorBGG.SpaceQ}
    (h : x ∈ MirrorBGG.complexQ.wave.domain) :
    wavePow (k + 1) x = wavePow k (MirrorBGG.complexQ.wave ⟨x, h⟩) := by
  simp [wavePow, h]

theorem memDomainPow_succ {k : ℕ} {x : PiLp 2 MirrorBGG.SpaceQ} :
    MemDomainPow (k + 1) x ↔ ∃ h : x ∈ MirrorBGG.complexQ.wave.domain,
      MemDomainPow k (MirrorBGG.complexQ.wave ⟨x, h⟩) := Iff.rfl

/-- **The wave group maps `D(L)` into `D(L)` and commutes with `L`, for every `t ∈ ℝ`**
(generalizes `waveGroupQ_graph`, `t ≥ 0`). -/
theorem waveGroupQ_mem_domain_wave (t : ℝ) {x : PiLp 2 MirrorBGG.SpaceQ}
    (hx : x ∈ MirrorBGG.complexQ.wave.domain) :
    ∃ h : MirrorBGG.complexQ.waveGroup.S t x ∈ MirrorBGG.complexQ.wave.domain,
      MirrorBGG.complexQ.wave ⟨_, h⟩ =
        MirrorBGG.complexQ.waveGroup.S t (MirrorBGG.complexQ.wave ⟨x, hx⟩) := by
  have hg := HilbertComplex.generator_waveGroup MirrorBGG.complexQ
  have hx' : x ∈ MirrorBGG.complexQ.waveGroup.generator.domain := by rw [hg]; exact hx
  have h1 := MirrorBGG.complexQ.waveGroup.mapsTo_domain ⟨x, hx'⟩ t
  have h2 := MirrorBGG.complexQ.waveGroup.generator_apply_S ⟨x, hx'⟩ t
  have h1' : MirrorBGG.complexQ.waveGroup.S t x ∈ MirrorBGG.complexQ.wave.domain := by
    rw [← hg]; exact h1
  refine ⟨h1', ?_⟩
  calc MirrorBGG.complexQ.wave ⟨_, h1'⟩ =
        MirrorBGG.complexQ.waveGroup.generator ⟨_, h1⟩ :=
          (LinearPMap.apply_eq_of_eq hg ⟨_, h1⟩ ⟨_, h1'⟩ rfl).symm
    _ = MirrorBGG.complexQ.waveGroup.S t (MirrorBGG.complexQ.waveGroup.generator ⟨x, hx'⟩) := h2
    _ = _ := by rw [LinearPMap.apply_eq_of_eq hg ⟨x, hx'⟩ ⟨x, hx⟩ rfl]

/-- **The wave group preserves `D(Lᵏ)` and commutes with `Lʲ`, `j ≤ k`, for every `t ∈ ℝ`.** -/
theorem waveGroupQ_mem_domain_pow (k : ℕ) (t : ℝ) {x : PiLp 2 MirrorBGG.SpaceQ}
    (hx : MemDomainPow k x) :
    MemDomainPow k (MirrorBGG.complexQ.waveGroup.S t x) ∧
      ∀ j ≤ k, wavePow j (MirrorBGG.complexQ.waveGroup.S t x) =
        MirrorBGG.complexQ.waveGroup.S t (wavePow j x) := by
  induction k generalizing x with
  | zero =>
    refine ⟨trivial, fun j hj => ?_⟩
    obtain rfl : j = 0 := Nat.le_zero.1 hj
    rfl
  | succ k ih =>
    obtain ⟨h, hk⟩ := memDomainPow_succ.1 hx
    obtain ⟨h', e⟩ := waveGroupQ_mem_domain_wave t h
    have ih' := ih hk
    refine ⟨memDomainPow_succ.2 ⟨h', by rw [e]; exact ih'.1⟩, fun j hj => ?_⟩
    rcases j with _ | j
    · rfl
    · rw [wavePow_succ h', wavePow_succ h, e]
      exact ih'.2 j (by omega)

/-- **`‖Lʲ e^{tL} x‖ = ‖Lʲ x‖` for `x ∈ D(Lᵏ)`, `j ≤ k`, `t ∈ ℝ`.** -/
theorem norm_pow_waveGroupQ_eq {k : ℕ} (t : ℝ) {x : PiLp 2 MirrorBGG.SpaceQ}
    (hx : MemDomainPow k x) {j : ℕ} (hj : j ≤ k) :
    ‖wavePow j (MirrorBGG.complexQ.waveGroup.S t x)‖ = ‖wavePow j x‖ := by
  rw [(waveGroupQ_mem_domain_pow k t hx).2 j hj, MirrorBGG.complexQ.isIsometric_waveGroup]

/-! ### `D(Lᵏ)` on TSD states is the Sobolev class `Hᵏ` of the mirror extension -/

theorem wavePow_mem_tsd {k : ℕ} {x : PiLp 2 MirrorBGG.SpaceQ} (hx : MemDomainPow k x)
    (hxt : x ∈ totalSub MirrorBGG.tsdQ) : wavePow k x ∈ totalSub MirrorBGG.tsdQ := by
  induction k generalizing x with
  | zero => exact hxt
  | succ k ih =>
    obtain ⟨h, hk⟩ := memDomainPow_succ.1 hx
    rw [wavePow_succ h]
    exact ih hk (waveQ_mem_tsd ⟨x, h⟩ hxt)

/-- **`Lᵏ` on TSD states, one frequency at a time**:
`Σᵢ |(J Lᵏ x)ᵢ^(m)|² = |ξ_m|^{2k} Σᵢ |(J x)ᵢ^(m)|²`. -/
theorem fibreEnergy_wavePow_of_tsd {k : ℕ} {x : PiLp 2 MirrorBGG.SpaceQ}
    (hx : MemDomainPow k x) (hxt : x ∈ totalSub MirrorBGG.tsdQ) (m : Fin 3 → ℤ) :
    fibreEnergy (extState (wavePow k x)) m =
      (‖Fourier.Torus.freq m‖ ^ 2) ^ k * fibreEnergy (extState x) m := by
  induction k generalizing x with
  | zero => rw [wavePow_zero, pow_zero, one_mul]
  | succ k ih =>
    obtain ⟨h, hk⟩ := memDomainPow_succ.1 hx
    rw [wavePow_succ h, ih hk (waveQ_mem_tsd ⟨x, h⟩ hxt), fibreEnergy_waveQ_of_tsd ⟨x, h⟩ hxt,
      pow_succ]
    ring

/-- **`‖Lᵏ x‖² = 8⁻¹ Σ_m |ξ_m|^{2k} Σᵢ |(J x)ᵢ^(m)|²` on TSD states of `D(Lᵏ)`** (the term
`m = 0` vanishes for `k ≥ 1`): TSD fields are symmetric and divergence-free row-wise, and
`|ξ × x| = |ξ| |x|` when `ξ · x = 0`. -/
theorem norm_wavePow_sq_of_tsd {k : ℕ} {x : PiLp 2 MirrorBGG.SpaceQ} (hx : MemDomainPow k x)
    (hxt : x ∈ totalSub MirrorBGG.tsdQ) :
    ‖wavePow k x‖ ^ 2 =
      8⁻¹ * ∑' m, (‖Fourier.Torus.freq m‖ ^ 2) ^ k * fibreEnergy (extState x) m := by
  rw [norm_sq_eq_tsum_extState]
  simp_rw [fibreEnergy_wavePow_of_tsd hx hxt]

theorem weight_natCast (k : ℕ) (m : Fin 3 → ℤ) :
    weight (k : ℝ) m = (1 + ‖Fourier.Torus.freq m‖ ^ 2) ^ k := by
  rw [weight, Real.rpow_natCast]

theorem one_add_pow_le {a : ℝ} (ha : 0 ≤ a) (k : ℕ) : (1 + a) ^ k ≤ 2 ^ k * (1 + a ^ k) := by
  rcases le_total 1 a with h | h
  · have h1 : 1 + a ≤ 2 * a := by linarith
    calc (1 + a) ^ k ≤ (2 * a) ^ k := pow_le_pow_left₀ (by linarith) h1 k
      _ = 2 ^ k * a ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * (1 + a ^ k) := by nlinarith [pow_pos (two_pos (α := ℝ)) k]
  · have h1 : 1 + a ≤ 2 := by linarith
    calc (1 + a) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by linarith) h1 k
      _ ≤ 2 ^ k * (1 + a ^ k) := by
        nlinarith [pow_pos (two_pos (α := ℝ)) k, pow_nonneg ha k]

theorem le_one_add_pow {a : ℝ} (ha : 0 ≤ a) (k : ℕ) : a ^ k ≤ (1 + a) ^ k :=
  pow_le_pow_left₀ ha (by linarith) k

theorem memSobState_of_memDomainPow {k : ℕ} {x : PiLp 2 MirrorBGG.SpaceQ}
    (hx : MemDomainPow k x) (hxt : x ∈ totalSub MirrorBGG.tsdQ) : MemSobState k x := by
  have hS : Summable fun m => 2 ^ k * (fibreEnergy (extState x) m +
      fibreEnergy (extState (wavePow k x)) m) :=
    ((summable_fibreEnergy _).add (summable_fibreEnergy _)).mul_left _
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg (weight_nonneg _ m)
    (fibreEnergy_nonneg _ m)) (fun m => ?_) hS
  rw [weight_natCast, fibreEnergy_wavePow_of_tsd hx hxt]
  have h := one_add_pow_le (sq_nonneg ‖Fourier.Torus.freq m‖) k
  have hf := fibreEnergy_nonneg (extState x) m
  nlinarith [mul_le_mul_of_nonneg_right h hf]

open Feec.Models.Cube.Sobolev (MemSob) in
/-- A TSD state with `Σ_m |ξ_m|² Σᵢ |(J x)ᵢ^(m)|² < ∞` lies in `D(L)`. -/
theorem mem_wave_domain_of_summable {x : PiLp 2 MirrorBGG.SpaceQ}
    (hxt : x ∈ totalSub MirrorBGG.tsdQ)
    (h : Summable fun m => ‖Fourier.Torus.freq m‖ ^ 2 * fibreEnergy (extState x) m) :
    x ∈ MirrorBGG.complexQ.wave.domain := by
  refine (HilbertComplex.mem_wave_domain_compress_iff Mirror.eight_pos MirrorBGG.inner_J
    MirrorBGG.reducingSubcomplex_range).2 ?_
  have hX := extState_mem_constraint hxt
  have hE : ∀ n, tc1 (extState x) n ∈ tsd (Fourier.Torus.freq n) := fun n =>
    Measure.ae_count_iff.1 (Operator.mem_fibreSub.1 (hX 1)) n
  have hB := fun n => Models.Torus.BGG.mem_constraint_two_iff.1 (hX 2) n
  refine Models.Torus.BGG.mem_wave_domain_of (Models.Torus.BGG.mem_constraint_zero_iff.1 (hX 0))
    (hX 1) ?_ ?_
  · refine (Operator.mem_mulDomain_count_iff
      (fun n => bggFamily.m 1 2 (Fourier.Torus.freq n))).2 (memℓp_gen ?_)
    have hb : ∀ n, ‖bgg (Fourier.Torus.freq n) (tc1 (extState x) n)‖ ^ 2 ≤
        ‖Fourier.Torus.freq n‖ ^ 2 * fibreEnergy (extState x) n := fun n => by
      have haxial : Fourier.BGG.axialL (tc1 (extState x) n) = 0 :=
        (mem_tsdB.1 (Fourier.BGG.bgg_mem_tsdB (hE n))).1
      rw [norm_sq_VM]
      change ‖Fourier.BGG.axialL (tc1 (extState x) n)‖ ^ 2 +
        ‖curl (Fourier.Torus.freq n) (tc1 (extState x) n)‖ ^ 2 ≤ _
      rw [haxial, norm_zero, norm_curl_of_mem_tsd (hE n), fibreEnergy_eq]
      nlinarith [sq_nonneg ‖tc0 (extState x) n‖, sq_nonneg ‖tc2 (extState x) n‖,
        sq_nonneg ‖Fourier.Torus.freq n‖, mul_nonneg (sq_nonneg ‖Fourier.Torus.freq n‖)
          (sq_nonneg ‖tc0 (extState x) n‖), mul_nonneg (sq_nonneg ‖Fourier.Torus.freq n‖)
          (sq_nonneg ‖tc2 (extState x) n‖)]
    have hs : Summable fun n => ‖bgg (Fourier.Torus.freq n) (tc1 (extState x) n)‖ ^ 2 :=
      Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hb h
    refine hs.congr fun n => ?_
    rw [ENNReal.toReal_ofNat, Real.rpow_two]
    rfl
  · rw [show (Models.Torus.BGG.complex.d 1 2)† = Operator.mulOp Measure.count fun n =>
        ContinuousLinearMap.adjoint (bggFamily.m 1 2 (Fourier.Torus.freq n)) from
      (Fourier.Torus.symbolComplex bggFamily).adjoint_d 1 2]
    refine (Operator.mem_mulDomain_count_iff _).2 (memℓp_gen ?_)
    have hb : ∀ n, ‖ContinuousLinearMap.adjoint (bgg (Fourier.Torus.freq n))
        (tc2 (extState x) n)‖ ^ 2 ≤ ‖Fourier.Torus.freq n‖ ^ 2 * fibreEnergy (extState x) n :=
      fun n => by
        have hw : tc2 (extState x) n =
            WithLp.toLp 2 ((0 : Vec), (WithLp.ofLp (tc2 (extState x) n)).2) := by
          rw [← (hB n).1]; rfl
        have hadj : ContinuousLinearMap.adjoint (bgg (Fourier.Torus.freq n))
            (tc2 (extState x) n) =
            curl (Fourier.Torus.freq n) (WithLp.ofLp (tc2 (extState x) n)).2 := by
          conv_lhs => rw [hw]
          exact adjoint_bgg_inr _ _
        have h3 : ‖tc2 (extState x) n‖ ^ 2 = ‖(WithLp.ofLp (tc2 (extState x) n)).2‖ ^ 2 := by
          rw [norm_sq_VM, (hB n).1, norm_zero]; ring
        rw [hadj, norm_curl_of_mem_tsd (hB n).2, fibreEnergy_eq, mul_pow, ← h3]
        nlinarith [sq_nonneg ‖tc0 (extState x) n‖, sq_nonneg ‖tc1 (extState x) n‖,
          mul_nonneg (sq_nonneg ‖Fourier.Torus.freq n‖) (sq_nonneg ‖tc0 (extState x) n‖),
          mul_nonneg (sq_nonneg ‖Fourier.Torus.freq n‖) (sq_nonneg ‖tc1 (extState x) n‖)]
    have hs : Summable fun n => ‖ContinuousLinearMap.adjoint (bgg (Fourier.Torus.freq n))
        (tc2 (extState x) n)‖ ^ 2 :=
      Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hb h
    refine hs.congr fun n => ?_
    rw [ENNReal.toReal_ofNat, Real.rpow_two]
    rfl

theorem memDomainPow_of_memSobState {k : ℕ} {x : PiLp 2 MirrorBGG.SpaceQ}
    (hxt : x ∈ totalSub MirrorBGG.tsdQ) (hs : MemSobState k x) : MemDomainPow k x := by
  induction k generalizing x with
  | zero => trivial
  | succ k ih =>
    have hsum : Summable fun m => ‖Fourier.Torus.freq m‖ ^ 2 * fibreEnergy (extState x) m := by
      refine Summable.of_nonneg_of_le (fun m => mul_nonneg (sq_nonneg _)
        (fibreEnergy_nonneg _ m)) (fun m => ?_) hs
      rw [weight_natCast]
      have ha := sq_nonneg ‖Fourier.Torus.freq m‖
      have h1 : ‖Fourier.Torus.freq m‖ ^ 2 ≤ (1 + ‖Fourier.Torus.freq m‖ ^ 2) ^ (k + 1) :=
        (le_self_pow₀ (by linarith) (Nat.succ_ne_zero k)).trans' (by linarith)
      exact mul_le_mul_of_nonneg_right h1 (fibreEnergy_nonneg _ m)
    have h := mem_wave_domain_of_summable hxt hsum
    refine memDomainPow_succ.2 ⟨h, ih (waveQ_mem_tsd ⟨x, h⟩ hxt) ?_⟩
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (weight_nonneg _ m)
      (fibreEnergy_nonneg _ m)) (fun m => ?_) hs
    rw [weight_natCast, weight_natCast, fibreEnergy_waveQ_of_tsd ⟨x, h⟩ hxt]
    have ha := sq_nonneg ‖Fourier.Torus.freq m‖
    have hf := fibreEnergy_nonneg (extState x) m
    have hp := pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + ‖Fourier.Torus.freq m‖ ^ 2) k
    rw [pow_succ]
    have : ‖Fourier.Torus.freq m‖ ^ 2 ≤ 1 + ‖Fourier.Torus.freq m‖ ^ 2 := by linarith
    calc (1 + ‖Fourier.Torus.freq m‖ ^ 2) ^ k * (‖Fourier.Torus.freq m‖ ^ 2 *
          fibreEnergy (extState x) m) ≤
        (1 + ‖Fourier.Torus.freq m‖ ^ 2) ^ k * ((1 + ‖Fourier.Torus.freq m‖ ^ 2) *
          fibreEnergy (extState x) m) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this hf) hp
      _ = _ := by ring

/-- **On TSD states, `D(Lᵏ)` is the Sobolev class `Hᵏ` of the mirror extension**:
`x ∈ D(Lᵏ)` iff `Σ_m ⟨ξ_m⟩^{2k} Σᵢ |(J x)ᵢ^(m)|² < ∞`. The mirror extension `J` of a field on
`Q` is its parity extension in the mirror classes (`E` tensor parities, `B` pseudo-tensor
parities), so this is the parity Sobolev class of `Q`: the rows of `Re E` and `⋆Re B` lie in
`Hᵏ_{a}(Q)` (`rowRe_sobolevPar`, `rowRe2_sobolevPar`). The compatibility conditions of `D(Lᵏ)`
at `∂Q` are exactly the mirror parities. -/
theorem mem_domain_pow_iff_sobolev_of_tsd {k : ℕ} {x : PiLp 2 MirrorBGG.SpaceQ}
    (hxt : x ∈ totalSub MirrorBGG.tsdQ) : MemDomainPow k x ↔ MemSobState k x :=
  ⟨fun h => memSobState_of_memDomainPow h hxt, memDomainPow_of_memSobState hxt⟩

/-- **Equivalent norms**: `‖Lᵏ x‖² ≤ ‖x‖²_k ≤ 2ᵏ (‖x‖² + ‖Lᵏ x‖²)` on TSD states of `D(Lᵏ)`. -/
theorem norm_wavePow_sq_le_sobState {k : ℕ} {x : PiLp 2 MirrorBGG.SpaceQ}
    (hx : MemDomainPow k x) (hxt : x ∈ totalSub MirrorBGG.tsdQ) :
    ‖wavePow k x‖ ^ 2 ≤ sobState k x ∧
      sobState k x ≤ 2 ^ k * (‖x‖ ^ 2 + ‖wavePow k x‖ ^ 2) := by
  have hS := memSobState_of_memDomainPow hx hxt
  have hP : Summable fun m => (‖Fourier.Torus.freq m‖ ^ 2) ^ k * fibreEnergy (extState x) m :=
    (summable_fibreEnergy (extState (wavePow k x))).congr fun m =>
      fibreEnergy_wavePow_of_tsd hx hxt m
  rw [norm_wavePow_sq_of_tsd hx hxt, norm_sq_eq_tsum_extState, sobState]
  constructor
  · refine mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum (fun m => ?_) hP hS) (by norm_num)
    rw [weight_natCast]
    exact mul_le_mul_of_nonneg_right (le_one_add_pow (sq_nonneg _) k) (fibreEnergy_nonneg _ m)
  · have hQ : Summable fun m => 2 ^ k * (fibreEnergy (extState x) m +
        (‖Fourier.Torus.freq m‖ ^ 2) ^ k * fibreEnergy (extState x) m) :=
      ((summable_fibreEnergy _).add hP).mul_left _
    have hle := Summable.tsum_le_tsum (fun m => ?_) hS hQ
    · rw [tsum_mul_left, Summable.tsum_add (summable_fibreEnergy _) hP] at hle
      have h8 : (0 : ℝ) ≤ 8⁻¹ := by norm_num
      nlinarith [mul_le_mul_of_nonneg_left hle h8]
    · rw [weight_natCast]
      have h := one_add_pow_le (sq_nonneg ‖Fourier.Torus.freq m‖) k
      have hf := fibreEnergy_nonneg (extState x) m
      nlinarith [mul_le_mul_of_nonneg_right h hf]

/-- **`D(Lᵏ)` TSD states have `Hᵏ` rows in the mirror parity classes.** -/
theorem rows_sobolevPar_of_memDomainPow {k : ℕ} {x : PiLp 2 MirrorBGG.SpaceQ}
    (hx : MemDomainPow k x) (hxt : x ∈ totalSub MirrorBGG.tsdQ) (a : Fin 3) :
    rowRe (stE x) a ∈ sobolevPar {a} 1 k ∧ rowRe2 (stB x) a ∈ sobolevPar {a} 2 k :=
  ⟨(rowRe_sobolevPar (memSobState_of_memDomainPow hx hxt) a).1,
    (rowRe2_sobolevPar (memSobState_of_memDomainPow hx hxt) a).1⟩

/-! ### Closeness of the TSD states to their parity-smoothed projections -/

open Feec.Models.Cube.WeakSymmetry (W0 W1 W2 Wv)
open Feec.Models.Cube.FEM (cubeDomain cubeDomain_eq_Q ParitySmoothingEstimates toQ castL2F
  sobConstPar sobConstPar_nonneg infDist_polyPartial_le_sobolevPar norm_sub_π_le_infDist)
open Feec.Models.Cube.FEM (meshSize meshSize_pos)
open Feec.FiniteElement (PolySeq)

theorem castL2F_eq_castL2 {Ω Ω' : Set (Fin 3 → ℝ)} (h : Ω = Ω') (ι : Type) [Fintype ι]
    (x : Feec.Domain.L2F ℝ Ω ι) : castL2F h ι x = castL2 h ι x := by
  subst h; rfl

theorem toQ_cQ_symm {k : ℕ} (r : Feec.Domain.L2F ℝ (Geometry.Q (Fin 3)) (Feec.Domain.formIdx 3 k)) :
    toQ (n := 3) k ((cQ _).symm r) = r := by
  rw [toQ, castL2F_eq_castL2]
  exact LinearIsometryEquiv.apply_symm_apply _ _

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C)

/-- The constant of the parity-smoothed projections on `Hˢ` data, `0 ≤ s ≤ 1`. -/
def mirrorSobConst (C : ℝ) : ℝ :=
  (1 + 2 * C) * (sobConstPar 3 PolySeq.lagrangeP2 1 + sobConstPar 3 PolySeq.lagrangeP2 2)

theorem mirrorSobConst_nonneg (hC : 0 ≤ 2 * C) : 0 ≤ mirrorSobConst C := by
  have := sobConstPar_nonneg (n := 3) PolySeq.lagrangeP2 1
  have := sobConstPar_nonneg (n := 3) PolySeq.lagrangeP2 2
  unfold mirrorSobConst; positivity

include hB in
/-- **The `Hˢ` approximation of the parity-smoothed projections of the bottom row**:
`‖y − π y‖ ≤ (1 + 2C) dist(y, V_{h,Γ_{a}}) ≤ (1 + 2C) C_s h^s ‖y‖_{s,{a}}`. -/
theorem norm_sub_projB_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (N : ℕ) (a : Fin 3) {k : ℕ}
    (hk : k = 1 ∨ k = 2)
    {r : Feec.Domain.L2F ℝ (Geometry.Q (Fin 3)) (Feec.Domain.formIdx 3 k)}
    (hr : r ∈ sobolevPar {a} k s) {Λ : ℝ} (hΛ : parNorm {a} k s r ≤ Λ) :
    ‖(cQ _).symm r - ((hB a).proj N).π k ((cQ _).symm r)‖ ≤
      mirrorSobConst C * meshSize N ^ s * Λ := by
  have hC := (hB a).two_mul_nonneg
  have h1 := norm_sub_π_le_infDist ((hB a).proj N) hC ((hB a).norm_proj_le N k) ((cQ _).symm r)
  have hr' : toQ (n := 3) k ((cQ _).symm r) ∈ sobolevPar {a} k s := by rwa [toQ_cQ_symm]
  have h2 := infDist_polyPartial_le_sobolevPar PolySeq.lagrangeP2 {a} k hs0 hs1 N _ hr'
  rw [toQ_cQ_symm] at h2
  have hΛ0 : 0 ≤ Λ := (Sobolev.parNorm_nonneg {a} k s r).trans hΛ
  have hh : 0 ≤ meshSize N ^ s := Real.rpow_nonneg (meshSize_pos N).le s
  have hsk : sobConstPar 3 PolySeq.lagrangeP2 k ≤
      sobConstPar 3 PolySeq.lagrangeP2 1 + sobConstPar 3 PolySeq.lagrangeP2 2 := by
    have := sobConstPar_nonneg (n := 3) PolySeq.lagrangeP2 1
    have := sobConstPar_nonneg (n := 3) PolySeq.lagrangeP2 2
    rcases hk with rfl | rfl <;> linarith
  refine h1.trans ?_
  calc (1 + 2 * C) * Metric.infDist ((cQ _).symm r) ((Feec.Models.Cube.FEM.polyPartial 3
        PolySeq.lagrangeP2 N {a}).V k) ≤
      (1 + 2 * C) * (sobConstPar 3 PolySeq.lagrangeP2 k * meshSize N ^ s * Λ) :=
        mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left hΛ
          (mul_nonneg (sobConstPar_nonneg _ _) hh))) (by linarith)
    _ ≤ (1 + 2 * C) * ((sobConstPar 3 PolySeq.lagrangeP2 1 + sobConstPar 3 PolySeq.lagrangeP2 2) *
        meshSize N ^ s * Λ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsk hh) hΛ0
    _ = mirrorSobConst C * meshSize N ^ s * Λ := by unfold mirrorSobConst; ring

/-- **TSD-type mirror states with `Hˢ` rows are `O(hˢ)`-close to their projections**: for a forms
state `(0, 0, u, 0, ρ)` with `u` the real rows of `E` (`bIncl1 u = rowsW1L E`), `d u` the rows of
`⋆ Re B'`, `ρ` the rows of `⋆ Re B` and `S¹ u = 0`, whose rows lie in the parity classes `Hˢ_{a}`
with norms `≤ Λ`. -/
theorem mirrorClose_of_sobolev {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (N : ℕ) {u : BU1}
    {E B B' : MQ} (hu : bIncl1 u = rowsW1L E) (hdu : bD1 u = rowsW2L B') (hSu : mS1 u = 0)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hE : ∀ a, rowRe E a ∈ sobolevPar {a} 1 s ∧ parNorm {a} 1 s (rowRe E a) ≤ Λ)
    (hB2 : ∀ a, rowRe2 B a ∈ sobolevPar {a} 2 s ∧ parNorm {a} 2 s (rowRe2 B a) ≤ Λ)
    (hB2' : ∀ a, rowRe2 B' a ∈ sobolevPar {a} 2 s ∧ parNorm {a} 2 s (rowRe2 B' a) ≤ Λ) :
    MirrorClose hT hB N (mirrorSobConst C * meshSize N ^ s * Λ) 0 0 u 0 (rowsW2L B) := by
  have hδ : 0 ≤ mirrorSobConst C * meshSize N ^ s * Λ :=
    mul_nonneg (mul_nonneg (mirrorSobConst_nonneg hT.two_mul_nonneg)
      (Real.rpow_nonneg (meshSize_pos N).le s)) hΛ0
  refine ⟨?_, fun a => ?_, fun a => ?_, fun a => ?_, ?_, fun a => ?_, ?_⟩
  · change ‖(0 : W0) - (hT.proj N).π 0 (0 : W0)‖ ≤ _
    rw [map_zero, sub_zero, norm_zero]; exact hδ
  · change ‖BD0 a (0 : (BD0 a).domain) - ((hB a).proj N).π 1 (BD0 a (0 : (BD0 a).domain))‖ ≤ _
    rw [LinearPMap.map_zero, map_zero, sub_zero, norm_zero]; exact hδ
  · have e : ((u a : (BD1 a).domain) : W1) = (cQ _).symm (rowRe E a) := by
      rw [← bIncl1_apply, hu, rowsW1L_apply]
    rw [e]
    exact norm_sub_projB_le hB hs0 hs1 N a (Or.inl rfl) (hE a).1 (hE a).2
  · have e : BD1 a (u a) = (cQ _).symm (rowRe2 B' a) := by
      rw [← bD1_apply, hdu, rowsW2L_apply]
    rw [e]
    exact norm_sub_projB_le hB hs0 hs1 N a (Or.inr rfl) (hB2' a).1 (hB2' a).2
  · change ‖(0 : W2) - (hT.proj N).π 2 (0 : W2)‖ ≤ _
    rw [map_zero, sub_zero, norm_zero]; exact hδ
  · rw [rowsW2L_apply]
    exact norm_sub_projB_le hB hs0 hs1 N a (Or.inr rfl) (hB2 a).1 (hB2 a).2
  · rw [hSu, map_zero, sub_zero, norm_zero]; exact hδ

/-! ### The TSD solution: closeness along the trajectory -/

theorem rows_sobolev {s : ℝ} {x : PiLp 2 MirrorBGG.SpaceQ} (hx : MemSobState s x) {Λ : ℝ}
    (hΛ : √(sobState s x) ≤ Λ) :
    (∀ a, rowRe (stE x) a ∈ sobolevPar {a} 1 s ∧ parNorm {a} 1 s (rowRe (stE x) a) ≤ Λ) ∧
      ∀ a, rowRe2 (stB x) a ∈ sobolevPar {a} 2 s ∧ parNorm {a} 2 s (rowRe2 (stB x) a) ≤ Λ :=
  ⟨fun a => ⟨(rowRe_sobolevPar hx a).1,
      ((le_abs_self _).trans (Real.abs_le_sqrt (rowRe_sobolevPar hx a).2)).trans hΛ⟩,
    fun a => ⟨(rowRe2_sobolevPar hx a).1,
      ((le_abs_self _).trans (Real.abs_le_sqrt (rowRe2_sobolevPar hx a).2)).trans hΛ⟩⟩

theorem rows_sobolev_waveGroup {s : ℝ} (t : ℝ) {x : PiLp 2 MirrorBGG.SpaceQ}
    (hx : MemSobState s x) {Λ : ℝ} (hΛ : √(sobState s x) ≤ Λ) :
    (∀ a, rowRe (stE (MirrorBGG.complexQ.waveGroup.S t x)) a ∈ sobolevPar {a} 1 s ∧
      parNorm {a} 1 s (rowRe (stE (MirrorBGG.complexQ.waveGroup.S t x)) a) ≤ Λ) ∧
    ∀ a, rowRe2 (stB (MirrorBGG.complexQ.waveGroup.S t x)) a ∈ sobolevPar {a} 2 s ∧
      parNorm {a} 2 s (rowRe2 (stB (MirrorBGG.complexQ.waveGroup.S t x)) a) ≤ Λ :=
  rows_sobolev ((memSobState_waveGroupQ_iff s t x).2 hx) (by rwa [sobState_waveGroupQ])

namespace TSDDatum

variable (D : TSDDatum)

include hB in
/-- **The forms state of the TSD solution is `O(hˢ)`-close to its projections**, uniformly in
time, when `J U₀`, `J L U₀ ∈ Hˢ(𝕋³)`. -/
theorem mirrorClose_state {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (N : ℕ)
    (h0 : MemSobState s D.U₀) (h1 : MemSobState s D.LU₀) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ₀ : √(sobState s D.U₀) ≤ Λ) (hΛ₁ : √(sobState s D.LU₀) ≤ Λ) {T t : ℝ}
    (ht : t ∈ Icc 0 T) :
    MirrorClose hT hB N (mirrorSobConst C * meshSize N ^ s * Λ) ((D.exactWave T).σ t)
      ((D.exactWave T).φ t) ((D.exactWave T).u t) ((D.exactWave T).M t)
      ((D.exactWave T).ρ t) :=
  mirrorClose_of_sobolev hT hB hs0 hs1 N (D.bIncl1_u ht.1) (D.bD1_u ht.1) (D.mS1_u ht.1) hΛ0
    (rows_sobolev_waveGroup t h0 hΛ₀).1 (rows_sobolev_waveGroup t h0 hΛ₀).2
    (rows_sobolev_waveGroup t h1 hΛ₁).2

include hB in
/-- **The time derivative of the forms state is `O(hˢ)`-close to its projections**, uniformly in
time, when `J L U₀`, `J L² U₀ ∈ Hˢ(𝕋³)`. -/
theorem mirrorClose_deriv {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (N : ℕ)
    (h1 : MemSobState s D.LU₀) (h2 : MemSobState s D.LLU₀) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ₁ : √(sobState s D.LU₀) ≤ Λ) (hΛ₂ : √(sobState s D.LLU₀) ≤ Λ) {T t : ℝ}
    (ht : t ∈ Icc 0 T) :
    MirrorClose hT hB N (mirrorSobConst C * meshSize N ^ s * Λ) ((D.exactWave T).σ' t)
      ((D.exactWave T).φ' t) ((D.exactWave T).u' t) ((D.exactWave T).M' t)
      ((D.exactWave T).ρ' t) :=
  mirrorClose_of_sobolev hT hB hs0 hs1 N (D.bIncl1_u' ht.1) (D.bD1_u' ht.1) (D.mS1_u' ht.1) hΛ0
    (rows_sobolev_waveGroup t h1 hΛ₁).1 (rows_sobolev_waveGroup t h1 hΛ₁).2
    (rows_sobolev_waveGroup t h2 hΛ₂).2

end TSDDatum

/-! ### Rates of the mirror scheme (6.5) for Sobolev data -/

/-- The Sobolev size `‖U₀‖_s + ‖L U₀‖_s + ‖L² U₀‖_s` of a TSD datum. -/
def TSDDatum.sobSize (D : TSDDatum) (s : ℝ) : ℝ :=
  √(sobState s D.U₀) + √(sobState s D.LU₀) + √(sobState s D.LLU₀)

theorem TSDDatum.sobSize_nonneg (D : TSDDatum) (s : ℝ) : 0 ≤ D.sobSize s := by
  unfold TSDDatum.sobSize; positivity

namespace TSDDatum

variable (D : TSDDatum)

theorem ell_S0_le_zero (T : ℝ) (N : ℕ) : ∀ t ∈ Icc 0 T, ∀ ψ ∈ (mirrorFEM hT hB N).Vt0h,
    |(D.exactWave T).ℓ t ((mirrorBGGSegment.S0 - (mirrorFEM hT hB N).S0h) ψ)| ≤
      0 * √(Feec.BGG.graphSq mirrorBGGSegment.dt0 ψ) := fun _ _ _ _ => by
  rw [zero_mul]
  exact (abs_eq_zero.2 (LinearMap.zero_apply _)).le

theorem ell'_S0_le_zero (T : ℝ) (N : ℕ) : ∀ t ∈ Icc 0 T, ∀ ψ ∈ (mirrorFEM hT hB N).Vt0h,
    |(D.exactWave T).ℓ' t ((mirrorBGGSegment.S0 - (mirrorFEM hT hB N).S0h) ψ)| ≤
      0 * √(Feec.BGG.graphSq mirrorBGGSegment.dt0 ψ) := fun _ _ _ _ => by
  rw [zero_mul]
  exact (abs_eq_zero.2 (LinearMap.zero_apply _)).le

theorem inner_M_S1_le_zero (T : ℝ) (N : ℕ) : ∀ t ∈ Icc 0 T, ∀ v ∈ (mirrorFEM hT hB N).Vt1h,
    |⟪(D.exactWave T).M t, (mirrorBGGSegment.S1 - (mirrorFEM hT hB N).S1h) v⟫_ℝ| ≤
      0 * √((mirrorFEM hT hB N).gnSq v) := fun _ _ _ _ => by
  rw [zero_mul]
  exact (abs_eq_zero.2 (inner_zero_left _)).le

theorem inner_M'_S1_le_zero (T : ℝ) (N : ℕ) : ∀ t ∈ Icc 0 T, ∀ v ∈ (mirrorFEM hT hB N).Vt1h,
    |⟪(D.exactWave T).M' t, (mirrorBGGSegment.S1 - (mirrorFEM hT hB N).S1h) v⟫_ℝ| ≤
      0 * √((mirrorFEM hT hB N).gnSq v) := fun _ _ _ _ => by
  rw [zero_mul]
  exact (abs_eq_zero.2 (inner_zero_left _)).le

theorem strangData_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (N : ℕ)
    (h0 : MemSobState s D.U₀) (h1 : MemSobState s D.LU₀) (h2 : MemSobState s D.LLU₀)
    (T : ℝ) : (∀ t ∈ Icc 0 T, (mirrorFEM hT hB N).strangData ((D.exactWave T).σ t)
      ((D.exactWave T).φ t) ((D.exactWave T).u t) ((D.exactWave T).M t) ((D.exactWave T).ρ t)
        0 0 ≤ (√(mirrorCloseConst C) * (mirrorSobConst C * meshSize N ^ s * D.sobSize s) * 1) ^ 2) ∧
    ∀ t ∈ Icc 0 T, (mirrorFEM hT hB N).strangData ((D.exactWave T).σ' t)
      ((D.exactWave T).φ' t) ((D.exactWave T).u' t) ((D.exactWave T).M' t)
      ((D.exactWave T).ρ' t) 0 0 ≤
        (√(mirrorCloseConst C) * (mirrorSobConst C * meshSize N ^ s * D.sobSize s) * 1) ^ 2 := by
  have hmc := mirrorCloseConst_nonneg C
  have hΛ0 := D.sobSize_nonneg s
  have r0 := Real.sqrt_nonneg (sobState s D.U₀)
  have r1 := Real.sqrt_nonneg (sobState s D.LU₀)
  have r2 := Real.sqrt_nonneg (sobState s D.LLU₀)
  have hΛ₀ : √(sobState s D.U₀) ≤ D.sobSize s := by unfold TSDDatum.sobSize; linarith
  have hΛ₁ : √(sobState s D.LU₀) ≤ D.sobSize s := by unfold TSDDatum.sobSize; linarith
  have hΛ₂ : √(sobState s D.LLU₀) ≤ D.sobSize s := by unfold TSDDatum.sobSize; linarith
  have hdat : ∀ x δ : ℝ, x ≤ mirrorCloseConst C * δ ^ 2 + 0 ^ 2 + 0 ^ 2 →
      x ≤ (√(mirrorCloseConst C) * δ * 1) ^ 2 := fun x δ hx => by
    rw [mul_one, mul_pow, Real.sq_sqrt hmc]; simpa using hx
  exact ⟨fun t ht => hdat _ _ (mirrorFEM_strangData_le_of_close hT hB N
      (D.mirrorClose_state hT hB hs0 hs1 N h0 h1 hΛ0 hΛ₀ hΛ₁ ht) 0 0),
    fun t ht => hdat _ _ (mirrorFEM_strangData_le_of_close hT hB N
      (D.mirrorClose_deriv hT hB hs0 hs1 N h1 h2 hΛ0 hΛ₁ hΛ₂ ht) 0 0)⟩

end TSDDatum

/-- **`O(hˢ)` rate of the mirror scheme (6.5) for Sobolev TSD data, `0 ≤ s ≤ 1`**, with no
smoothness hypothesis on the solution: there is `K`, independent of `N`, `T`, `s` and the datum,
such that for every TSD datum `D` (`U₀ ∈ D(L²)` in the constraint) whose mirror extensions
`J U₀`, `J L U₀`, `J L² U₀` lie in `Hˢ(𝕋³)` (`MemSobState s`, the torus weights of the mirror
extension; on TSD states of `D(Lᵏ)` this is `D(Lᵏ)` for `s = k`,
`mem_domain_pow_iff_sobolev_of_tsd`), and every strong solution `U` from `U₀`, the scheme (6.5)
without source has a solution from the
elliptic projection of the initial forms state with
`(‖σₕ‖² + ‖Re E − uₕ‖² + ‖Mₕ‖² + ‖Re B − ρₕ‖²)^{1/2}(t)`
`≤ K (‖U₀‖_s + ‖LU₀‖_s + ‖L²U₀‖_s) (1 + t) h_Nˢ`
on `[0,T]`. The rows of `Re E(t)`, `⋆Re B(t)`, `⋆Re B'(t)`, `Re E'(t)`, `⋆Re B''(t)` lie in the
parity classes `Hˢ_{a}` with the norms of the data (`rowRe_sobolevPar`, `rowRe2_sobolevPar`, the
wave group preserving the torus weights, `sobState_waveGroupQ`), so they are `O(hˢ)`-close to their
parity-smoothed projections (`mirrorClose_of_sobolev`, from `infDist_polyPartial_le_sobolevPar`);
the multipliers `ℓ ≡ 0` and `M ≡ 0` of TSD data make the consistency constants `K₀ = K₁ = 0`.
See [QuennevilleBelair2015], Ch. 6, §6.3, (6.5), and §4.10; [AFW2010], §5.4. -/
theorem mirror_waveFEM_rate_sobolev :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) (D : TSDDatum) {s : ℝ}, 0 ≤ s → s ≤ 1 →
      MemSobState s D.U₀ → MemSobState s D.LU₀ → MemSobState s D.LLU₀ →
      ∀ {T : ℝ}, 0 < T → ∀ {U : ℝ → PiLp 2 MirrorBGG.SpaceQ}, U 0 = D.U₀ →
        Evolution.IsStrongSolution MirrorBGG.complexQ.wave (Icc 0 T) 0 U →
      ∃ sh : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T (mirrorSource hT hB N 0),
        (sh.σ 0, sh.u 0, sh.M 0, sh.ρ 0) =
          (Feec.BGG.ellipticProjection (mirrorWave hT hB N) (mirrorWave_dt0_injective hT hB N)
            (Feec.BGG.exists_sub_eq_of_surjective (mirrorWave_S0_surjective hT hB N))
            (Feec.BGG.ellipticRhs ((mirrorFEM hT hB N).ellipticDataH ((D.exactWave T).σ 0)
              ((D.exactWave T).φ 0) ((D.exactWave T).u 0) ((D.exactWave T).M 0)
              ((D.exactWave T).ρ 0) ((D.exactWave T).ℓ 0)) 0)).1.1 ∧
        ∀ t ∈ Icc 0 T, √(‖(sh.σ t : TU0)‖ ^ 2 +
          ‖rowsW1L (stEL (U t)) - bIncl1 (sh.u t : BU1)‖ ^ 2 + ‖(sh.M t : W2)‖ ^ 2 +
          ‖rowsW2L (stBL (U t)) - (sh.ρ t : Wv W2)‖ ^ 2) ≤
            K * D.sobSize s * (1 + t) * meshSize N ^ s := by
  have hC := hT.two_mul_nonneg
  have hA0 := mirrorSobConst_nonneg hC
  have hmc := mirrorCloseConst_nonneg C
  have ex1 : ∃ Ks : ℝ, Ks = √(2 * (Feec.BGG.Discrete.strangConst (2 * Real.pi)⁻¹ + 1)) :=
    ⟨_, rfl⟩
  obtain ⟨Ks, hKs⟩ := ex1
  have hKs0 : 0 ≤ Ks := by rw [hKs]; exact Real.sqrt_nonneg _
  refine ⟨2 * Ks * √(mirrorCloseConst C) * mirrorSobConst C, by positivity, ?_⟩
  intro N D s hs0 hs1 h0 h1 h2 T hT0 U hU0 hU
  have hΛ0 := D.sobSize_nonneg s
  have hδ0 : 0 ≤ mirrorSobConst C * meshSize N ^ s * D.sobSize s :=
    mul_nonneg (mul_nonneg hA0 (Real.rpow_nonneg (meshSize_pos N).le s)) hΛ0
  have hEq := D.eqOn_of_isStrongSolution hU0 hU
  have hf : ContinuousOn (0 : ℝ → Wv W1) (Icc 0 T) := continuousOn_const
  have hd := D.strangData_le hT hB hs0 hs1 N h0 h1 h2 T
  have hrate := (D.exactWave T).exists_discreteSolution_rate_harm (mirrorFEM hT hB N)
    mirror_harmonicStability (mirrorFEM_compatible hT hB N) (K0 := 0) (K1 := 0)
    (c := √(mirrorCloseConst C) * (mirrorSobConst C * meshSize N ^ s * D.sobSize s)) (h := 1)
    (mirrorWave_S0_surjective hT hB N) hT0
    (continuousOn_mirrorSource hT hB N hf) (fun t _ v => (inner_mirrorSource hT hB N 0 t v).symm)
    (D.ell_S0_le_zero hT hB T N) (D.ell'_S0_le_zero hT hB T N)
    (D.inner_M_S1_le_zero hT hB T N) (D.inner_M'_S1_le_zero hT hB T N)
    hd.1 hd.2
  obtain ⟨sh, hsh0, hb⟩ := hrate
  refine ⟨sh, hsh0, fun t ht => ?_⟩
  refine (sqrt_four_congr (hb t ht) (norm_zero_sub' _) (D.norm_exactWave_u_sub hEq ht _)
    (norm_zero_sub' _) (D.norm_exactWave_ρ_sub hEq ht _)).trans (le_of_eq ?_)
  rw [← hKs, abs_of_nonneg (by positivity), abs_one]
  ring



theorem sqrt_sq_add_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a ^ 2 + b ^ 2) ≤ a + b :=
  Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩

/-- **The data class `D(L³)`**: a TSD datum with `L² U₀ ∈ D(L)` has `J U₀, J L U₀, J L² U₀ ∈ H¹`,
with `‖U₀‖_1 + ‖LU₀‖_1 + ‖L²U₀‖_1 ≤ 2 (‖U₀‖ + ‖LU₀‖ + ‖L²U₀‖ + ‖L³U₀‖)`. -/
theorem TSDDatum.memSobState_one (D : TSDDatum)
    (h3 : D.LLU₀ ∈ MirrorBGG.complexQ.wave.domain) :
    MemSobState 1 D.U₀ ∧ MemSobState 1 D.LU₀ ∧ MemSobState 1 D.LLU₀ ∧
      D.sobSize 1 ≤ 2 * (‖D.U₀‖ + ‖D.LU₀‖ + ‖D.LLU₀‖ +
        ‖MirrorBGG.complexQ.wave ⟨D.LLU₀, h3⟩‖) := by
  have t2 : D.LLU₀ ∈ totalSub MirrorBGG.tsdQ := waveQ_mem_tsd ⟨D.LU₀, D.mem₂⟩ D.LU₀_tsd
  refine ⟨memSobState_one_of_tsd ⟨D.U₀, D.mem⟩ D.tsd,
    memSobState_one_of_tsd ⟨D.LU₀, D.mem₂⟩ D.LU₀_tsd, memSobState_one_of_tsd ⟨D.LLU₀, h3⟩ t2, ?_⟩
  have e0 := sobState_one_of_tsd ⟨D.U₀, D.mem⟩ D.tsd
  have e1 := sobState_one_of_tsd ⟨D.LU₀, D.mem₂⟩ D.LU₀_tsd
  have e2 := sobState_one_of_tsd ⟨D.LLU₀, h3⟩ t2
  unfold TSDDatum.sobSize
  rw [e0, e1, e2]
  have q0 := sqrt_sq_add_sq_le (norm_nonneg D.U₀) (norm_nonneg D.LU₀)
  have q1 := sqrt_sq_add_sq_le (norm_nonneg D.LU₀) (norm_nonneg D.LLU₀)
  have q2 := sqrt_sq_add_sq_le (norm_nonneg D.LLU₀)
    (norm_nonneg (MirrorBGG.complexQ.wave ⟨D.LLU₀, h3⟩))
  change √(‖D.U₀‖ ^ 2 + ‖D.LU₀‖ ^ 2) + √(‖D.LU₀‖ ^ 2 + ‖D.LLU₀‖ ^ 2) +
    √(‖D.LLU₀‖ ^ 2 + ‖MirrorBGG.complexQ.wave ⟨D.LLU₀, h3⟩‖ ^ 2) ≤ _
  have := norm_nonneg D.U₀
  have := norm_nonneg (MirrorBGG.complexQ.wave ⟨D.LLU₀, h3⟩)
  linarith

/-- **`O(h)` rate of the mirror scheme (6.5) for every TSD datum of `D(L³)`, with no smoothness
hypothesis**: there is `K`, independent of `N`, `T` and the datum, such that for every TSD datum
`D` with `L² U₀ ∈ D(L)` and every strong solution `U` from `U₀`, the scheme (6.5) without source
has a solution from the elliptic projection (6.4) of the initial forms state with
`(‖σₕ‖² + ‖Re E − uₕ‖² + ‖Mₕ‖² + ‖Re B − ρₕ‖²)^{1/2}(t)`
`≤ K (‖U₀‖ + ‖LU₀‖ + ‖L²U₀‖ + ‖L³U₀‖)(1 + t) h_N`
on `[0,T]`. This is the conclusion of `mirror_waveFEM_rate` with its hypothesis that the forms
states of the solution are `C²` up to `∂Q` (`IsSmoothStateMirror`) replaced by the explicit
condition `U₀ ∈ D(L³)` on the datum. On TSD states of `D(L)` the graph norm of `L` is the `H¹`
norm of the mirror extension (`sobState_one_of_tsd`: `|L(ξ) v| = |ξ| |v|` on the TSD fibres), so
`U(t)`, `U'(t)`, `U''(t)` have `H¹` rows in the parity classes of `MirrorClose`, with norms
conserved in time (`mirror_waveFEM_rate_sobolev`, `s = 1`). `D(L³)` is what the proof uses: the
Strang data contain `d u'`, the rows of `B''`, which must be `H¹`.
See [QuennevilleBelair2015], Ch. 6, §6.3, (6.5), and §4.10; [AFW2010], §5.4. -/
theorem rate_bound_aux {K S Λ t h : ℝ} (hK : 0 ≤ K) (hS : S ≤ 2 * Λ) (ht : 0 ≤ t)
    (hh : 0 ≤ h) : K * S * (1 + t) * h ^ (1 : ℝ) ≤ 2 * K * Λ * (1 + t) * h := by
  rw [Real.rpow_one]
  have h1 : K * S ≤ K * (2 * Λ) := mul_le_mul_of_nonneg_left hS hK
  have h2 : 0 ≤ 1 + t := by linarith
  calc K * S * (1 + t) * h ≤ K * (2 * Λ) * (1 + t) * h :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 h2) hh
    _ = 2 * K * Λ * (1 + t) * h := by ring

theorem mirror_waveFEM_rate_of_mem_domain :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) (D : TSDDatum) (h3 : D.LLU₀ ∈ MirrorBGG.complexQ.wave.domain)
      {T : ℝ}, 0 < T → ∀ {U : ℝ → PiLp 2 MirrorBGG.SpaceQ}, U 0 = D.U₀ →
        Evolution.IsStrongSolution MirrorBGG.complexQ.wave (Icc 0 T) 0 U →
      ∃ sh : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T (mirrorSource hT hB N 0),
        (sh.σ 0, sh.u 0, sh.M 0, sh.ρ 0) =
          (Feec.BGG.ellipticProjection (mirrorWave hT hB N) (mirrorWave_dt0_injective hT hB N)
            (Feec.BGG.exists_sub_eq_of_surjective (mirrorWave_S0_surjective hT hB N))
            (Feec.BGG.ellipticRhs ((mirrorFEM hT hB N).ellipticDataH ((D.exactWave T).σ 0)
              ((D.exactWave T).φ 0) ((D.exactWave T).u 0) ((D.exactWave T).M 0)
              ((D.exactWave T).ρ 0) ((D.exactWave T).ℓ 0)) 0)).1.1 ∧
        ∀ t ∈ Icc 0 T, √(‖(sh.σ t : TU0)‖ ^ 2 +
          ‖rowsW1L (stEL (U t)) - bIncl1 (sh.u t : BU1)‖ ^ 2 + ‖(sh.M t : W2)‖ ^ 2 +
          ‖rowsW2L (stBL (U t)) - (sh.ρ t : Wv W2)‖ ^ 2) ≤
            K * (‖D.U₀‖ + ‖D.LU₀‖ + ‖D.LLU₀‖ + ‖MirrorBGG.complexQ.wave ⟨D.LLU₀, h3⟩‖) *
              (1 + t) * meshSize N := by
  have hR := mirror_waveFEM_rate_sobolev hT hB
  have hK0 := hR.choose_spec.1
  refine ⟨2 * hR.choose, mul_nonneg zero_le_two hK0, ?_⟩
  intro N D h3 T hT0 U hU0 hU
  have hm := TSDDatum.memSobState_one D h3
  have hb := hR.choose_spec.2 N D zero_le_one le_rfl hm.1 hm.2.1 hm.2.2.1 hT0 hU0 hU
  exact ⟨hb.choose, hb.choose_spec.1, fun t ht => (hb.choose_spec.2 t ht).trans
    (rate_bound_aux hK0 hm.2.2.2 ht.1 (meshSize_pos N).le)⟩

theorem memSobState_mono {s t : ℝ} (hst : s ≤ t) {x : PiLp 2 MirrorBGG.SpaceQ}
    (hx : MemSobState t x) : MemSobState s x :=
  Summable.of_nonneg_of_le (fun m => mul_nonneg (weight_nonneg s m) (fibreEnergy_nonneg _ m))
    (fun m => mul_le_mul_of_nonneg_right (Sobolev.weight_mono hst m) (fibreEnergy_nonneg _ m)) hx

/-! ### Non-vacuity -/

/-- **The cos datum `E₀ = 2 cos(2π x₃) diag(1, -1, 0)` of `mirror_waveFEM_nonvacuous` lies in
`D(L³)`**: its mirror extension has finitely many Fourier modes, which `L` preserves on the
torus (`torusBGG_wave_finite`). -/
theorem cosDatum_LLU₀_mem : cosDatum.LLU₀ ∈ MirrorBGG.complexQ.wave.domain := by
  have e : extState cosDatum.LU₀ = Models.Torus.BGG.complex.wave
      ⟨MirrorBGG.cosState, MirrorBGG.cosState_mem_domain⟩ := by
    rw [TSDDatum.LU₀, extState_wave]
    exact LinearPMap.apply_congr' _ _ MirrorBGG.cosState_mem_domain MirrorBGG.totalJ_cosStateQ
  have hfin : ∀ i, ∀ n ∉ ({Mirror.k0, -Mirror.k0} : Finset (Fin 3 → ℤ)),
      (((extState cosDatum.LU₀) i : Models.Torus.BGG.Space i) : (Fin 3 → ℤ) → _) n = 0 := by
    rw [e]; exact torusBGG_wave_finite _ _ cosState_finite
  refine (HilbertComplex.mem_wave_domain_compress_iff Mirror.eight_pos MirrorBGG.inner_J
    MirrorBGG.reducingSubcomplex_range).2 ?_
  have e2 : extState cosDatum.LLU₀ = Models.Torus.BGG.complex.wave
      ⟨extState cosDatum.LU₀, extState_mem_wave_domain cosDatum.mem₂⟩ :=
    extState_wave ⟨cosDatum.LU₀, cosDatum.mem₂⟩
  change extState cosDatum.LLU₀ ∈ _
  rw [e2]
  exact torusBGG_wave_mem_of_finite _ _ hfin

/-- **Non-vacuity of `mirror_waveFEM_rate_of_mem_domain` and `mirror_waveFEM_rate_sobolev`**: the
cos datum is a non-stationary TSD datum with `L² U₀ ∈ D(L)`, its mirror extensions
`J U₀`, `J L U₀`, `J L² U₀` lie in `Hˢ(𝕋³)` for every `s ≤ 1`, and its forms state is not zero. -/
theorem mirror_waveFEM_rate_of_mem_domain_nonvacuous :
    cosDatum.LLU₀ ∈ MirrorBGG.complexQ.wave.domain ∧
      cosDatum.U₀ ∉ MirrorBGG.complexQ.waveGroup.stationary ∧
      (∀ s ≤ 1, MemSobState s cosDatum.U₀ ∧ MemSobState s cosDatum.LU₀ ∧
        MemSobState s cosDatum.LLU₀) ∧ ∀ T, (cosDatum.exactWave T).u 0 ≠ 0 := by
  have h := cosDatum.memSobState_one cosDatum_LLU₀_mem
  exact ⟨cosDatum_LLU₀_mem, cosDatum_not_stationary, fun s hs =>
    ⟨memSobState_mono hs h.1, memSobState_mono hs h.2.1, memSobState_mono hs h.2.2.1⟩,
    cosDatum_u_ne⟩

end Feec.Models.Cube.MirrorWeakSymmetry
