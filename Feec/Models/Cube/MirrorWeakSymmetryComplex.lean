module

public import Feec.Models.Cube.WeakSymmetryComplex
public import Feec.Models.Cube.DeRhamPartialFEM
public import Feec.Models.Cube.ParitySmoother
public import Feec.HilbertComplex.BGG.Harmonic

/-!
# The continuous BGG data of the mirror scheme on the cube

The BGG data (4.16) of [QuennevilleBelair2015], §5.3, on `Q = (0, ½)³` with the **mirror
boundary conditions** of `Feec.Models.Cube.MirrorBGG` (the boundary conditions of the scheme
(6.5) in `Feec.Models.Cube.MirrorWeakSymmetryFEM`), in the `W`-normed domain model of
`Feec.BGG.Segment`:

* top row `HΛ⁰(Q) → HΛ¹(Q) → L²Λ²(Q)` (no boundary condition, `d_∅ = d_max`);
* bottom row `∏ₐ H_{a}Λ⁰(Q) → ∏ₐ H_{a}Λ¹(Q) → (L²Λ²(Q))³`, the component `a` with vanishing
  tangential traces on the faces normal to `eₐ` (`HΛ_{a}(Q)` of
  `Feec.Models.Cube.DeRhamPartialIdent`);
* `S⁰ = I`, `S¹ = 2 vskw` (`Feec.FiniteElement.wsL2`), with `d S⁰ = −S¹ d`
  (`wsL2_bIncl0_mem`: the bottom row lies in `HΛ⁰(Q)³` and `S` maps `D(d_max)³` into `D(d_max)`).

The rows carry harmonic forms: the constants on the top row in degree `0`
(`mirror_constantMode_continuous`; `ℌ⁰(HΛ(Q)) = ℝ`) and `ℝ dxₐ` in the component `a` of the bottom
row in degree `1` (`harmonic_one_part`, from `Feec.Models.Cube.FEM.harmonic_card_eq_span_part`).
So `Feec.BGG.Stability` fails (`mirror_not_stability`), and the data satisfy instead
**`Feec.BGG.HarmonicStability` modulo `𝔥 = {Σₐ cₐ dxₐ ⊗ eₐ}`** (`mirror_harmonicStability`):
Poincaré on the bottom `0`-forms, the Hodge decomposition `v = dψ + w + k` with `k ∈ 𝔥`,
`𝔥 ⊥ dṼ⁰`, and `S¹ 𝔥 = 0` (diagonal matrices are symmetric). The top row is exact at `HΛ¹`
(`mirror_exact1`).

**Regular potentials in the parity model.** For every class `J` and degree `k`, every
`u ∈ D(d_J)` has a coexact companion `w` with `d_J w = d_J u`, `‖w‖ ≤ (2π)⁻¹ ‖d_J u‖`, whose
coefficients `w_s` are `H¹` with vanishing traces on the faces normal to `J ∆ s` and
`Σ_s ‖∇w_s‖² = ‖d_J u‖²` (`Feec.Models.Cube.DeRhamIdent.exists_coexact_potential`): on the Fourier
side of the parity extension, `ŵ(m)` is the projection of `û(m)` onto `N(d_{ξ_m})ᗮ`
(`coexactProj`, equivariant under the reflections and the conjugation, so the parity class is
kept), and Gaffney's identity `|ξ|²|ŵ|² = |d_ξ û|²` holds frequency by frequency. Conversely,
forms with `H¹` coefficients of the classes `J ∆ s` lie in `D(d_J)` (`mem_dPart_of_coeff`). For
`J = ∅`, `k = 1` this is **`mirrorCurlPotential`**, the regularity hypothesis of Prop 5.3 for the
mirror data, proved with constant `C_R = 1`: `curl S⁰φ = curl u`, `‖∇φ‖ = ‖curl u‖`.

## Main definitions

* `TD0`, `TD1`, `BD0`, `BD1`, `TU0`, `TU1`, `BU0`, `BU1`; `tD0`, `tD1`, `bD0`, `bD1`, `mS0`,
  `mS1`; **`mirrorBGGSegment`**.
* `harmBot` (`𝔥`), `harmVec a` (`dxₐ ⊗ eₐ`), `oneU` (the constant mode).
* `Feec.Models.Cube.DeRhamIdent.coexactProj`, `coexactLp`.

## Main results

* **`mirror_harmonicStability`**, `mirror_not_stability`, `mirror_constantMode_continuous`,
  `mirror_exact1`, `harmBot_ne_bot`, `hodge_one_part`, `bpoincare0`.
* **`Feec.Models.Cube.DeRhamIdent.exists_coexact_potential`**,
  `Feec.Models.Cube.DeRhamIdent.mem_dPart_of_coeff`, `exists_coexact_potential_cube`,
  **`mirrorCurlPotential`**.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.1 (Prop 5.3), §5.3 ((4.16)), §6.3 ((6.5))
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3 (Hodge decomposition, harmonic forms), §4.3 (boundary conditions)
* [R. Hiptmair, *Finite elements in computational electromagnetism*][Hiptmair2002], Lemma 2.4
  (regular decomposition)
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.2 (extension by reflection)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ComplexConjugate
open Set MeasureTheory Filter Finset

@[expose] public noncomputable section

/-! ### Coexact parts in the parity model and regular potentials of `HΛ_J(Q)` -/

namespace Feec.Models.Cube.DeRhamIdent

open Feec.Models.Cube.Geometry
open Feec.Fourier.Exterior (Form koszulDeg)
open Feec.Fourier.Torus (freq)
open Feec.Domain (formIdx L2F L2)
open Feec.Models.Cube.ParitySmoother (zeroForm zeroForm_apply)

variable {n : ℕ}

section Fibre

variable (k : ℕ) (ξ : EuclideanSpace ℝ (Fin n))

/-- The kernel of the de Rham symbol `d_ξ : Λᵏ → Λᵏ⁺¹` at one frequency. -/
abbrev symKer : Submodule ℂ (Form ℂ (Fin n) k) :=
  LinearMap.ker ((Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) ξ :
    Form ℂ (Fin n) k →ₗ[ℂ] Form ℂ (Fin n) (k + 1))

/-- **The coexact projection at one frequency**: the orthogonal projection of `Λᵏ` onto
`N(d_ξ)ᗮ`. -/
def coexactProj : Form ℂ (Fin n) k →L[ℂ] Form ℂ (Fin n) k := (symKer k ξ)ᗮ.starProjection

variable {k ξ}

theorem coexactProj_mem (v : Form ℂ (Fin n) k) : coexactProj k ξ v ∈ (symKer k ξ)ᗮ :=
  Submodule.starProjection_apply_mem _ v

/-- `d_ξ` does not see the projection: `d_ξ (P v) = d_ξ v`. -/
theorem deRham_coexactProj (v : Form ℂ (Fin n) k) :
    (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) ξ (coexactProj k ξ v) =
      (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) ξ v := by
  have h := Submodule.sub_starProjection_mem_orthogonal (K := (symKer k ξ)ᗮ) v
  rw [Submodule.orthogonal_orthogonal, LinearMap.mem_ker, map_sub, sub_eq_zero] at h
  exact h.symm

theorem norm_coexactProj_le (v : Form ℂ (Fin n) k) : ‖coexactProj k ξ v‖ ≤ ‖v‖ :=
  Submodule.norm_starProjection_apply_le _ v

/-- **Gaffney's identity at one frequency**: `‖d_ξ v‖ = |ξ| ‖P v‖`. -/
theorem norm_deRham_eq (v : Form ℂ (Fin n) k) :
    ‖(Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) ξ v‖ = ‖ξ‖ * ‖coexactProj k ξ v‖ := by
  rw [← deRham_coexactProj]
  exact Feec.Fourier.Exterior.norm_deRham_of_mem_orthogonal (coexactProj_mem v)

theorem coexactProj_zero_freq (v : Form ℂ (Fin n) k) :
    coexactProj k (0 : EuclideanSpace ℝ (Fin n)) v = 0 := by
  have hK : ∀ w, w ∈ symKer k (0 : EuclideanSpace ℝ (Fin n)) := fun w => by
    simp [symKer, Feec.Fourier.Exterior.deRham_m_zero]
  exact inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal (hK _) (coexactProj_mem v))

end Fibre

section Symmetry

variable {k : ℕ} {ξ : EuclideanSpace ℝ (Fin n)}

open Feec.Models.Cube.DeRham (reflFreq reflFreq_apply reflForm reflForm_apply reflForm_reflForm
  inner_reflForm deRham_reflForm)

theorem reflFreq_reflFreq (j : Fin n) (ξ : EuclideanSpace ℝ (Fin n)) :
    reflFreq j (reflFreq j ξ) = ξ := by
  ext a; simp only [reflFreq_apply]; split_ifs <;> simp

theorem reflForm_mem_symKer (j : Fin n) {z : Form ℂ (Fin n) k} (hz : z ∈ symKer k ξ) :
    reflForm j k z ∈ symKer k (reflFreq j ξ) := by
  rw [LinearMap.mem_ker] at hz ⊢
  change (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) (reflFreq j ξ) (reflForm j k z) = 0
  rw [deRham_reflForm]
  rw [show (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) ξ z = 0 from hz, map_zero]

theorem reflForm_mem_orth (j : Fin n) {w : Form ℂ (Fin n) k} (hw : w ∈ (symKer k ξ)ᗮ) :
    reflForm j k w ∈ (symKer k (reflFreq j ξ))ᗮ := by
  intro z hz
  have hz' : reflForm j k z ∈ symKer k ξ := by
    have := reflForm_mem_symKer j hz
    rwa [reflFreq_reflFreq] at this
  rw [← inner_reflForm j k, reflForm_reflForm]
  exact hw _ hz'

/-- **The coexact projection is reflection-equivariant**:
`P_{R_j ξ} (R_j^* v) = R_j^* (P_ξ v)`. -/
theorem coexactProj_reflForm (j : Fin n) (v : Form ℂ (Fin n) k) :
    coexactProj k (reflFreq j ξ) (reflForm j k v) = reflForm j k (coexactProj k ξ v) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (reflForm_mem_orth j (coexactProj_mem v)) fun w hw => ?_
  have hw' : reflForm j k w ∈ (symKer k ξ)ᗮ := by
    have := reflForm_mem_orth j hw
    rwa [reflFreq_reflFreq] at this
  rw [← map_sub, ← inner_reflForm j k, reflForm_reflForm]
  have h := Submodule.sub_starProjection_mem_orthogonal (K := (symKer k ξ)ᗮ) v
  rw [Submodule.orthogonal_orthogonal] at h
  exact Submodule.inner_right_of_mem_orthogonal h hw'

/-- Entrywise complex conjugation of a form at one frequency. -/
def cjForm (v : Form ℂ (Fin n) k) : Form ℂ (Fin n) k := WithLp.toLp 2 fun t => conj (v t)

@[simp] theorem cjForm_apply (v : Form ℂ (Fin n) k) (t : {s : Finset (Fin n) // #s = k}) :
    cjForm v t = conj (v t) := rfl

theorem cjForm_sub (v w : Form ℂ (Fin n) k) : cjForm (v - w) = cjForm v - cjForm w := by
  ext t; simp

theorem inner_cjForm (v w : Form ℂ (Fin n) k) : ⟪cjForm v, cjForm w⟫_ℂ = conj ⟪v, w⟫_ℂ := by
  simp only [PiLp.inner_apply, cjForm_apply, map_sum, RCLike.inner_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp

theorem cjForm_cjForm (v : Form ℂ (Fin n) k) : cjForm (cjForm v) = v := by
  ext t; simp

/-- The de Rham symbol has real coefficients up to the factor `i`: `d_ξ (v̄) = -(d_ξ v)‾`. -/
theorem deRham_cjForm (v : Form ℂ (Fin n) k) :
    (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) ξ (cjForm v) =
      -cjForm ((Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) ξ v) := by
  ext u
  rw [Feec.Fourier.Exterior.deRham_m_succ]
  simp only [_root_.smul_apply, PiLp.smul_apply, PiLp.neg_apply, cjForm_apply, smul_eq_mul,
    Feec.Fourier.Exterior.koszulDeg_apply, Feec.Fourier.Exterior.res_apply,
    Feec.Fourier.Exterior.koszul_apply, map_mul, Complex.conj_I, map_sum]
  rw [neg_mul, neg_neg]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  have he : (Feec.Fourier.Exterior.ext k (cjForm v) : Feec.Fourier.Exterior.Lam ℂ (Fin n))
      (u.1.erase l) = conj ((Feec.Fourier.Exterior.ext k v : Feec.Fourier.Exterior.Lam ℂ (Fin n))
        (u.1.erase l)) := by
    by_cases h : #(u.1.erase l) = k
    · rw [Feec.Fourier.Exterior.ext_apply k _ h, Feec.Fourier.Exterior.ext_apply k _ h,
        cjForm_apply]
    · rw [Feec.Fourier.Exterior.ext_apply_of_ne k _ h, Feec.Fourier.Exterior.ext_apply_of_ne k _ h,
        map_zero]
  rw [he]
  have hs : conj (Feec.Fourier.Exterior.sgn l u.1 : ℂ) = Feec.Fourier.Exterior.sgn l u.1 := by
    simp [Feec.Fourier.Exterior.sgn]
  rw [hs]
  simp only [RCLike.conj_ofReal]

theorem cjForm_mem_symKer {z : Form ℂ (Fin n) k} (hz : z ∈ symKer k ξ) :
    cjForm z ∈ symKer k ξ := by
  rw [LinearMap.mem_ker] at hz ⊢
  change (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) ξ (cjForm z) = 0
  rw [deRham_cjForm, show (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) ξ z = 0 from hz]
  ext t; simp

theorem cjForm_mem_orth {w : Form ℂ (Fin n) k} (hw : w ∈ (symKer k ξ)ᗮ) :
    cjForm w ∈ (symKer k ξ)ᗮ := by
  intro z hz
  have h := hw _ (cjForm_mem_symKer hz)
  rw [← cjForm_cjForm z, inner_cjForm, h, map_zero]

/-- **The coexact projection commutes with conjugation.** -/
theorem coexactProj_cjForm (v : Form ℂ (Fin n) k) :
    coexactProj k ξ (cjForm v) = cjForm (coexactProj k ξ v) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (cjForm_mem_orth (coexactProj_mem v))
    fun w hw => ?_
  have h := Submodule.sub_starProjection_mem_orthogonal (K := (symKer k ξ)ᗮ) v
  rw [Submodule.orthogonal_orthogonal] at h
  rw [← cjForm_sub, ← cjForm_cjForm w, inner_cjForm,
    show ⟪v - coexactProj k ξ v, cjForm w⟫_ℂ = 0 from
      Submodule.inner_right_of_mem_orthogonal h (cjForm_mem_orth hw), map_zero]

theorem symKer_neg : symKer k (-ξ) = symKer k ξ := by
  ext z
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, Feec.Fourier.Exterior.deRham_m_succ,
    _root_.smul_apply]
  rw [show -ξ = (-1 : ℝ) • ξ from (neg_one_smul ℝ ξ).symm, Feec.Fourier.Exterior.koszulDeg_smul]
  simp

theorem coexactProj_neg (v : Form ℂ (Fin n) k) : coexactProj k (-ξ) v = coexactProj k ξ v := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_
  · rw [symKer_neg]; exact coexactProj_mem v
  · rw [symKer_neg] at hw
    have h := Submodule.sub_starProjection_mem_orthogonal (K := (symKer k ξ)ᗮ) v
    rw [Submodule.orthogonal_orthogonal] at h
    exact Submodule.inner_right_of_mem_orthogonal h hw

end Symmetry

section Sequence

open Feec.Models.Cube.DeRham (reflForm reflForm_apply freq_flipAt)

theorem norm_sq_count' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : Lp E 2 (Measure.count : Measure (Fin n → ℤ))) : ‖v‖ ^ 2 = ∑' q, ‖v q‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    ((lp.equivLpCount ℂ (Fin n → ℤ) E 2).symm v)
  rw [LinearIsometryEquiv.norm_map] at h
  simp only [lp.equivLpCount_symm_apply, ENNReal.toReal_ofNat] at h
  simpa only [Real.rpow_two] using h

theorem summable_norm_sq_count' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : Lp E 2 (Measure.count : Measure (Fin n → ℤ))) : Summable fun q => ‖v q‖ ^ 2 := by
  have h := (lp.memℓp_count (Fin n → ℤ) E 2 v).summable (by norm_num)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

theorem memLp_count_of_summable {E : Type*} [NormedAddCommGroup E] {f : (Fin n → ℤ) → E}
    (h : Summable fun q => ‖f q‖ ^ 2) : MemLp f 2 (Measure.count : Measure (Fin n → ℤ)) :=
  (memLp_count_iff (by norm_num)).2 (memℓp_gen (by simpa only [ENNReal.toReal_ofNat,
    Real.rpow_two] using h))

theorem norm_sq_JfJ (J : Finset (Fin n)) (k : ℕ) (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) :
    ‖JfJ J k u‖ ^ 2 = 2 ^ n * ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_JfJ, real_inner_self_eq_norm_sq]

variable {J : Finset (Fin n)} {k : ℕ}

/-- The coexact part of a coefficient sequence, frequency by frequency. -/
def coexactSeq (x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ))) :
    (Fin n → ℤ) → Form ℂ (Fin n) k := fun m => coexactProj k (freq m) (x m)

theorem memLp_coexactSeq (x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ))) :
    MemLp (coexactSeq x) 2 (Measure.count : Measure (Fin n → ℤ)) :=
  (memLp_count_iff (by norm_num)).2
    ((lp.memℓp_count (Fin n → ℤ) _ 2 x).mono' fun _ => norm_coexactProj_le _)

/-- **The coexact part** of `x ∈ ℓ²(ℤⁿ; Λᵏ)`. -/
def coexactLp (x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ))) :
    Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ)) :=
  (memLp_coexactSeq x).toLp _

theorem coexactLp_apply (x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ)))
    (m : Fin n → ℤ) :
    (coexactLp x : (Fin n → ℤ) → Form ℂ (Fin n) k) m = coexactProj k (freq m) (x m) := by
  rw [coexactLp, MemLp.coeFn_toLp_count]; rfl

/-- **The coexact part stays in the real mixed parity class `J`.** -/
theorem realParJ_coexactLp {x : Lp (Form ℂ (Fin n) k) 2 (Measure.count : Measure (Fin n → ℤ))}
    (hx : RealParJ J k x) : RealParJ J k (coexactLp x) := by
  refine ⟨fun m t => ?_, fun j m t => ?_⟩
  · rw [coexactLp_apply, coexactLp_apply, Feec.Fourier.Torus.freq_neg, coexactProj_neg]
    have : (x : (Fin n → ℤ) → Form ℂ (Fin n) k) (-m) = cjForm (x m) := by
      ext t; exact hx.1 m t
    rw [this, coexactProj_cjForm, cjForm_apply]
  · rw [coexactLp_apply, coexactLp_apply, freq_flipAt]
    have : (x : (Fin n → ℤ) → Form ℂ (Fin n) k) (DeRham.flipAt j m) =
        DeRham.mixedSign J j • reflForm j k (x m) := by
      ext t; rw [hx.2, PiLp.smul_apply, reflForm_apply, smul_eq_mul]; ring
    rw [this, map_smul, coexactProj_reflForm, PiLp.smul_apply, reflForm_apply, smul_eq_mul]
    ring

/-- The parity vector of the coefficient of `dx_s` in the class `J` is that of the `0`-form in
the class `J ∆ s`. -/
theorem pcJ_symmDiff_empty (J s : Finset (Fin n)) : pcJ (symmDiff J s) ∅ = pcJ J s := by
  funext j
  simp only [pcJ, DeRham.mixedSign, DeRham.reflSign, Finset.mem_symmDiff, Finset.notMem_empty,
    ite_false, mul_one]
  by_cases hJ : j ∈ J <;> by_cases hs : j ∈ s <;> simp [hJ, hs]

/-- **The coefficients of a component as a `0`-form**: the extension of `w_s` in the class
`J ∆ s` has the coefficients of the component `s` of the extension of `w` in the class `J`. -/
theorem coeff_JfJ_zeroForm (J : Finset (Fin n)) (k : ℕ) (w : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ)))
    (s : formIdx n (k : ℤ)) (m : Fin n → ℤ) (t₀ : {r : Finset (Fin n) // #r = 0}) :
    (JfJ (symmDiff J s.1) 0 (zeroForm (w s)) : (Fin n → ℤ) → Form ℂ (Fin n) 0) m t₀ =
      (JfJ J k w : (Fin n → ℤ) → Form ℂ (Fin n) k) m (idx k s) := by
  rw [coeff_JfJ, coeff_JfJ]
  have ht : t₀.1 = ∅ := Finset.card_eq_zero.1 t₀.2
  rw [ht, pcJ_symmDiff_empty, zeroForm_apply, Equiv.symm_apply_apply, idx_val]

/-- `‖d_ξ c‖ = |ξ| ‖c‖` on `0`-forms. -/
theorem norm_deRham_zero (ξ : EuclideanSpace ℝ (Fin n)) (c : Form ℂ (Fin n) 0) :
    ‖(Feec.Fourier.Exterior.deRham (Fin n)).m 0 (0 + 1) ξ c‖ = ‖ξ‖ * ‖c‖ := by
  rw [Feec.Fourier.Exterior.norm_deRham_apply]
  have h := Feec.Fourier.Exterior.norm_koszulDeg_sq_add 0 ξ c
  have h0 : Feec.Fourier.Exterior.contr ξ (Feec.Fourier.Exterior.ext 0 c) = 0 := by
    ext s; exact Feec.Fourier.Exterior.contr_ext_eq_zero ξ 0 c (by omega)
  rw [h0, norm_zero, zero_pow two_ne_zero, add_zero, ← mul_pow] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h

theorem norm_form_zero (c : Form ℂ (Fin n) 0) (t₀ : {r : Finset (Fin n) // #r = 0}) :
    ‖c‖ = ‖c t₀‖ := by
  have hsub : Subsingleton {r : Finset (Fin n) // #r = 0} :=
    ⟨fun a b => Subtype.ext ((Finset.card_eq_zero.1 a.2).trans (Finset.card_eq_zero.1 b.2).symm)⟩
  rw [EuclideanSpace.norm_eq, Fintype.sum_subsingleton _ t₀, Real.sqrt_sq (norm_nonneg _)]

/-- **A criterion for `D(d_J)` by summability**, with the norm of `d_J u` as an `ℓ²` sum. -/
theorem exists_mem_dPart_of_summable {u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))}
    (h : Summable fun m => ‖(Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) (freq m)
      ((JfJ J k u : (Fin n → ℤ) → Form ℂ (Fin n) k) m)‖ ^ 2) :
    ∃ hu : u ∈ (dPart (Q (Fin n)) J (k : ℤ)).domain,
      ‖dPart (Q (Fin n)) J (k : ℤ) ⟨u, hu⟩‖ ^ 2 = (2 ^ n)⁻¹ * ∑' m,
        ‖(Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) (freq m)
          ((JfJ J k u : (Fin n → ℤ) → Form ℂ (Fin n) k) m)‖ ^ 2 := by
  have hf := memLp_count_of_summable h
  obtain ⟨hu, hy⟩ := mem_dPart_of_JfJ (J := J) (k := k) (u := u) (y := hf.toLp _)
    fun m => by rw [MemLp.coeFn_toLp_count]
  refine ⟨hu, ?_⟩
  have e1 := norm_sq_JfJ J (k + 1) (dPart (Q (Fin n)) J (k : ℤ) ⟨u, hu⟩)
  rw [hy, norm_sq_count', MemLp.coeFn_toLp_count] at e1
  rw [e1]
  field_simp

end Sequence

section Potential

variable (J : Finset (Fin n)) (k : ℕ)

/-- **Regular potentials of `HΛ_J(Q)`** (all `J`, all degrees): every `u ∈ D(d_J)` has a
coexact companion `w ∈ D(d_J)` with `d_J w = d_J u`, `‖w‖ ≤ (2π)⁻¹ ‖d_J u‖`, whose coefficients
`w_s` are `H¹` with vanishing traces on the faces normal to `J ∆ s` (`w_s ∈ D(d_{J ∆ s})` as
`0`-forms, i.e. the parity extension of `w` has `H¹` coefficients) and
`Σ_s ‖∇ w_s‖² = ‖d_J u‖²`. The companion is the coexact part of `u` in the parity model, `ŵ(m)`
the projection of `û(m)` onto `N(d_{ξ_m})ᗮ`; the identity is **Gaffney's identity** on the torus,
`|ξ|² |ŵ(m)|² = |d_ξ û(m)|²` frequency by frequency (`norm_deRham_eq`; in degree `1` of `ℝ³`,
`|ξ|²|v|² = |ξ × v|² + |ξ · v|²`). See [AFW2010], §4.3, and [Brezis2011], §9.2 (reflection). -/
theorem exists_coexact_potential (u : (dPart (Q (Fin n)) J (k : ℤ)).domain) :
    ∃ w : (dPart (Q (Fin n)) J (k : ℤ)).domain,
      dPart (Q (Fin n)) J (k : ℤ) w = dPart (Q (Fin n)) J (k : ℤ) u ∧
      ‖(w : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ)))‖ ≤
        (2 * Real.pi)⁻¹ * ‖dPart (Q (Fin n)) J (k : ℤ) u‖ ∧
      ∃ g : formIdx n (k : ℤ) → L2F ℝ (Q (Fin n)) (formIdx n (((0 : ℕ) : ℤ) + 1)),
        (∀ s, (zeroForm ((w : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) s), g s) ∈
          (dPart (Q (Fin n)) (symmDiff J s.1) ((0 : ℕ) : ℤ)).graph) ∧
        ∑ s, ‖g s‖ ^ 2 = ‖dPart (Q (Fin n)) J (k : ℤ) u‖ ^ 2 := by
  set x := JfJ J k (u : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ))) with hxdef
  set du := dPart (Q (Fin n)) J (k : ℤ) u
  set Y := coexactLp x with hYdef
  have hY : RealParJ J k Y := realParJ_coexactLp (JfJ_realParJ J k _)
  set w₀ := Jinvf k Y
  have hJw : JfJ J k w₀ = Y := JfJ_Jinvf hY
  clear_value w₀
  have hdx : ∀ m, (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) (freq m)
      ((x : (Fin n → ℤ) → Form ℂ (Fin n) k) m) =
        (JfJ J (k + 1) du : (Fin n → ℤ) → Form ℂ (Fin n) (k + 1)) m :=
    fun m => coeff_d_dPart J k u m
  have hdY : ∀ m, (Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) (freq m)
      ((JfJ J k w₀ : (Fin n → ℤ) → Form ℂ (Fin n) k) m) =
        (JfJ J (k + 1) du : (Fin n → ℤ) → Form ℂ (Fin n) (k + 1)) m := fun m => by
    rw [hJw, coexactLp_apply, deRham_coexactProj, hdx]
  obtain ⟨hw₀, he⟩ := mem_dPart_of_JfJ (J := J) (k := k) (u := w₀) hdY
  set w : (dPart (Q (Fin n)) J (k : ℤ)).domain := ⟨w₀, hw₀⟩
  have hdw : dPart (Q (Fin n)) J (k : ℤ) w = du := injective_JfJ J (k + 1) he
  -- the pointwise bounds
  have hsd : Summable fun m => ‖(JfJ J (k + 1) du : (Fin n → ℤ) → Form ℂ (Fin n) (k + 1)) m‖ ^ 2 :=
    summable_norm_sq_count' _
  have hYm : ∀ m, ‖(Y : (Fin n → ℤ) → Form ℂ (Fin n) k) m‖ ≤ (2 * Real.pi)⁻¹ *
      ‖(JfJ J (k + 1) du : (Fin n → ℤ) → Form ℂ (Fin n) (k + 1)) m‖ := fun m => by
    rw [coexactLp_apply, ← hdx, norm_deRham_eq]
    by_cases hm : m = 0
    · subst hm
      rw [Feec.Fourier.Torus.freq_zero, coexactProj_zero_freq, norm_zero]
      positivity
    · have h2 := Feec.Fourier.Torus.two_pi_le_norm_freq hm
      rw [← mul_assoc]
      refine le_mul_of_one_le_left (norm_nonneg _) ?_
      rw [← div_eq_inv_mul, le_div_iff₀ (by positivity), one_mul]
      exact h2
  have hYeq : ∀ m, ‖(JfJ J (k + 1) du : (Fin n → ℤ) → Form ℂ (Fin n) (k + 1)) m‖ =
      ‖freq m‖ * ‖(Y : (Fin n → ℤ) → Form ℂ (Fin n) k) m‖ := fun m => by
    rw [← hdx, norm_deRham_eq, coexactLp_apply]
  refine ⟨w, hdw, ?_, ?_⟩
  · -- the `L²` bound
    have h1 := norm_sq_JfJ J k w₀
    rw [hJw, norm_sq_count'] at h1
    have h2 := norm_sq_JfJ J (k + 1) du
    rw [norm_sq_count'] at h2
    have hle : ∑' m, ‖(Y : (Fin n → ℤ) → Form ℂ (Fin n) k) m‖ ^ 2 ≤
        ((2 * Real.pi)⁻¹) ^ 2 *
          ∑' m, ‖(JfJ J (k + 1) du : (Fin n → ℤ) → Form ℂ (Fin n) (k + 1)) m‖ ^ 2 := by
      rw [← tsum_mul_left]
      refine (summable_norm_sq_count' Y).tsum_le_tsum (fun m => ?_) (hsd.mul_left _)
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hYm m) 2
    have hpos : (0 : ℝ) < 2 ^ n := by positivity
    have key : ‖w₀‖ ^ 2 ≤ ((2 * Real.pi)⁻¹ * ‖du‖) ^ 2 := by
      rw [mul_pow]
      have := hle
      rw [h1, h2] at this
      refine le_of_mul_le_mul_left ?_ hpos
      linarith
    exact (abs_le_of_sq_le_sq' key (by positivity)).2
  · -- the coefficients
    have hcoef : ∀ (s : formIdx n (k : ℤ)) m, ‖(JfJ (symmDiff J s.1) 0 (zeroForm (w₀ s)) :
        (Fin n → ℤ) → Form ℂ (Fin n) 0) m‖ = ‖(Y : (Fin n → ℤ) → Form ℂ (Fin n) k) m (idx k s)‖ :=
      fun s m => by
        rw [norm_form_zero _ ⟨∅, Finset.card_empty⟩, coeff_JfJ_zeroForm, hJw]
    have hsum_s : ∀ (s : formIdx n (k : ℤ)), Summable fun m =>
        ‖(Feec.Fourier.Exterior.deRham (Fin n)).m 0 (0 + 1) (freq m)
          ((JfJ (symmDiff J s.1) 0 (zeroForm (w₀ s)) : (Fin n → ℤ) → Form ℂ (Fin n) 0) m)‖ ^ 2 :=
      fun s => hsd.of_nonneg_of_le (fun _ => sq_nonneg _) fun m => by
        rw [norm_deRham_zero, hcoef, hYeq]
        exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left
          (PiLp.norm_apply_le _ _) (norm_nonneg _)) 2
    have hmem := fun s => exists_mem_dPart_of_summable (hsum_s s)
    choose hw hnorm using hmem
    refine ⟨fun s => dPart (Q (Fin n)) (symmDiff J s.1) ((0 : ℕ) : ℤ) ⟨_, hw s⟩,
      fun s => (dPart (Q (Fin n)) (symmDiff J s.1) ((0 : ℕ) : ℤ)).mem_graph ⟨_, hw s⟩, ?_⟩
    simp only [hnorm, norm_deRham_zero, hcoef]
    rw [← Finset.mul_sum, ← Summable.tsum_finsetSum fun s _ => (hsum_s s).congr fun m => by
      rw [norm_deRham_zero, hcoef]]
    have hm : ∀ m, ∑ s : formIdx n (k : ℤ),
        (‖freq m‖ * ‖(Y : (Fin n → ℤ) → Form ℂ (Fin n) k) m (idx k s)‖) ^ 2 =
          ‖(JfJ J (k + 1) du : (Fin n → ℤ) → Form ℂ (Fin n) (k + 1)) m‖ ^ 2 := fun m => by
      rw [hYeq, mul_pow, EuclideanSpace.norm_sq_eq ((Y : (Fin n → ℤ) → Form ℂ (Fin n) k) m),
        Finset.mul_sum]
      refine Fintype.sum_equiv (idx k) _ _ fun s => ?_
      rw [mul_pow]
    simp only [hm]
    rw [← norm_sq_count', norm_sq_JfJ]
    field_simp


/-- `‖d_ξ v‖ ≤ |ξ| ‖v‖`. -/
theorem norm_deRham_le (ξ : EuclideanSpace ℝ (Fin n)) (v : Form ℂ (Fin n) k) :
    ‖(Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) ξ v‖ ≤ ‖ξ‖ * ‖v‖ := by
  rw [norm_deRham_eq]
  exact mul_le_mul_of_nonneg_left (norm_coexactProj_le v) (norm_nonneg _)

/-- **Forms whose coefficients are `H¹` in the classes `J ∆ s` lie in `D(d_J)`**, with
`‖d_J w‖² ≤ Σ_s ‖∇ w_s‖²` (the converse of the coefficient part of `exists_coexact_potential`;
on the Fourier side `|d_ξ x|² ≤ |ξ|² |x|² = Σ_s |ξ|² |x_s|²`). -/
theorem mem_dPart_of_coeff (w : L2F ℝ (Q (Fin n)) (formIdx n (k : ℤ)))
    (g : formIdx n (k : ℤ) → L2F ℝ (Q (Fin n)) (formIdx n (((0 : ℕ) : ℤ) + 1)))
    (hg : ∀ s : formIdx n (k : ℤ), (zeroForm (w s), g s) ∈ (dPart (Q (Fin n)) (symmDiff J s.1) ((0 : ℕ) : ℤ)).graph) :
    ∃ h : w ∈ (dPart (Q (Fin n)) J (k : ℤ)).domain,
      ‖dPart (Q (Fin n)) J (k : ℤ) ⟨w, h⟩‖ ^ 2 ≤ ∑ s, ‖g s‖ ^ 2 := by
  choose y hy1 hy2 using fun s => (LinearPMap.mem_graph_iff _).1 (hg s)
  have hy1' : ∀ s : formIdx n (k : ℤ), ((y s : (dPart (Q (Fin n)) (symmDiff J s.1) ((0 : ℕ) : ℤ)).domain) :
      L2F ℝ (Q (Fin n)) (formIdx n ((0 : ℕ) : ℤ))) = zeroForm (w s) := hy1
  have hy2' : ∀ s : formIdx n (k : ℤ), dPart (Q (Fin n)) (symmDiff J s.1) ((0 : ℕ) : ℤ) (y s) = g s := hy2
  set x := JfJ J k w
  -- the coefficient sequences of the components
  have hz : ∀ (s : formIdx n (k : ℤ)) m, (JfJ (symmDiff J s.1) (0 + 1) (g s) : (Fin n → ℤ) → Form ℂ (Fin n) (0 + 1)) m =
      (Feec.Fourier.Exterior.deRham (Fin n)).m 0 (0 + 1) (freq m)
        ((JfJ (symmDiff J s.1) 0 (zeroForm (w s)) : (Fin n → ℤ) → Form ℂ (Fin n) 0) m) :=
    fun s m => by
      rw [← hy2' s, ← hy1' s]
      exact (coeff_d_dPart (symmDiff J s.1) 0 (y s) m).symm
  have hzn : ∀ (s : formIdx n (k : ℤ)) m, ‖(JfJ (symmDiff J s.1) (0 + 1) (g s) :
      (Fin n → ℤ) → Form ℂ (Fin n) (0 + 1)) m‖ = ‖freq m‖ * ‖(x : (Fin n → ℤ) → Form ℂ (Fin n) k) m
        (idx k s)‖ := fun s m => by
    rw [hz, norm_deRham_zero, norm_form_zero _ ⟨∅, Finset.card_empty⟩, coeff_JfJ_zeroForm]
  have hsum_s : ∀ s : formIdx n (k : ℤ), Summable fun m => (‖freq m‖ *
      ‖(x : (Fin n → ℤ) → Form ℂ (Fin n) k) m (idx k s)‖) ^ 2 := fun s =>
    (summable_norm_sq_count' (JfJ (symmDiff J s.1) (0 + 1) (g s))).congr fun m => by rw [hzn]
  have hpt : ∀ m, ‖(Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) (freq m)
      ((x : (Fin n → ℤ) → Form ℂ (Fin n) k) m)‖ ^ 2 ≤
        ∑ s, (‖freq m‖ * ‖(x : (Fin n → ℤ) → Form ℂ (Fin n) k) m (idx k s)‖) ^ 2 := fun m => by
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_deRham_le k (freq m)
      ((x : (Fin n → ℤ) → Form ℂ (Fin n) k) m)) 2
    refine h1.trans_eq ?_
    rw [mul_pow, EuclideanSpace.norm_sq_eq ((x : (Fin n → ℤ) → Form ℂ (Fin n) k) m),
      Finset.mul_sum]
    exact (Fintype.sum_equiv (idx k) _ _ fun s => by rw [mul_pow]).symm
  have hsumall : Summable fun m => ∑ s,
      (‖freq m‖ * ‖(x : (Fin n → ℤ) → Form ℂ (Fin n) k) m (idx k s)‖) ^ 2 :=
    summable_sum fun s _ => hsum_s s
  obtain ⟨hw, hn⟩ := exists_mem_dPart_of_summable (J := J) (k := k) (u := w)
    (hsumall.of_nonneg_of_le (fun _ => sq_nonneg _) hpt)
  refine ⟨hw, ?_⟩
  rw [hn]
  have hle := (hsumall.of_nonneg_of_le (fun _ => sq_nonneg _) hpt).tsum_le_tsum hpt hsumall
  rw [Summable.tsum_finsetSum fun s _ => hsum_s s] at hle
  have he : ∀ s : formIdx n (k : ℤ), (2 ^ n)⁻¹ * ∑' m,
      (‖freq m‖ * ‖(x : (Fin n → ℤ) → Form ℂ (Fin n) k) m (idx k s)‖) ^ 2 = ‖g s‖ ^ 2 := by
    intro s
    have e := norm_sq_JfJ (symmDiff J s.1) (0 + 1) (g s)
    rw [norm_sq_count'] at e
    simp only [hzn] at e
    rw [e]; field_simp
  calc (2 ^ n)⁻¹ * ∑' m, ‖(Feec.Fourier.Exterior.deRham (Fin n)).m k (k + 1) (freq m)
        ((JfJ J k w : (Fin n → ℤ) → Form ℂ (Fin n) k) m)‖ ^ 2
      ≤ (2 ^ n)⁻¹ * ∑ s, ∑' m,
        (‖freq m‖ * ‖(x : (Fin n → ℤ) → Form ℂ (Fin n) k) m (idx k s)‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = ∑ s, ‖g s‖ ^ 2 := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => he s


end Potential

end Feec.Models.Cube.DeRhamIdent

/-! ### The continuous mirror BGG data in the forms model -/

namespace Feec.Models.Cube.MirrorWeakSymmetry

open Feec.Domain Feec.HilbertComplex Feec.FiniteElement Feec.Models.Cube.FEM
open Feec.Models.Cube.WeakSymmetry (W0 W1 W2 Wv rel_m10 rel_01 rel_12)
open Feec.Models.Cube.DeRhamIdent (dPart mapsTo_dPart dPart_comp dPart_le_maximal dPart_apply_eq
  dPart_empty)
open Feec.Models.Cube.ParitySmoother (zeroForm zeroForm_apply)

/-- **Regular potentials of `HΛ_J(Q)` on the cube domain** (`exists_coexact_potential`
transported to `cubeDomain 3 = Q`). -/
theorem exists_coexact_potential_cube (J : Finset (Fin 3)) (k : ℕ)
    (u : (dPart (cubeDomain 3) J (k : ℤ)).domain) :
    ∃ w : (dPart (cubeDomain 3) J (k : ℤ)).domain,
      dPart (cubeDomain 3) J (k : ℤ) w = dPart (cubeDomain 3) J (k : ℤ) u ∧
      ‖(w : L2F ℝ (cubeDomain 3) (formIdx 3 (k : ℤ)))‖ ≤
        (2 * Real.pi)⁻¹ * ‖dPart (cubeDomain 3) J (k : ℤ) u‖ ∧
      ∃ g : formIdx 3 (k : ℤ) → L2F ℝ (cubeDomain 3) (formIdx 3 (((0 : ℕ) : ℤ) + 1)),
        (∀ s, (zeroForm ((w : L2F ℝ (cubeDomain 3) (formIdx 3 (k : ℤ))) s), g s) ∈
          (dPart (cubeDomain 3) (symmDiff J s.1) ((0 : ℕ) : ℤ)).graph) ∧
        ∑ s, ‖g s‖ ^ 2 = ‖dPart (cubeDomain 3) J (k : ℤ) u‖ ^ 2 := by
  have key : ∀ (Ω : Set (Fin 3 → ℝ)) (_ : Ω = Geometry.Q (Fin 3))
      (u : (dPart Ω J (k : ℤ)).domain), ∃ w : (dPart Ω J (k : ℤ)).domain,
      dPart Ω J (k : ℤ) w = dPart Ω J (k : ℤ) u ∧
      ‖(w : L2F ℝ Ω (formIdx 3 (k : ℤ)))‖ ≤ (2 * Real.pi)⁻¹ * ‖dPart Ω J (k : ℤ) u‖ ∧
      ∃ g : formIdx 3 (k : ℤ) → L2F ℝ Ω (formIdx 3 (((0 : ℕ) : ℤ) + 1)),
        (∀ s, (zeroForm ((w : L2F ℝ Ω (formIdx 3 (k : ℤ))) s), g s) ∈
          (dPart Ω (symmDiff J s.1) ((0 : ℕ) : ℤ)).graph) ∧
        ∑ s, ‖g s‖ ^ 2 = ‖dPart Ω J (k : ℤ) u‖ ^ 2 := by
    rintro Ω rfl u
    exact DeRhamIdent.exists_coexact_potential J k u
  exact key _ (cubeDomain_eq_Q 3) u

/-! #### The operators and spaces -/

/-- The top row `d_∅ = d_max` in degree `0` (`grad` on `H¹(Q)`). -/
abbrev TD0 : W0 →ₗ.[ℝ] W1 := dPart (cubeDomain 3) ∅ 0
/-- The top row `d_∅ = d_max` in degree `1` (`curl` on `H(curl, Q)`). -/
abbrev TD1 : W1 →ₗ.[ℝ] W2 := dPart (cubeDomain 3) ∅ 1
/-- The component `a` of the bottom row in degree `0`: `grad` on `H¹(Q)` with vanishing trace on
the faces normal to `eₐ`. -/
abbrev BD0 (a : Fin 3) : W0 →ₗ.[ℝ] W1 := dPart (cubeDomain 3) {a} 0
/-- The component `a` of the bottom row in degree `1`: `curl` with vanishing tangential trace on
the faces normal to `eₐ`. -/
abbrev BD1 (a : Fin 3) : W1 →ₗ.[ℝ] W2 := dPart (cubeDomain 3) {a} 1

/-- `HΛ⁰(Q)` with the `L²` norm. -/
abbrev TU0 := TD0.domain
/-- `HΛ¹(Q)` with the `L²` norm. -/
abbrev TU1 := TD1.domain
/-- `∏ₐ H_{a}Λ⁰(Q)` with the `L²` norm. -/
abbrev BU0 := PiLp 2 fun a : Fin 3 => (BD0 a).domain
/-- `∏ₐ H_{a}Λ¹(Q)` with the `L²` norm. -/
abbrev BU1 := PiLp 2 fun a : Fin 3 => (BD1 a).domain

theorem isOpen_cube : IsOpen (cubeDomain 3) := isOpen_cubeDomain 3

theorem complexPart_d01 (J : Finset (Fin 3)) :
    (complexPart 3 J).d 0 1 = dPart (cubeDomain 3) J 0 := complexPart_d J 0

theorem complexPart_d12 (J : Finset (Fin 3)) :
    (complexPart 3 J).d 1 2 = dPart (cubeDomain 3) J 1 := complexPart_d J 1

theorem TD0_mem (x : TU0) : TD0 x ∈ TD1.domain := mapsTo_dPart isOpen_cube ∅ 0 x

theorem BD0_mem (a : Fin 3) (x : (BD0 a).domain) : BD0 a x ∈ (BD1 a).domain :=
  mapsTo_dPart isOpen_cube {a} 0 x

/-- `d` on the top row in degree `0`. -/
def tD0 : TU0 →ₗ[ℝ] TU1 where
  toFun x := ⟨TD0 x, TD0_mem x⟩
  map_add' x y := Subtype.ext (LinearPMap.map_add _ x y)
  map_smul' c x := Subtype.ext (LinearPMap.map_smul _ c x)

/-- `d` on the top row in degree `1`. -/
def tD1 : TU1 →ₗ[ℝ] W2 := TD1.toFun

/-- `d` on the bottom row in degree `0`, componentwise. -/
def bD0 : BU0 →ₗ[ℝ] BU1 where
  toFun φ := WithLp.toLp 2 fun a => ⟨BD0 a (φ a), BD0_mem a (φ a)⟩
  map_add' φ ψ := PiLp.ext fun a => Subtype.ext (LinearPMap.map_add _ (φ a) (ψ a))
  map_smul' c φ := PiLp.ext fun a => Subtype.ext (LinearPMap.map_smul _ c (φ a))

/-- `d` on the bottom row in degree `1`, componentwise. -/
def bD1 : BU1 →ₗ[ℝ] Wv W2 where
  toFun v := WithLp.toLp 2 fun a => BD1 a (v a)
  map_add' u v := PiLp.ext fun a => LinearPMap.map_add _ (u a) (v a)
  map_smul' c v := PiLp.ext fun a => LinearPMap.map_smul _ c (v a)

@[simp] theorem bD0_apply (φ : BU0) (a : Fin 3) : ((bD0 φ a : (BD1 a).domain) : W1) = BD0 a (φ a) :=
  rfl

@[simp] theorem bD1_apply (v : BU1) (a : Fin 3) : bD1 v a = BD1 a (v a) := rfl

/-- The inclusion `∏ₐ H_{a}Λ⁰ → (L²Λ⁰)³`. -/
def bIncl0 : BU0 →ₗ[ℝ] Wv W0 where
  toFun φ := WithLp.toLp 2 fun a => (φ a : W0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The inclusion `∏ₐ H_{a}Λ¹ → (L²Λ¹)³`. -/
def bIncl1 : BU1 →ₗ[ℝ] Wv W1 where
  toFun v := WithLp.toLp 2 fun a => (v a : W1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem bIncl0_apply (φ : BU0) (a : Fin 3) : bIncl0 φ a = (φ a : W0) := rfl
@[simp] theorem bIncl1_apply (v : BU1) (a : Fin 3) : bIncl1 v a = (v a : W1) := rfl

theorem norm_bIncl0 (φ : BU0) : ‖bIncl0 φ‖ = ‖φ‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), PiLp.norm_sq_eq_of_L2,
    PiLp.norm_sq_eq_of_L2]
  rfl

theorem norm_bIncl1 (v : BU1) : ‖bIncl1 v‖ = ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), PiLp.norm_sq_eq_of_L2,
    PiLp.norm_sq_eq_of_L2]
  rfl

/-- **`S⁰` maps `∏ₐ H_{a}Λ⁰(Q)` into `HΛ¹(Q)` with `d S⁰ = −S¹ d`**: the bottom row lies in
`HΛ⁰(Q)³` (`d_{a} ≤ d_max`) and `S` maps `D(d_max)³` into `D(d_max) = D(d_∅)`. -/
theorem wsL2_bIncl0_mem (φ : BU0) :
    ∃ h : wsL2 (Ω := cubeDomain 3) 0 (bIncl0 φ) ∈ TD1.domain,
      TD1 ⟨_, h⟩ = -wsL2 (Ω := cubeDomain 3) 1 (bIncl1 (bD0 φ)) := by
  have hv : ∀ a, bIncl0 φ a ∈ ((extDerivOp ℝ 3 0).maximal (cubeDomain 3)).domain := fun a =>
    (dPart_le_maximal isOpen_cube {a} 0).1 (φ a).2
  obtain ⟨h, e⟩ := wsL2_mem_maximal isOpen_cube 0 (v := bIncl0 φ) hv
  have hD : TD1 = (extDerivOp ℝ 3 1).maximal (cubeDomain 3) := dPart_empty isOpen_cube 1
  have h' : wsL2 (Ω := cubeDomain 3) 0 (bIncl0 φ) ∈ TD1.domain := by rw [hD]; exact h
  refine ⟨h', ?_⟩
  rw [dPart_apply_eq isOpen_cube ∅ 1 ⟨_, h'⟩]
  refine e.trans ?_
  congr 2
  refine PiLp.ext fun a => ?_
  exact (dPart_apply_eq isOpen_cube {a} 0 (φ a)).symm

/-- `S⁰` on the domains. -/
def mS0 : BU0 →ₗ[ℝ] TU1 where
  toFun φ := ⟨_, (wsL2_bIncl0_mem φ).1⟩
  map_add' φ ψ := Subtype.ext (by simp)
  map_smul' c φ := Subtype.ext (by simp)

theorem coe_mS0 (φ : BU0) : ((mS0 φ : TU1) : W1) = wsL2 (Ω := cubeDomain 3) 0 (bIncl0 φ) := rfl

/-- `S¹` on the domain. -/
def mS1 : BU1 →ₗ[ℝ] W2 where
  toFun v := wsL2 (Ω := cubeDomain 3) 1 (bIncl1 v)
  map_add' u v := by simp
  map_smul' c v := by simp

theorem mS1_apply (v : BU1) : mS1 v = wsL2 (Ω := cubeDomain 3) 1 (bIncl1 v) := rfl

/-- **The continuous BGG data of the mirror scheme (6.5)** in the `W`-normed domain model of
`Feec.BGG.Segment`: top row `HΛ⁰(Q) → HΛ¹(Q) → L²Λ²(Q)` (no boundary condition), bottom row
`∏ₐ H_{a}Λ⁰(Q) → ∏ₐ H_{a}Λ¹(Q) → (L²Λ²(Q))³` (component `a` with vanishing tangential traces on
the faces normal to `eₐ`), `S⁰ = I`, `S¹ = 2 vskw`. -/
def mirrorBGGSegment : Feec.BGG.Segment ℝ TU0 TU1 W2 BU0 BU1 (Wv W2) where
  d0 := tD0
  d1 := tD1
  dt0 := bD0
  dt1 := bD1
  S0 := mS0
  S1 := mS1
  d1_d0 x := dPart_comp isOpen_cube ∅ 0 x
  dt1_dt0 φ := PiLp.ext fun a => dPart_comp isOpen_cube {a} 0 (φ a)
  anticomm φ := (wsL2_bIncl0_mem φ).2


/-! #### Hodge theory of the rows -/

theorem cycles_zero_part (a : Fin 3) : (complexPart 3 {a}).cycles 0 = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
  rw [← (complexPart 3 {a}).exact_iff_harmonic_eq_bot (closedRangeAt_part {a} 0) |>.2
    (harmonic_eq_bot_part (by simp)), (complexPart 3 {a}).boundaries_eq rel_m10] at hx
  obtain ⟨y, hy⟩ := hx
  have : Subsingleton (L2F ℝ (cubeDomain 3) (formIdx 3 (-1 : ℤ))) :=
    LocalElement.subsingleton_L2F_negSucc _ 0
  have hy0 : y = 0 := Subtype.ext (Subsingleton.elim _ _)
  rw [← hy, hy0]
  exact LinearPMap.map_zero _

/-- **Poincaré on the bottom row in degree `0`**: `‖φ‖ ≤ (2π)⁻¹ ‖∇φ‖` on `H¹(Q)` with vanishing
trace on the faces normal to `eₐ`. -/
theorem bpoincare0 (a : Fin 3) (x : (BD0 a).domain) :
    ‖(x : W0)‖ ≤ (2 * Real.pi)⁻¹ * ‖BD0 a x‖ := by
  have h := norm_le_of_mem_orthogonal_cycles_part (n := 3) {a} rel_01
  rw [complexPart_d01] at h
  exact h x (by rw [cycles_zero_part, Submodule.bot_orthogonal_eq_top]; exact Submodule.mem_top)

/-- `d_J` in degree `0` on the cube, with target `L²Λ¹`. -/
abbrev dQ0 (J : Finset (Fin 3)) : W0 →ₗ.[ℝ] W1 := dPart (cubeDomain 3) J 0

theorem cycles_one_part (J : Finset (Fin 3)) :
    (complexPart 3 J).cycles 1 = (dPart (cubeDomain 3) J 1).ker := by
  rw [(complexPart 3 J).cycles_eq rel_12, complexPart_d12]

theorem boundaries_one_part (J : Finset (Fin 3)) :
    (complexPart 3 J).boundaries 1 = LinearMap.range (dPart (cubeDomain 3) J 0).toFun := by
  rw [(complexPart 3 J).boundaries_eq rel_01, complexPart_d01]

/-- **The Hodge decomposition of `HΛ_J¹(Q)` with harmonic part**:
`x = dψ + w + h`, `h ∈ ℌ¹`, `d w = d x`, `‖w‖ ≤ (2π)⁻¹ ‖d x‖`. -/
theorem hodge_one_part (J : Finset (Fin 3)) (x : (dPart (cubeDomain 3) J 1).domain) :
    ∃ ψ : (dQ0 J).domain, ∃ w : (dPart (cubeDomain 3) J 1).domain,
      ∃ h ∈ (complexPart 3 J).harmonic 1,
        (x : W1) = dQ0 J ψ + w + h ∧
        dPart (cubeDomain 3) J 1 w = dPart (cubeDomain 3) J 1 x ∧
        ‖(w : W1)‖ ≤ (2 * Real.pi)⁻¹ * ‖dPart (cubeDomain 3) J 1 x‖ := by
  set K := (complexPart 3 J).cycles 1
  have hpK : K.starProjection (x : W1) ∈ K := K.starProjection_apply_mem _
  have hp : K.starProjection (x : W1) ∈ (dPart (cubeDomain 3) J 1).ker := by
    rw [← cycles_one_part]; exact hpK
  obtain ⟨p, hpe, hp0⟩ := LinearPMap.mem_ker_iff.1 hp
  have hsup := (complexPart 3 J).boundaries_sup_harmonic (closedRangeAt_part J 1)
  have hpK2 : K.starProjection (x : W1) ∈
      (complexPart 3 J).boundaries 1 ⊔ (complexPart 3 J).harmonic 1 := by
    rw [hsup]; exact hpK
  obtain ⟨b, hb, h, hh, hbh⟩ := Submodule.mem_sup.1 hpK2
  rw [boundaries_one_part] at hb
  obtain ⟨ψ, hψ⟩ := hb
  refine ⟨ψ, x - p, h, hh, ?_, ?_, ?_⟩
  · rw [Submodule.coe_sub, ← hpe, ← hbh]
    rw [show dQ0 J ψ = b from hψ]; abel
  · rw [LinearPMap.map_sub, hp0, sub_zero]
  · have hw : ((x - p : (dPart (cubeDomain 3) J 1).domain) : W1) ∈ Kᗮ := by
      rw [Submodule.coe_sub, ← hpe]
      exact K.sub_starProjection_mem_orthogonal _
    have h1 := norm_le_of_mem_orthogonal_cycles_part (n := 3) J rel_12
    rw [complexPart_d12] at h1
    have := h1 (x - p) hw
    rwa [LinearPMap.map_sub, hp0, sub_zero] at this

theorem harmonic_orth_part (J : Finset (Fin 3)) {h : W1} (hh : h ∈ (complexPart 3 J).harmonic 1)
    (ψ : (dQ0 J).domain) : ⟪h, dQ0 J ψ⟫_ℝ = 0 := by
  rw [(complexPart 3 J).harmonic_eq] at hh
  refine Submodule.inner_left_of_mem_orthogonal ?_ hh.2
  rw [boundaries_one_part]
  exact ⟨ψ, rfl⟩

theorem harmonic_le_domain (J : Finset (Fin 3)) {h : W1}
    (hh : h ∈ (complexPart 3 J).harmonic 1) : h ∈ (dPart (cubeDomain 3) J 1).domain := by
  have := (complexPart 3 J).harmonic_le_cycles 1 hh
  rw [cycles_one_part] at this
  exact (dPart (cubeDomain 3) J 1).ker_le_domain this

theorem constForm_apply_of_ne {Ω : Set (Fin 3 → ℝ)} (hm : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) {k : ℤ} {s₀ s : formIdx 3 k} (hs : s ≠ s₀) :
    DeRhamIdent.constForm hm hb s₀ s = 0 := by
  refine Lp.ext ?_
  filter_upwards [MemLp.coeFn_toLp (DeRhamIdent.memLp_constFun hm hb s₀ s),
    Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with y h1 h2
  change ((DeRhamIdent.memLp_constFun hm hb s₀ s).toLp (DeRhamIdent.constFun s₀ s) :
    (Fin 3 → ℝ) → ℝ) y = _
  rw [h1, h2]
  simp [DeRhamIdent.constFun, hs]

/-- The constant `1`-form `dxₐ` on `Q`. -/
abbrev dxForm (a : Fin 3) : W1 := formPart 3 {a}

/-- **The harmonic `1`-forms of the bottom component `a` are `ℝ dxₐ`.** -/
theorem harmonic_one_part (a : Fin 3) : (complexPart 3 {a}).harmonic 1 = ℝ ∙ dxForm a :=
  harmonic_card_eq_span_part {a}

/-- **`S¹` kills the harmonic forms of the bottom row**: `S¹ (Σₐ cₐ dxₐ ⊗ eₐ) = Σₐ cₐ dxₐ ∧ dxₐ = 0`
(diagonal matrices are symmetric). -/
theorem wsL2_harmonic_eq_zero {v : Wv W1} (hv : ∀ a, v a ∈ (complexPart 3 {a}).harmonic 1) :
    wsL2 (Ω := cubeDomain 3) 1 v = 0 := by
  have hc : ∀ a, ∃ c : ℝ, v a = c • dxForm a := fun a => by
    have := hv a
    rw [harmonic_one_part, Submodule.mem_span_singleton] at this
    obtain ⟨c, hc⟩ := this
    exact ⟨c, hc.symm⟩
  choose c hc using hc
  refine PiLp.ext fun t => ?_
  rw [wsL2_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [hc p.1]
  by_cases hp : p.2.1 = {p.1}
  · rw [wsCoeff_eq]
    have : ¬ (p.1 ∈ t.1 ∧ t.1.erase p.1 = p.2.1) := by
      rintro ⟨-, h⟩
      rw [hp] at h
      have : p.1 ∈ t.1.erase p.1 := h ▸ Finset.mem_singleton_self p.1
      simp at this
    simp [this]
  · have h0 : (c p.1 • dxForm p.1) p.2 = 0 := by
      rw [PiLp.smul_apply]
      have : (dxForm p.1) p.2 = 0 := constForm_apply_of_ne _ _ fun h => hp (by
        rw [h])
      rw [this, smul_zero]
    rw [h0, smul_zero]


/-! #### The hypotheses modulo harmonic forms -/

/-- **The harmonic forms of the bottom row**, `𝔥 = {Σₐ cₐ dxₐ ⊗ eₐ}` (componentwise
`ℌ¹(HΛ_{a}(Q)) = ℝ dxₐ`, `harmonic_one_part`). -/
def harmBot : Submodule ℝ BU1 where
  carrier := {v | ∀ a, (v a : W1) ∈ (complexPart 3 {a}).harmonic 1}
  add_mem' hu hv a := Submodule.add_mem _ (hu a) (hv a)
  zero_mem' _ := Submodule.zero_mem _
  smul_mem' c _ hv a := Submodule.smul_mem _ c (hv a)

theorem mem_harmBot {v : BU1} : v ∈ harmBot ↔ ∀ a, (v a : W1) ∈ (complexPart 3 {a}).harmonic 1 :=
  Iff.rfl

theorem norm_sq_BU0 (φ : BU0) : ‖φ‖ ^ 2 = ∑ a, ‖(φ a : W0)‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ φ
theorem norm_sq_BU1 (v : BU1) : ‖v‖ ^ 2 = ∑ a, ‖(v a : W1)‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ v
theorem norm_sq_bD0 (φ : BU0) : ‖bD0 φ‖ ^ 2 = ∑ a, ‖BD0 a (φ a)‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ (bD0 φ)
theorem norm_sq_bD1 (v : BU1) : ‖bD1 v‖ ^ 2 = ∑ a, ‖BD1 a (v a)‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ (bD1 v)

theorem le_of_sq_le_sq' {x y : ℝ} (hy : 0 ≤ y) (h : x ^ 2 ≤ y ^ 2) : x ≤ y :=
  abs_le_of_sq_le_sq' h hy |>.2

/-- **Poincaré on `∏ₐ H_{a}Λ⁰(Q)`**: `‖φ‖ ≤ (2π)⁻¹ ‖dφ‖`. -/
theorem mirror_poinct0 (φ : BU0) : ‖φ‖ ≤ (2 * Real.pi)⁻¹ * ‖bD0 φ‖ := by
  refine le_of_sq_le_sq' (by positivity) ?_
  rw [mul_pow, norm_sq_BU0, norm_sq_bD0, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (bpoincare0 a (φ a)) 2

/-- **The Hodge decomposition of `∏ₐ H_{a}Λ¹(Q)` modulo `𝔥`.** -/
theorem mirror_hodget1 (v : BU1) : ∃ ψ w, ∃ k ∈ harmBot, v = bD0 ψ + w + k ∧
    ‖w‖ ≤ (2 * Real.pi)⁻¹ * ‖bD1 v‖ := by
  choose ψ w h hh hv hdw hnw using fun a => hodge_one_part {a} (v a)
  refine ⟨WithLp.toLp 2 ψ, WithLp.toLp 2 w,
    WithLp.toLp 2 fun a => ⟨h a, harmonic_le_domain {a} (hh a)⟩, fun a => hh a,
    PiLp.ext fun a => Subtype.ext (hv a), ?_⟩
  refine le_of_sq_le_sq' (by positivity) ?_
  rw [mul_pow, norm_sq_BU1, norm_sq_bD1, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hnw a) 2

theorem mirror_harmonic_orth (k : BU1) (hk : k ∈ harmBot) (ψ : BU0) :
    ⟪k, bD0 ψ⟫_ℝ = 0 := by
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Submodule.coe_inner]
  exact harmonic_orth_part {a} (hk a) (ψ a)

theorem mirror_S1_harmonic (k : BU1) (hk : k ∈ harmBot) : mS1 k = 0 :=
  wsL2_harmonic_eq_zero fun a => hk a

theorem mirror_boundS1 (v : BU1) :
    ‖mS1 v‖ ^ 2 ≤ Real.sqrt 2 ^ 2 * Feec.BGG.graphSq bD1 v := by
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h := norm_wsL2_sq_le (Ω := cubeDomain 3) 1 (bIncl1 v)
  have h1 : (((1 : ℤ) : ℝ) + 1) = 2 := by norm_num
  rw [h1, norm_bIncl1] at h
  rw [hsq2, Feec.BGG.graphSq, mS1_apply]
  nlinarith [sq_nonneg ‖bD1 v‖]

/-- **The continuous hypotheses of the Ch. 6 convergence theory for the mirror data, modulo the
harmonic forms of the bottom row** (`Feec.BGG.HarmonicStability`), with `C_p = (2π)⁻¹` and
`C_S = √2`. The top row has the constant mode (`mirror_constantMode_continuous`), the bottom
row the harmonic forms `dxₐ ⊗ eₐ` (`harmBot`), and `Feec.BGG.Stability` fails
(`mirror_not_stability`). -/
theorem mirror_harmonicStability :
    Feec.BGG.HarmonicStability mirrorBGGSegment harmBot (2 * Real.pi)⁻¹ (Real.sqrt 2) where
  Cp_nonneg := by positivity
  CS_nonneg := Real.sqrt_nonneg _
  poinct0 := mirror_poinct0
  hodget1 := mirror_hodget1
  harmonic_orth := mirror_harmonic_orth
  S1_harmonic := mirror_S1_harmonic
  boundS1 := mirror_boundS1

/-! #### The top row: exactness at `HΛ¹`, the constant mode, and the regularity -/

theorem harmonic_one_empty : (complexPart 3 ∅).harmonic 1 = ⊥ :=
  harmonic_eq_bot_part (by simp)

/-- **Exactness of `HΛ(Q)` at `HΛ¹`** (`ℌ¹(HΛ(Q)) = 0`): `curl μ = 0` gives `μ = grad ρ`. -/
theorem mirror_exact1 (μ : TU1) (hμ : tD1 μ = 0) : ∃ ρ, tD0 ρ = μ := by
  have hz : (μ : W1) ∈ (complexPart 3 ∅).cycles 1 := by
    rw [cycles_one_part]
    exact LinearPMap.mem_ker_iff.2 ⟨μ, rfl, hμ⟩
  rw [← (complexPart 3 ∅).exact_iff_harmonic_eq_bot (closedRangeAt_part ∅ 1) |>.2
    harmonic_one_empty, boundaries_one_part] at hz
  obtain ⟨ρ, hρ⟩ := hz
  exact ⟨ρ, Subtype.ext hρ⟩

/-- The constant function `1` on `Q`. -/
abbrev constOneForm : W0 := formPart 3 ∅

theorem oneForm_mem_harmonic : constOneForm ∈ (complexPart 3 ∅).harmonic 0 := by
  have h : (complexPart 3 ∅).harmonic 0 = ℝ ∙ constOneForm := harmonic_card_eq_span_part ∅
  rw [h]
  exact Submodule.mem_span_singleton_self _

theorem oneForm_mem : constOneForm ∈ TD0.domain := by
  have h := (complexPart 3 ∅).harmonic_le_cycles 0 oneForm_mem_harmonic
  rw [(complexPart 3 ∅).cycles_eq rel_01, complexPart_d01] at h
  exact TD0.ker_le_domain h

/-- The constant mode `1 ∈ HΛ⁰(Q)`. -/
def oneU : TU0 := ⟨constOneForm, oneForm_mem⟩

theorem oneU_ne_zero : oneU ≠ 0 := fun h =>
  formPart_ne_zero (n := 3) ∅ (congrArg Subtype.val h)

theorem tD0_oneU : tD0 oneU = 0 := by
  have h := (complexPart 3 ∅).harmonic_le_cycles 0 oneForm_mem_harmonic
  rw [(complexPart 3 ∅).cycles_eq rel_01, complexPart_d01] at h
  obtain ⟨y, hy, hy0⟩ := LinearPMap.mem_ker_iff.1 h
  refine Subtype.ext ?_
  change TD0 oneU = 0
  rw [show oneU = y from Subtype.ext hy, hy0]

/-- **The constant mode of the continuous top row**: `σ = 1` has `grad σ = 0` (`σ` carries no
boundary condition), so the Poincaré inequality `poinc0` fails on `HΛ⁰(Q)`. -/
theorem mirror_constantMode_continuous : oneU ≠ 0 ∧ mirrorBGGSegment.d0 oneU = 0 :=
  ⟨oneU_ne_zero, tD0_oneU⟩

/-- **`Feec.BGG.Stability` fails for the mirror data** (whatever the constants): the constant
mode violates `poinc0`. The convergence theory runs on `mirror_harmonicStability` instead. -/
theorem mirror_not_stability (Cp CR CS : ℝ) : ¬ Feec.BGG.Stability mirrorBGGSegment Cp CR CS := by
  intro H
  have h := H.poinc0 oneU
  rw [show mirrorBGGSegment.d0 oneU = 0 from tD0_oneU, norm_zero, mul_zero] at h
  exact oneU_ne_zero (norm_le_zero_iff.1 h)

theorem dxForm_mem_harmonic (a : Fin 3) : dxForm a ∈ (complexPart 3 {a}).harmonic 1 := by
  rw [harmonic_one_part]; exact Submodule.mem_span_singleton_self _

/-- The bottom harmonic form `dxₐ ⊗ eₐ`. -/
def harmVec (a : Fin 3) : BU1 :=
  WithLp.toLp 2 (Pi.single (M := fun b : Fin 3 => (BD1 b).domain) a
    ⟨dxForm a, harmonic_le_domain {a} (dxForm_mem_harmonic a)⟩)

theorem harmVec_mem (a : Fin 3) : harmVec a ∈ harmBot := fun b => by
  by_cases h : b = a
  · subst h
    simp only [harmVec, PiLp.toLp_apply, Pi.single_eq_same]
    rw [harmonic_one_part]; exact Submodule.mem_span_singleton_self _
  · simp only [harmVec, PiLp.toLp_apply, Pi.single_eq_of_ne h, ZeroMemClass.coe_zero]
    exact Submodule.zero_mem _

theorem harmVec_ne_zero (a : Fin 3) : harmVec a ≠ 0 := fun h => by
  have := congrArg (fun v : BU1 => ((v a : (BD1 a).domain) : W1)) h
  simp only [harmVec, PiLp.toLp_apply, Pi.single_eq_same, PiLp.zero_apply,
    ZeroMemClass.coe_zero] at this
  exact formPart_ne_zero (n := 3) {a} this

theorem harmBot_ne_bot : harmBot ≠ ⊥ := fun h =>
  harmVec_ne_zero 0 ((Submodule.mem_bot ℝ).1 (h ▸ harmVec_mem 0))

/-- **`mirrorCurlPotential`, the mirror regularity hypothesis, proved**: for every
`u ∈ HΛ¹(Q)` (no boundary condition) there is `φ` with `φₐ ∈ H¹(Q)`, `φₐ = 0` on the faces
normal to `eₐ` (`φ ∈ ∏ₐ H_{a}Λ⁰(Q)`), `curl S⁰φ = curl u` and `‖∇φ‖ = ‖curl u‖` (constant
`C_R = 1`). `S⁰φ` is the coexact part of `u` in the absolute parity model; Gaffney's identity
`|ξ|²|v|² = |ξ × v|² + |ξ · v|²` puts the parity extensions of its components in `H¹(𝕋³)`
(`exists_coexact_potential`). This is the field `reg` of `Feec.BGG.Stability` for the mirror
data, without hypothesis (compare `Feec.Models.Cube.WeakSymmetry.CurlPotential`, a different
parity class). See [Hiptmair2002], Lemma 2.4 (regular decomposition), [Brezis2011], §9.2. -/
theorem mirrorCurlPotential (u : TU1) :
    ∃ φ : BU0, mirrorBGGSegment.d1 (mirrorBGGSegment.S0 φ) = mirrorBGGSegment.d1 u ∧
      ‖mirrorBGGSegment.dt0 φ‖ ≤ 1 * ‖mirrorBGGSegment.d1 u‖ := by
  obtain ⟨w, hdw, -, g, hg, hsum⟩ := exists_coexact_potential_cube ∅ 1 u
  set sb : Fin 3 → formIdx 3 ((1 : ℕ) : ℤ) := fun b => FEM.singletonEquiv 3 b
  have hgb : ∀ b, (zeroForm ((w : W1) (sb b)), g (sb b)) ∈ (BD0 b).graph := fun b => by
    have h := hg (sb b)
    have e : symmDiff (∅ : Finset (Fin 3)) {b} = {b} := by ext x; simp [Finset.mem_symmDiff]
    rwa [show ((sb b).1 : Finset (Fin 3)) = {b} from rfl, e] at h
  have hmem : ∀ b, zeroForm ((w : W1) (sb b)) ∈ (BD0 b).domain := fun b =>
    LinearPMap.mem_domain_of_mem_graph (hgb b)
  have happ : ∀ b, BD0 b ⟨_, hmem b⟩ = g (sb b) := fun b =>
    ((LinearPMap.image_iff (hmem b)).2 (hgb b)).symm
  set φ : BU0 := WithLp.toLp 2 fun b => ⟨_, hmem b⟩
  have hS : mS0 φ = w := by
    refine Subtype.ext (PiLp.ext fun t => ?_)
    obtain ⟨j, rfl⟩ := (FEM.singletonEquiv 3).surjective t
    change wsL2 (Ω := cubeDomain 3) 0 (bIncl0 φ) ⟨{j}, by simp⟩ = _
    rw [WeakSymmetry.wsL2_zero_apply, bIncl0_apply]
    exact zeroForm_apply _ _
  have hφb : ∀ b, BD0 b (φ b) = g (sb b) := fun b => happ b
  clear_value φ
  have key : ‖bD0 φ‖ ^ 2 = ‖TD1 u‖ ^ 2 := by
    rw [norm_sq_bD0]
    calc ∑ a, ‖BD0 a (φ a)‖ ^ 2 = ∑ a, ‖g (sb a)‖ ^ 2 :=
          Finset.sum_congr rfl fun b _ => by rw [hφb b]
      _ = ∑ s, ‖g s‖ ^ 2 := (FEM.singletonEquiv 3).sum_comp (fun s => ‖g s‖ ^ 2)
      _ = ‖TD1 u‖ ^ 2 := hsum
  refine ⟨φ, ?_, ?_⟩
  · change tD1 (mS0 φ) = tD1 u
    rw [hS]; exact hdw
  · exact (le_of_sq_le_sq' (norm_nonneg _) key.le).trans_eq (one_mul _).symm

end Feec.Models.Cube.MirrorWeakSymmetry
