module

public import Feec.Ch4.Whole
public import Feec.Ch4.TorusSym

/-!
# Thesis Prop 4.19 on the whole space `ℝ³`: the strong-symmetry complex

Prop 4.19 ([QuennevilleBelair2015, §4.11]) is Prop 4.17 for the strong-symmetry complex (4.16)
`H̊²(R) --grad grad--> H̊(curl, S) --curl--> L²(T)` (`R` scalars, `S` symmetric, `T` trace-free
matrices). The thesis' bounded-domain statement fails (`Feec.Ch4.BoundedSym`);
`Feec.Ch4.TorusSym` proves the periodic version. This file proves it on the whole space `ℝ³`,
with no boundary, in the Fourier model of `Feec.Ch4.Whole`.

## Model

`L2R = L²(ℝ³_ξ; ℂ)`, `L2S = L²(ℝ³_ξ; S)`, `L2T = L²(ℝ³_ξ; T)` (Fourier transforms, real Hilbert
spaces), with the fibre algebra of `Feec.Ch4.TorusSym` at `freqW ξ = 2πξ`: `grad grad ↦ -û ξξᵀ`
(`hessW`), `curl : S → T` (`curlSW`), `(grad grad)* = div div` (`coeFn_adjoint_hessW`),
`curl* = sym curl` (`coeFn_adjoint_curlSW`). The TSD fibre projections inside `S` and `T` are
strongly measurable (`stronglyMeasurable_projS`, `stronglyMeasurable_projT`, from
`Feec.Whole.stronglyMeasurable_projTSD`), so `P_TSD` acts fibrewise (`coeFn_projS`,
`coeFn_projT`). The symbols are continuous in `ξ` (`continuous_hessS`, `continuous_curlS`,
`continuous_divdivS`, `continuous_symCurlS`). Not formalized: the identification of `L2S`, `L2T`
with Fourier transforms of symmetric resp. trace-free physical fields (on `𝕋³` this is
`Feec.TorusSym.matrixFourier_mem_sym`), and of the multipliers with weak derivatives
(`Feec.Ch4.WholeWeak` does this for `H(curl; M)` only).

## Main results

* `symWComplex : HilbertComplex2 L2R L2S L2T`, the complex (4.16) on `ℝ³`.
* All hypotheses of `Feec.Constraints.prop_4_17` for `S1 = S2 = L²(TSD)`: `L2TSDS_le_ker`,
  `projKc_mem_domL` (the projection hypotheses `projS_mem_HcurlS_HdivdivS`,
  `projT_mem_HsymCurlT`), `curlSW_mem_L2TSDT`, `adjoint_curlSW_mem_L2TSDS`; also
  `projS_mem_H1S` (`P_TSD H(curl, S) ⊆ Ḣ¹(S)`).
* **`prop_4_19_whole`**, **`prop_4_19_whole_exists`** (existence and uniqueness via Stone's
  theorem, for TSD data `E₀ ∈ H(curl, S)`, `B₀ ∈ H(sym curl, T)`; `ini_mem_domL_iff_of_TSD`) and
  `prop_4_19_whole_group` (all `t ∈ ℝ`).

## Correction

On `ℝ³` the thesis' projection conjectures for Prop 4.19 are theorems and its density
conjectures are unnecessary, exactly as on `𝕋³`; the thesis' initial-data space misplaces the
boundary conditions (see `Feec.Ch4.TorusSym`), and here there are none.

## References

* [QuennevilleBelair2015], §3.4 (Lemma 3.5), §4.11 ((4.16)–(4.18), Prop 4.19), §4.3 (Thm 4.3)
* [ArnoldHu2021], [Eastwood2000] (the `grad grad`–`curl`–`div` complex)
* [ACBY1997] (the Einstein–Bianchi system)
* [Pazy1983], §1.10 (Stone's theorem)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace ENNReal Topology
open MeasureTheory LinearPMap Set Filter

namespace Feec.WholeSym

open Feec.Torus Feec.TorusSym Feec.Whole HilbertComplex2 Constraints

section Symbols

/-- A map into a submodule is continuous if its coercion is. -/
theorem continuous_of_coe {U : Submodule ℝ Mat3} {f : Freq → U}
    (h : Continuous fun ξ => (f ξ : Mat3)) : Continuous f :=
  continuous_induced_rng.2 h

/-- The scalar gradient symbol `c ↦ i c ξ`. -/
def gradVec (ξ : Freq) (c : ℂ) : Vec3 := vec fun a => Complex.I * c * ξ a

/-- `grad grad = grad ∘ grad` on the symbol level. -/
theorem hessM_eq_gradSym (ξ : Freq) (c : ℂ) : hessM ξ c = gradSym ξ (gradVec ξ c) := by
  ext ⟨a, b⟩
  simp only [hessM_apply, gradSym_apply, gradVec, vec_apply]
  ring_nf; rw [Complex.I_sq]; ring

theorem continuous_hessS : Continuous hessS := by
  refine continuous_clm_apply.2 fun c => continuous_of_coe ?_
  simp only [coe_hessS, hessM_eq_gradSym]
  refine continuous_gradSym.clm_apply ?_
  refine Whole.continuous_of_linear (fun ξ η => ?_) (fun r ξ => ?_)
  · ext a; simp [gradVec]; ring
  · ext a; simp [gradVec, Complex.real_smul]; ring

theorem continuous_curlS : Continuous curlS := by
  refine continuous_clm_apply.2 fun A => continuous_of_coe ?_
  simp only [coe_curlS]
  exact continuous_curlSym.clm_apply continuous_const

theorem continuous_symCurlS : Continuous symCurlS := by
  refine continuous_clm_apply.2 fun ρ => continuous_of_coe ?_
  simp only [coe_symCurlS]
  exact symM.continuous.comp (continuous_curlSym.clm_apply continuous_const)

theorem divdivS_eq (ξ : Freq) (A : Sym3) :
    divdivS ξ A = -∑ a, divR ξ (A : Mat3) a * ξ a := by
  simp only [divdivS_apply, divR_apply, Fin.sum_univ_three]
  ring

theorem continuous_divdivS : Continuous divdivS := by
  refine continuous_clm_apply.2 fun A => ?_
  simp only [divdivS_eq]
  refine Continuous.neg (continuous_finsetSum _ fun a _ => ?_)
  refine Continuous.mul ?_ ?_
  · exact (EuclideanSpace.proj (𝕜 := ℂ) a).continuous.comp
      (continuous_divR.clm_apply continuous_const)
  · exact Complex.continuous_ofReal.comp (EuclideanSpace.proj (𝕜 := ℝ) a).continuous

theorem stronglyMeasurable_hessW : StronglyMeasurable fun ξ => hessS (freqW ξ) :=
  (continuous_hessS.comp continuous_freqW).stronglyMeasurable

theorem stronglyMeasurable_curlSW : StronglyMeasurable fun ξ => curlS (freqW ξ) :=
  (continuous_curlS.comp continuous_freqW).stronglyMeasurable

theorem stronglyMeasurable_divdivW : StronglyMeasurable fun ξ => divdivS (freqW ξ) :=
  (continuous_divdivS.comp continuous_freqW).stronglyMeasurable

theorem stronglyMeasurable_symCurlW : StronglyMeasurable fun ξ => symCurlS (freqW ξ) :=
  (continuous_symCurlS.comp continuous_freqW).stronglyMeasurable

theorem stronglyMeasurable_normS :
    StronglyMeasurable fun ξ => ‖freqW ξ‖ • ContinuousLinearMap.id ℝ Sym3 :=
  ((continuous_norm.comp continuous_freqW).smul continuous_const).stronglyMeasurable

/-- The TSD projection in `U ⊇ tsd ξ` is the ambient projection followed by the projection
onto `U`. -/
theorem starProjection_comap_eq {U K : Submodule ℝ Mat3} (h : K ≤ U) (x : U) :
    (K.comap U.subtype).starProjection x = U.orthogonalProjectionOnto (K.starProjection x) := by
  rw [← coe_starProjection_comap h x, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

theorem stronglyMeasurable_projS :
    StronglyMeasurable fun ξ => (tsdS (freqW ξ)).starProjection := by
  refine stronglyMeasurable_clm_of_apply fun A => ?_
  have : (fun ξ => (tsdS (freqW ξ)).starProjection A) =
      fun ξ => symSub.orthogonalProjectionOnto ((tsd (freqW ξ)).starProjection (A : Mat3)) :=
    funext fun ξ => starProjection_comap_eq (tsd_le_symSub _) A
  rw [this]
  exact symSub.orthogonalProjectionOnto.continuous.comp_stronglyMeasurable
    (StronglyMeasurable.apply_continuousLinearMap stronglyMeasurable_projTSD _)

theorem stronglyMeasurable_projT :
    StronglyMeasurable fun ξ => (tsdT (freqW ξ)).starProjection := by
  refine stronglyMeasurable_clm_of_apply fun A => ?_
  have : (fun ξ => (tsdT (freqW ξ)).starProjection A) =
      fun ξ => trSub.orthogonalProjectionOnto ((tsd (freqW ξ)).starProjection (A : Mat3)) :=
    funext fun ξ => starProjection_comap_eq (tsd_le_trSub _) A
  rw [this]
  exact trSub.orthogonalProjectionOnto.continuous.comp_stronglyMeasurable
    (StronglyMeasurable.apply_continuousLinearMap stronglyMeasurable_projTSD _)

end Symbols

section Complex

/-- Fourier transforms of scalar fields, `W0 = L²(ℝ³_ξ; ℂ)`. -/
abbrev L2R := Lp ℂ 2 (volume : Measure Freq)
/-- Fourier transforms of symmetric-matrix fields, `W1 = L²(ℝ³_ξ; S)`. -/
abbrev L2S := Lp Sym3 2 (volume : Measure Freq)
/-- Fourier transforms of trace-free-matrix fields, `W2 = L²(ℝ³_ξ; T)`. -/
abbrev L2T := Lp Tr3 2 (volume : Measure Freq)

/-- `grad grad : H²(R) → L²(S)` on `ℝ³` (Fourier side). -/
def hessW : L2R →ₗ.[ℝ] L2S := mulOp volume fun ξ => hessS (freqW ξ)
/-- `curl : H(curl, S) → L²(T)` on `ℝ³` (Fourier side). -/
def curlSW : L2S →ₗ.[ℝ] L2T := mulOp volume fun ξ => curlS (freqW ξ)
/-- `H(curl, S)`. -/
def HcurlS : Submodule ℝ L2S := mulDomain volume fun ξ => curlS (freqW ξ)
/-- `H(div div, S)`. -/
def HdivdivS : Submodule ℝ L2S := mulDomain volume fun ξ => divdivS (freqW ξ)
/-- `H(sym curl, T)`. -/
def HsymCurlT : Submodule ℝ L2T := mulDomain volume fun ξ => symCurlS (freqW ξ)
/-- The `Ḣ¹(S)` condition `|2πξ| Â ∈ L²`. -/
def H1S : Submodule ℝ L2S :=
  mulDomain volume fun ξ => ‖freqW ξ‖ • ContinuousLinearMap.id ℝ Sym3
/-- `L²(TSD)` inside `L²(S)`. -/
abbrev L2TSDS : Submodule ℝ L2S := fibreSub volume fun ξ => tsdS (freqW ξ)
/-- `L²(TSD)` inside `L²(T)`. -/
abbrev L2TSDT : Submodule ℝ L2T := fibreSub volume fun ξ => tsdT (freqW ξ)

instance : L2TSDS.HasOrthogonalProjection :=
  hasOrthogonalProjection_fibreSub _ stronglyMeasurable_projS.aestronglyMeasurable

instance : L2TSDT.HasOrthogonalProjection :=
  hasOrthogonalProjection_fibreSub _ stronglyMeasurable_projT.aestronglyMeasurable

theorem coeFn_projS (A : L2S) :
    L2TSDS.starProjection A =ᵐ[volume] fun ξ => (tsdS (freqW ξ)).starProjection (A ξ) :=
  coeFn_starProjection_fibreSub _ stronglyMeasurable_projS.aestronglyMeasurable A

theorem coeFn_projT (ρ : L2T) :
    L2TSDT.starProjection ρ =ᵐ[volume] fun ξ => (tsdT (freqW ξ)).starProjection (ρ ξ) :=
  coeFn_starProjection_fibreSub _ stronglyMeasurable_projT.aestronglyMeasurable ρ

theorem coeFn_hessW (u : hessW.domain) :
    hessW u =ᵐ[volume] fun ξ => hessS (freqW ξ) ((u : L2R) ξ) := coeFn_mulOp _ _ u

theorem coeFn_curlSW (u : curlSW.domain) :
    curlSW u =ᵐ[volume] fun ξ => curlS (freqW ξ) ((u : L2S) ξ) := coeFn_mulOp _ _ u

/-- The domain of `(grad grad)*` is `H(div div, S)`. -/
theorem adjoint_hessW_domain : hessW†.domain = HdivdivS := by
  ext A
  rw [hessW, mem_adjoint_mulOp_domain stronglyMeasurable_hessW]
  simp only [adjoint_hessS]; rfl

/-- `(grad grad)* = div div` fibrewise. -/
theorem coeFn_adjoint_hessW (y : hessW†.domain) :
    hessW† y =ᵐ[volume] fun ξ => divdivS (freqW ξ) ((y : L2S) ξ) := by
  have h := coeFn_adjoint_mulOp stronglyMeasurable_hessW y
  simp only [adjoint_hessS] at h
  exact h

/-- The domain of `curl*` is `H(sym curl, T)`. -/
theorem adjoint_curlSW_domain : curlSW†.domain = HsymCurlT := by
  ext A
  rw [curlSW, mem_adjoint_mulOp_domain stronglyMeasurable_curlSW]
  simp only [adjoint_curlS]; rfl

/-- **`curl* = sym curl`** fibrewise. -/
theorem coeFn_adjoint_curlSW (y : curlSW†.domain) :
    curlSW† y =ᵐ[volume] fun ξ => symCurlS (freqW ξ) ((y : L2T) ξ) := by
  have h := coeFn_adjoint_mulOp stronglyMeasurable_curlSW y
  simp only [adjoint_curlS] at h
  exact h

/-- **The strong-symmetry complex (4.16) on `ℝ³`**
`H²(R) --grad grad--> H(curl, S) --curl--> L²(T)`, on the Fourier side.
See [QuennevilleBelair2015, §4.11, (4.16)]; cf. [ArnoldHu2021]. -/
def symWComplex : HilbertComplex2 L2R L2S L2T where
  d0 := hessW
  d1 := curlSW
  dense0 := dense_mulDomain stronglyMeasurable_hessW
  dense1 := dense_mulDomain stronglyMeasurable_curlSW
  closed0 := isClosed_mulOp stronglyMeasurable_hessW
  closed1 := isClosed_mulOp stronglyMeasurable_curlSW
  map_mem x := by
    change MemLp _ 2 volume
    refine (MemLp.zero (ε := Tr3)).ae_eq ?_
    filter_upwards [coeFn_hessW x] with ξ h
    change (0 : Tr3) = curlS (freqW ξ) ((hessW x : L2S) ξ)
    rw [h]
    exact (Subtype.ext (curlSym_hessM _ _)).symm
  comp_zero x := by
    refine (Lp.eq_zero_iff_ae_eq_zero).2 ?_
    filter_upwards [coeFn_curlSW ⟨hessW x, _⟩, coeFn_hessW x] with ξ h1 h2
    rw [h1]
    change curlS (freqW ξ) ((hessW x : L2S) ξ) = 0
    rw [h2]
    exact Subtype.ext (curlSym_hessM _ _)

/-- `L²(TSD) ⊆ H(div div, S)`. -/
theorem L2TSDS_le_HdivdivS : L2TSDS ≤ HdivdivS := fun A hA => by
  change MemLp _ 2 volume
  refine (MemLp.zero (ε := ℂ)).ae_eq ?_
  filter_upwards [hA] with ξ h
  exact (divdivS_eq_zero h).symm

/-- `L²(TSD) ⊆ ker div div` (`hS1` of `prop_4_17`). -/
theorem L2TSDS_le_ker : L2TSDS ≤ symWComplex.d0†.ker := by
  intro A hA
  change A ∈ hessW†.ker
  have hdom : A ∈ hessW†.domain := adjoint_hessW_domain ▸ L2TSDS_le_HdivdivS hA
  refine LinearPMap.mem_ker_iff.2 ⟨⟨A, hdom⟩, rfl, ?_⟩
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [coeFn_adjoint_hessW ⟨A, hdom⟩, hA] with ξ h1 h2
  rw [h1]; exact divdivS_eq_zero h2

/-- `curl` maps `H(curl, S) ∩ L²(TSD)` into `L²(TSD)` (`hd1`; Lemma 3.5). -/
theorem curlSW_mem_L2TSDT (u : symWComplex.d1.domain) (hu : (u : L2S) ∈ L2TSDS) :
    symWComplex.d1 u ∈ L2TSDT := by
  change curlSW u ∈ L2TSDT
  refine mem_fibreSub.2 ?_
  filter_upwards [coeFn_curlSW u, hu] with ξ h1 h2
  rw [h1]; exact curlSym_mem_tsd h2

/-- `curl* = sym curl` maps `H(sym curl, T) ∩ L²(TSD)` into `L²(TSD)` (`hd1s`). -/
theorem adjoint_curlSW_mem_L2TSDS (ρ : symWComplex.d1†.domain) (hρ : (ρ : L2T) ∈ L2TSDT) :
    symWComplex.d1† ρ ∈ L2TSDS := by
  change curlSW† ρ ∈ L2TSDS
  refine mem_fibreSub.2 ?_
  filter_upwards [coeFn_adjoint_curlSW ρ, hρ] with ξ h1 h2
  rw [h1]
  change ((symCurlS (freqW ξ) ((ρ : L2T) ξ) : Sym3) : Mat3) ∈ tsd (freqW ξ)
  rw [coe_symCurlS]
  exact symM_mem_tsd (curlSym_mem_tsd h2)

/-- `P_TSD H(curl, S) ⊆ H(curl, S)`. -/
theorem projS_mem_HcurlS {A : L2S} (hA : A ∈ HcurlS) : L2TSDS.starProjection A ∈ HcurlS := by
  refine MemLp.of_le hA (aestronglyMeasurable_apply
    stronglyMeasurable_curlSW.aestronglyMeasurable (Lp.aestronglyMeasurable _)) ?_
  filter_upwards [coeFn_projS A] with ξ h
  rw [h]
  exact norm_curlS_projS_le _ _

/-- `P_TSD H(curl, S) ⊆ Ḣ¹(S)`. -/
theorem projS_mem_H1S {A : L2S} (hA : A ∈ HcurlS) : L2TSDS.starProjection A ∈ H1S := by
  refine MemLp.of_le hA (aestronglyMeasurable_apply
    stronglyMeasurable_normS.aestronglyMeasurable (Lp.aestronglyMeasurable _)) ?_
  filter_upwards [coeFn_projS A] with ξ h
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, norm_smul, norm_norm]
  rw [h]
  exact norm_freq_mul_norm_projS_le _ _

/-- `P_TSD H(sym curl, T) ⊆ H(sym curl, T)`. -/
theorem projT_mem_HsymCurlT {ρ : L2T} (hρ : ρ ∈ HsymCurlT) :
    L2TSDT.starProjection ρ ∈ HsymCurlT := by
  refine MemLp.of_le hρ (aestronglyMeasurable_apply
    stronglyMeasurable_symCurlW.aestronglyMeasurable (Lp.aestronglyMeasurable _)) ?_
  filter_upwards [coeFn_projT ρ] with ξ h
  rw [h]
  exact norm_symCurlS_projT_le _ _

/-- `P_TSD (H(curl, S) ∩ H(div div, S)) ⊆ H(curl, S) ∩ H(div div, S)` (first hypothesis of
Prop 4.19). -/
theorem projS_mem_HcurlS_HdivdivS {A : L2S} (hA : A ∈ HcurlS ⊓ HdivdivS) :
    L2TSDS.starProjection A ∈ HcurlS ⊓ HdivdivS :=
  ⟨projS_mem_HcurlS hA.1, L2TSDS_le_HdivdivS (L2TSDS.starProjection_apply_mem A)⟩

/-- **The projection hypothesis of Prop 4.19 holds on `ℝ³`** (`hPD` of `prop_4_17`):
`P_K D(L) ⊆ D(L)` for `K = {0} × L²(TSD) × L²(TSD)`,
`D(L) = H²(R) × (H(curl, S) ∩ H(div div, S)) × H(sym curl, T)`.
See [QuennevilleBelair2015, §4.11, Prop 4.19]. -/
theorem projKc_mem_domL : ∀ x ∈ symWComplex.domL,
    projKc L2R L2TSDS L2TSDT x ∈ symWComplex.domL := by
  intro x hx
  rw [Constraints.mem_domL] at hx ⊢
  rw [tot_projKc]
  refine ⟨symWComplex.d0.domain.zero_mem, ⟨projS_mem_HcurlS hx.2.1.1, ?_⟩, ?_⟩
  · exact (LinearPMap.mem_ker_iff.1 (L2TSDS_le_ker (L2TSDS.starProjection_apply_mem _))).elim
      fun y hy => hy.1 ▸ y.2
  · have hd : symWComplex.d1†.domain = HsymCurlT := adjoint_curlSW_domain
    have h : (tot L2R L2S L2T x).2.2 ∈ HsymCurlT := hd.le hx.2.2
    exact hd.ge (projT_mem_HsymCurlT h)

/-- `D(L)` for TSD data: `(0, E₀, B₀) ∈ D(L)` iff `E₀ ∈ H(curl, S)` and `B₀ ∈ H(sym curl, T)`. -/
theorem ini_mem_domL_iff_of_TSD {E₀ : L2S} {B₀ : L2T} (hE₀ : E₀ ∈ L2TSDS) :
    ini L2R E₀ B₀ ∈ symWComplex.domL ↔ E₀ ∈ HcurlS ∧ B₀ ∈ HsymCurlT := by
  have h2 : symWComplex.d1†.domain = HsymCurlT := adjoint_curlSW_domain
  have h1 : symWComplex.midDomain = HcurlS ⊓ HdivdivS := by
    rw [midDomain]
    change HcurlS ⊓ hessW†.domain = _
    rw [adjoint_hessW_domain]
  rw [Constraints.mem_domL, tot_ini, h1, h2]
  simp only [Submodule.zero_mem, true_and, Submodule.mem_inf]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, L2TSDS_le_HdivdivS hE₀⟩, h.2⟩⟩

end Complex

section Prop419

/-- **Thesis Prop 4.19 on `ℝ³`, unconditional.** For the strong-symmetry complex (4.16) on
`ℝ³`, `H²(R) → H(curl, S) → L²(T)`, and its Hodge wave (4.18) (`ξ' = -L ξ`:
`σ' = div div E`, `E' = -grad grad σ - sym curl B`, `B' = curl E`), every strong solution with
data `(0, E₀, B₀)`, `E₀, B₀ ∈ L²(TSD)`, keeps `σ ≡ 0` and `E, B ∈ L²(TSD)` for all
`t ∈ [0, T]`, and `(E, B)` solves the reduced system.

Correction: the thesis states Prop 4.19 on a bounded domain under projection and density
conjectures; there it fails (`Feec.BoundedSym.symComplexB_not_propagate_unconditional`). On `ℝ³`
(no boundary) the projection hypotheses are theorems (`projS_mem_HcurlS_HdivdivS`,
`projT_mem_HsymCurlT`) and the density ones are unnecessary (`Feec.Constraints.prop_4_17`).
See [QuennevilleBelair2015, §4.11, Prop 4.19]; cf. [ACBY1997], [ArnoldHu2021]. -/
theorem prop_4_19_whole {T : ℝ} {E₀ : L2S} {B₀ : L2T} {U : ℝ → Tot L2R L2S L2T}
    (hE₀ : E₀ ∈ L2TSDS) (hB₀ : B₀ ∈ L2TSDT)
    (hU : IsStrongSolution (-symWComplex.waveOp) T (ini L2R E₀ B₀) 0 U) :
    (∀ t ∈ Icc 0 T, U t ∈ Kc L2R L2TSDS L2TSDT) ∧
      IsReducedSolution symWComplex T E₀ B₀ (fun t => (tot L2R L2S L2T (U t)).2.1)
        (fun t => (tot L2R L2S L2T (U t)).2.2) :=
  prop_4_17 L2TSDS_le_ker projKc_mem_domL curlSW_mem_L2TSDT adjoint_curlSW_mem_L2TSDS hE₀ hB₀ hU

/-- **Thesis Prop 4.19 on `ℝ³`, with existence.** For TSD data `E₀ ∈ L²(TSD) ∩ H(curl, S)`,
`B₀ ∈ L²(TSD) ∩ H(sym curl, T)`, (4.18) has a solution in `C⁰([0,T]; D(L)) ∩ C¹([0,T]; X)`
(Stone's theorem), unique among strong solutions, that stays in `K` and solves the reduced
system. See [QuennevilleBelair2015, §4.11, Prop 4.19, Thm 4.3]. -/
theorem prop_4_19_whole_exists (T : ℝ) {E₀ : L2S} {B₀ : L2T} (hE₀ : E₀ ∈ L2TSDS)
    (hB₀ : B₀ ∈ L2TSDT) (hE₀c : E₀ ∈ HcurlS) (hB₀c : B₀ ∈ HsymCurlT) :
    ∃ U, IsClassicalSolution (-symWComplex.waveOp) T (ini L2R E₀ B₀) 0 U ∧
      (∀ t ∈ Icc 0 T, U t ∈ Kc L2R L2TSDS L2TSDT) ∧
      IsReducedSolution symWComplex T E₀ B₀ (fun t => (tot L2R L2S L2T (U t)).2.1)
        (fun t => (tot L2R L2S L2T (U t)).2.2) ∧
      ∀ U', IsStrongSolution (-symWComplex.waveOp) T (ini L2R E₀ B₀) 0 U' →
        EqOn U' U (Icc 0 T) :=
  prop_4_17_exists_unconditional L2TSDS_le_ker projKc_mem_domL curlSW_mem_L2TSDT
    adjoint_curlSW_mem_L2TSDS T hE₀ hB₀ ((ini_mem_domL_iff_of_TSD hE₀).2 ⟨hE₀c, hB₀c⟩)

/-- **Prop 4.19 on `ℝ³`, group form for all times**: the Stone group `e^{-tL}` of
`symWComplex` maps `D(L) ∩ K` into `K` for every `t ∈ ℝ`. -/
theorem prop_4_19_whole_group (t : ℝ) {x : Tot L2R L2S L2T} (hx : x ∈ symWComplex.domL)
    (hxK : x ∈ Kc L2R L2TSDS L2TSDT) : symWComplex.waveGroup.S t x ∈ Kc L2R L2TSDS L2TSDT :=
  prop_4_17_group_all_unconditional L2TSDS_le_ker projKc_mem_domL curlSW_mem_L2TSDT
    adjoint_curlSW_mem_L2TSDS t hx hxK

end Prop419

end Feec.WholeSym
