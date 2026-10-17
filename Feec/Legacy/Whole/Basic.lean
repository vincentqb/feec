module

public import Mathlib.Analysis.Fourier.LpSpace
public import Feec.Legacy.Whole.Mul
public import Feec.Legacy.Torus.Basic
public import Feec.Legacy.WeakSolution

/-!
# Thesis Prop 4.17 on the whole space `ℝ³`

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use. It
keeps only what those modules need and the results that have no home in the general layers
yet; everything else moved there (see `docs/migration/map.tsv`).

Props 4.17/4.19 ([QuennevilleBelair2015, §4.10–4.11]) propagate the TSD constraint
(symmetric, trace-free, divergence-free) for the matrix Hodge wave (4.14). The thesis poses them
on a bounded domain, where they fail (`Feec.Legacy.BoundedDomain.Basic`, `Feec.Legacy.BoundedDomain.Sym`), and
`Feec.Legacy.Torus.Basic` proves them on the flat torus `𝕋³`. This file proves Prop 4.17 on the whole
space `ℝ³`, with no boundary: the physically natural setting of an isolated source.

## Model

Fields are modelled by their Fourier transforms: `L2V = L²(ℝ³_ξ; ℂ³)` and
`L2M = L²(ℝ³_ξ; ℂ³ˣ³)` (Lebesgue measure), as real Hilbert spaces (inner product `Re ⟨·,·⟩`).
The ambient spaces are identified with physical `L²` fields by Plancherel's theorem, Mathlib's
`MeasureTheory.Lp.fourierTransformₗᵢ` (`fieldFourierW`, `vectorFourierW`, `matrixFourierW`),
which is the Fourier transform `𝓕 f (ξ) = ∫ e^{-2πi ⟪x, ξ⟫} f x dx` on Schwartz fields
(`fieldFourierW_toLp`) and preserves the real inner product (`inner_fieldFourierW`). With this
convention `∂_c ↦ 2πi ξ_c`, so the operators are multiplication operators by the symbols of
`Feec.Legacy.Torus.Basic` at `freqW ξ = 2πξ`: `grad u ↦ i û (2πξ)ᵀ` (`gradW`), row-wise
`curl A ↦ i (2πξ × Â_a)_a` (`curlW`, the thesis' convention as in `Feec.Legacy.curl`), `div A ↦ i Â (2πξ)`
(`Hdiv`). The spaces `H¹`, `H(curl)`, `H(div)` are the corresponding weighted-`L²` conditions
(`Feec.Legacy.Whole.mulDomain`, `Feec.Legacy.Whole.Mul`); `L²(TSD)` is the fibrewise subspace
`{Â(ξ) ∈ tsd (2πξ) a.e.}` (`L2TSD`). These Fourier-side definitions are identified with the
physical (weak-derivative) ones in companion files: `H(curl)` in `Feec.Legacy.Whole.Weak`
(`Feec.Models.Euclidean.GradCurl.mem_domain_curl_iff_weak`), `H¹` and `H(div)` in `Feec.Legacy.Whole.Ident`
(`Feec.Models.Euclidean.GradCurl.mem_domain_grad_iff_weak`, `Feec.Legacy.WholeIdent.mem_Hdiv_iff_weak`), and `L²(TSD)` as the
space of symmetric, trace-free, weakly divergence-free `L²` fields
(`Feec.Legacy.WholeIdent.fourier_mem_L2TSD_iff`). Weak derivatives are tested against Schwartz fields.
As on `𝕋³`, the theorems here are stated for complex-valued fields viewed as a real Hilbert
space. `Feec.Fourier.Reality` restricts the complex to real-valued fields
(`Â(-ξ) = conj Â(ξ)`, `Feec.Fourier.Weak.fourier_fixed_iff`) and proves Prop 4.17 there, with
existence (`Feec.Models.Euclidean.GradCurl.real_tsd_existsUnique`).

## Main results

* The fibre projection `ξ ↦ P_ξ` onto `tsd ξ` is strongly measurable
  (`stronglyMeasurable_projTSD`): `tsd ξ` is the kernel of the continuous positive family
  `tsdOp ξ` (`tsd_eq_ker`), and `Feec.Legacy.Whole.stronglyMeasurable_starProjection_ker` applies. So
  `P_TSD` acts fibrewise (`coeFn_projTSD`), exactly as on `𝕋³`.
* `wholeComplex : HilbertComplex2 L2V L2M L2M`, the complex `H¹(V) → H(curl; M) → L²(M)` on
  `ℝ³`: closed and densely defined (generic multiplier theory), `curl ∘ grad = 0`;
  `adjoint_curlW` (`curl* = curl`), `adjoint_gradW_domain` (`D(grad*) = H(div)`),
  `coeFn_adjoint_gradW` (`grad* = -div`).
* All hypotheses of `Feec.Legacy.Constraints.Kc_propagates` for `S1 = S2 = L²(TSD)`: `L2TSD_le_ker`,
  `projKc_mem_domL` (the projection hypothesis, from `projTSD_mem_Hcurl`), `curlW_mem_L2TSD`
  (Lemma 3.5), `adjoint_curlW_mem_L2TSD`; also `Feec.Models.Euclidean.GradCurl.reducingSubcomplex` (`P_TSD H(curl) ⊆ Ḣ¹`) and
  `Feec.Models.Euclidean.GradCurl.reducingSubcomplex` (`curl P_TSD = P_TSD curl`).
* Prop 4.19 on `ℝ³` (complex (4.16)) is `Feec.Models.Euclidean.SymCurl.tsd_propagates_neg` in `Feec.Models.Euclidean.SymCurl`.
* **`whole_Kc_propagates`** (every strong solution with TSD data propagates the constraints and
  solves (4.15)), **`Feec.Models.Euclidean.GradCurl.tsd_existsUnique`** (existence and uniqueness of a classical solution
  for TSD data in `H(curl)`, via Stone's theorem: `Feec.Legacy.Constraints.existsUnique_classicalSolution_mem_Kc`)
  and `Feec.Models.Euclidean.GradCurl.waveGroup_mem` (the Stone group preserves `D(L) ∩ K` for all `t ∈ ℝ`).
* Remark: the complex is **not closed** (`Feec.Models.Euclidean.GradCurl.not_closedRangeAt_one`,
  `Feec.Models.Euclidean.GradCurl.not_closedRangeAt_one`): `grad` is injective on `L²(ℝ³)` (`ker_gradW`) but has no
  Poincaré inequality (low frequencies). The range of `curl` is not closed either
  (`Feec.Models.Euclidean.GradCurl.not_closedRangeAt_two`). Neither Prop 4.17 nor the existence theory needs
  closed range.

## Correction

As on `𝕋³`, the thesis' "conjecture" `P_{L²(TSD)} D(L) ⊆ D(L)` is a theorem on `ℝ³`, in the
stronger form `P_TSD H(curl) ⊆ H(curl) ∩ Ḣ¹` with `curl P_TSD = P_TSD curl`, and the density
conjectures are unnecessary. The propagation mechanism is the fibrewise commutation of `P_TSD`
with the curl symbol (`Feec.Legacy.Torus.proj_curlSym`), the same on `𝕋³` and `ℝ³`. Interpretation (not
a theorem): together with the bounded-domain counterexamples (`Feec.Legacy.BoundedDomain.Basic`) and the
box with mirror boundary conditions, where Prop 4.17 holds (`Feec.Models.Cube.Mirror.existsUnique_mem`),
this indicates that the bounded-domain failure comes from the thesis' boundary conditions. Unlike
the torus, `grad` is injective on `ℝ³` (`ker_gradW`: no constant mode), but the complex does not
have closed range.

## References

* [QuennevilleBelair2015], §3.4 (Lemma 3.5), §4.10 (Prop 4.17, (4.14), (4.15)), §4.3 (Thm 4.3)
* [ACBY1997] (the Einstein–Bianchi system)
* [AFW2010], [Arnold2018], [BruningLesch1992] (Hilbert complexes)
* [Pazy1983], §1.10 (unitary groups and Stone's theorem)
* Mathlib, `Mathlib.Analysis.Fourier.LpSpace` (the `L²` Fourier transform, Plancherel)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace ENNReal Topology
open MeasureTheory LinearPMap Set Filter

namespace Feec.Legacy.Whole

open Feec.Legacy.Torus HilbertComplex2 Constraints

section Symbols

/-- A map out of `ℝ³` that is additive and homogeneous is continuous. -/
theorem continuous_of_linear {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : Freq → X} (hadd : ∀ ξ η, f (ξ + η) = f ξ + f η)
    (hsmul : ∀ (r : ℝ) ξ, f (r • ξ) = r • f ξ) : Continuous f :=
  LinearMap.continuous_of_finiteDimensional
    ({ toFun := f, map_add' := hadd, map_smul' := hsmul } : Freq →ₗ[ℝ] X)

/-- The angular frequency `2π ξ` of the mode `e^{2πi x·ξ}` (Mathlib's convention for the Fourier
transform, `𝓕 f (ξ) = ∫ e^{-2πi ⟪x, ξ⟫} f x dx`). -/
def freqW (ξ : Freq) : Freq := (2 * Real.pi) • ξ

theorem continuous_freqW : Continuous freqW := by
  unfold freqW; exact (continuous_const (y := (2 * Real.pi : ℝ))).smul continuous_id

theorem continuous_gradSym : Continuous gradSym := by
  refine continuous_clm_apply.2 fun u => continuous_of_linear (fun ξ η => ?_) (fun r ξ => ?_)
  · ext ⟨a, b⟩; simp [gradSym_apply]; ring
  · ext ⟨a, b⟩; simp [gradSym_apply, Complex.real_smul]; ring

theorem continuous_curlSym : Continuous curlSym := by
  refine continuous_clm_apply.2 fun M => continuous_of_linear (fun ξ η => ?_) (fun r ξ => ?_)
  · ext ⟨a, b⟩
    fin_cases b <;> simp [curlSym_apply, jM_apply, curlR_apply, cross] <;> ring
  · ext ⟨a, b⟩
    fin_cases b <;> simp [curlSym_apply, jM_apply, curlR_apply, cross, Complex.real_smul] <;> ring

theorem continuous_divSym : Continuous divSym := by
  refine continuous_clm_apply.2 fun M => continuous_of_linear (fun ξ η => ?_) (fun r ξ => ?_)
  · ext a; simp [divSym_apply, Fin.sum_univ_three]; ring
  · ext a; simp [divSym_apply, Fin.sum_univ_three, Complex.real_smul]; ring

theorem continuous_divR : Continuous divR := by
  refine continuous_clm_apply.2 fun M => continuous_of_linear (fun ξ η => ?_) (fun r ξ => ?_)
  · ext a; simp [divR_apply, Fin.sum_univ_three]; ring
  · ext a; simp [divR_apply, Fin.sum_univ_three, Complex.real_smul]; ring

theorem stronglyMeasurable_gradW : StronglyMeasurable fun ξ => gradSym (freqW ξ) :=
  (continuous_gradSym.comp continuous_freqW).stronglyMeasurable

theorem stronglyMeasurable_curlW : StronglyMeasurable fun ξ => curlSym (freqW ξ) :=
  (continuous_curlSym.comp continuous_freqW).stronglyMeasurable

end Symbols

section TSDProj

/-- A positive symmetric operator with kernel `tsd ξ`: the projection onto the complement of
the symmetric trace-free matrices plus `divR ξ* divR ξ`. -/
def tsdOp (ξ : Freq) : Mat3 →L[ℝ] Mat3 :=
  (tsd 0)ᗮ.starProjection + (ContinuousLinearMap.adjoint (divR ξ)).comp (divR ξ)

theorem inner_starProjection_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] (x : E) :
    ⟪K.starProjection x, x⟫ = ‖K.starProjection x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  conv_rhs => rw [Submodule.inner_starProjection_left_eq_right,
    K.starProjection_eq_self_iff.2 (K.starProjection_apply_mem x)]
  exact Submodule.inner_starProjection_left_eq_right _ _ _

theorem inner_tsdOp_self (ξ : Freq) (M : Mat3) :
    ⟪tsdOp ξ M, M⟫ = ‖(tsd 0)ᗮ.starProjection M‖ ^ 2 + ‖divR ξ M‖ ^ 2 := by
  rw [tsdOp, _root_.add_apply, inner_add_left, inner_starProjection_self,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    real_inner_self_eq_norm_sq]

theorem tsdOp_symm (ξ : Freq) (M N : Mat3) : ⟪tsdOp ξ M, N⟫ = ⟪M, tsdOp ξ N⟫ := by
  rw [tsdOp, _root_.add_apply, _root_.add_apply, inner_add_left, inner_add_right,
    Submodule.inner_starProjection_left_eq_right, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]

theorem tsdOp_pos (ξ : Freq) (M : Mat3) : 0 ≤ ⟪tsdOp ξ M, M⟫ := by
  rw [inner_tsdOp_self]; positivity

theorem mem_tsd_iff_tsdOp {ξ : Freq} {M : Mat3} : M ∈ tsd ξ ↔ tsdOp ξ M = 0 := by
  constructor
  · intro hM
    have h0 : M ∈ tsd 0 := mem_tsd_zero.2 ⟨hM.1, hM.2.1⟩
    have h1 : (tsd 0)ᗮ.starProjection M = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff _).2 (Submodule.le_orthogonal_orthogonal _ h0)
    rw [tsdOp, _root_.add_apply, h1, ContinuousLinearMap.comp_apply,
      divR_eq_zero_of_mem_tsd hM, _root_.map_zero, add_zero]
  · intro h
    have h2 := inner_tsdOp_self ξ M
    rw [h, inner_zero_left] at h2
    have ha := sq_nonneg ‖(tsd 0)ᗮ.starProjection M‖
    have hb := sq_nonneg ‖divR ξ M‖
    have hP : (tsd 0)ᗮ.starProjection M = 0 := by
      have : ‖(tsd 0)ᗮ.starProjection M‖ ^ 2 = 0 := by linarith
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
    have hD : divR ξ M = 0 := by
      have : ‖divR ξ M‖ ^ 2 = 0 := by linarith
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
    have h0 : M ∈ tsd 0 := by
      have := (Submodule.starProjection_apply_eq_zero_iff _).1 hP
      rwa [Submodule.orthogonal_orthogonal] at this
    obtain ⟨hs, ht⟩ := mem_tsd_zero.1 h0
    refine ⟨hs, ht, fun a => ?_⟩
    have := congrArg (fun v : Vec3 => v a) hD
    simpa [divR_apply] using this

/-- `tsd ξ` is the kernel of the positive operator `tsdOp ξ`. -/
theorem tsd_eq_ker (ξ : Freq) : tsd ξ = LinearMap.ker (tsdOp ξ : Mat3 →ₗ[ℝ] Mat3) := by
  ext M; rw [mem_tsd_iff_tsdOp]; rfl

theorem continuous_tsdOp : Continuous tsdOp :=
  continuous_const.add
    (((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Mat3) (F := Vec3)).continuous.comp
      continuous_divR).clm_comp continuous_divR)

/-- **The TSD fibre projection `ξ ↦ P_ξ` is strongly measurable** (it is discontinuous at
`ξ = 0`, where the fibre jumps from dimension 4 to 10). -/
theorem stronglyMeasurable_projTSD :
    StronglyMeasurable fun ξ => (tsd (freqW ξ)).starProjection := by
  have h := stronglyMeasurable_starProjection_ker (H := fun ξ => tsdOp (freqW ξ))
    (continuous_tsdOp.comp continuous_freqW) (fun ξ => tsdOp_symm (freqW ξ))
    (fun ξ => tsdOp_pos (freqW ξ))
  simp only [← tsd_eq_ker] at h
  exact h

end TSDProj

section Complex

/-- Fourier transforms of vector fields on `ℝ³`: `L²(ℝ³_ξ; ℂ³)` (real Hilbert space). -/
abbrev L2V := Lp Vec3 2 (volume : Measure Freq)
/-- Fourier transforms of matrix fields on `ℝ³`: `L²(ℝ³_ξ; ℂ³ˣ³)` (real Hilbert space). -/
abbrev L2M := Lp Mat3 2 (volume : Measure Freq)

/-- The gradient `H¹(ℝ³; V) → L²(ℝ³; M)` on the Fourier side: `û ↦ i û (2πξ)ᵀ`. -/
def gradW : L2V →ₗ.[ℝ] L2M := mulOp volume fun ξ => gradSym (freqW ξ)
/-- The row-wise curl on the Fourier side: `Â ↦ i (2πξ × Â_a)_a`. -/
def curlW : L2M →ₗ.[ℝ] L2M := mulOp volume fun ξ => curlSym (freqW ξ)
/-- `H(curl; M)` on `ℝ³`. -/
def Hcurl : Submodule ℝ L2M := mulDomain volume fun ξ => curlSym (freqW ξ)
/-- `H(div; M)` on `ℝ³` (row-wise divergence). -/
def Hdiv : Submodule ℝ L2M := mulDomain volume fun ξ => divSym (freqW ξ)
/-- `L²(TSD)` on `ℝ³`: fields whose Fourier transform lies a.e. in the TSD fibre
`tsd (2πξ) = {M | Mᵀ = M, tr M = 0, M ξ = 0}`. -/
abbrev L2TSD : Submodule ℝ L2M := fibreSub volume fun ξ => tsd (freqW ξ)

instance : L2TSD.HasOrthogonalProjection :=
  hasOrthogonalProjection_fibreSub _ stronglyMeasurable_projTSD.aestronglyMeasurable

/-- `P_TSD` acts fibrewise by `P_ξ`. -/
theorem coeFn_projTSD (A : L2M) :
    L2TSD.starProjection A =ᵐ[volume] fun ξ => (tsd (freqW ξ)).starProjection (A ξ) :=
  coeFn_starProjection_fibreSub _ stronglyMeasurable_projTSD.aestronglyMeasurable A

theorem coeFn_gradW (u : gradW.domain) :
    gradW u =ᵐ[volume] fun ξ => gradSym (freqW ξ) ((u : L2V) ξ) := coeFn_mulOp _ _ u

theorem coeFn_curlW (u : curlW.domain) :
    curlW u =ᵐ[volume] fun ξ => curlSym (freqW ξ) ((u : L2M) ξ) := coeFn_mulOp _ _ u

/-- `curl* = curl` on `ℝ³`. -/
theorem adjoint_curlW : curlW† = curlW := by
  rw [curlW, adjoint_mulOp stronglyMeasurable_curlW]; simp only [adjoint_curlSym]

/-- The domain of `grad*` is `H(div)`. -/
theorem adjoint_gradW_domain : gradW†.domain = Hdiv := by
  ext A
  rw [gradW, mem_adjoint_mulOp_domain stronglyMeasurable_gradW]
  simp only [adjoint_gradSym, _root_.neg_apply]
  exact memLp_neg_iff (f := fun ξ => divSym (freqW ξ) (A ξ))

/-- `grad* = -div` fibrewise. -/
theorem coeFn_adjoint_gradW (y : gradW†.domain) :
    gradW† y =ᵐ[volume] fun ξ => -divSym (freqW ξ) ((y : L2M) ξ) := by
  have h := coeFn_adjoint_mulOp stronglyMeasurable_gradW y
  simp only [adjoint_gradSym, _root_.neg_apply] at h
  exact h

/-- `curl*` acts fibrewise by the curl symbol. -/
theorem coeFn_adjoint_curlW (ρ : curlW†.domain) :
    curlW† ρ =ᵐ[volume] fun ξ => curlSym (freqW ξ) ((ρ : L2M) ξ) := by
  have h := coeFn_adjoint_mulOp stronglyMeasurable_curlW ρ
  simp only [adjoint_curlSym] at h
  exact h

/-- **The whole-space matrix complex** `H¹(V) --grad--> H(curl; M) --curl--> L²(M)` on `ℝ³`,
on the Fourier side. -/
def wholeComplex : HilbertComplex2 L2V L2M L2M where
  d0 := gradW
  d1 := curlW
  dense0 := dense_mulDomain stronglyMeasurable_gradW
  dense1 := dense_mulDomain stronglyMeasurable_curlW
  closed0 := isClosed_mulOp stronglyMeasurable_gradW
  closed1 := isClosed_mulOp stronglyMeasurable_curlW
  map_mem x := by
    change MemLp _ 2 volume
    refine (MemLp.zero (ε := Mat3)).ae_eq ?_
    filter_upwards [coeFn_gradW x] with ξ h
    change (0 : Mat3) = curlSym (freqW ξ) ((gradW x : L2M) ξ)
    rw [h, curlSym_gradSym]
  comp_zero x := by
    refine Lp.ext ?_
    filter_upwards [coeFn_curlW ⟨gradW x, _⟩, coeFn_gradW x,
      Lp.coeFn_zero Mat3 2 (volume : Measure Freq)] with ξ h1 h2 h3
    rw [h1, h3]
    change curlSym (freqW ξ) ((gradW x : L2M) ξ) = 0
    rw [h2, curlSym_gradSym]

/-- `L²(TSD) ⊆ H(div)`: TSD fields are divergence-free. -/
theorem L2TSD_le_Hdiv : L2TSD ≤ Hdiv := fun A hA => by
  change MemLp _ 2 volume
  refine (MemLp.zero (ε := Vec3)).ae_eq ?_
  filter_upwards [hA] with ξ h
  ext a
  simp [divSym_apply, h.2.2 a]

/-- `L²(TSD) ⊆ ker div` (`hS1` of `Kc_propagates`). -/
theorem L2TSD_le_ker : L2TSD ≤ wholeComplex.d0†.ker := by
  intro A hA
  change A ∈ gradW†.ker
  have hdom : A ∈ gradW†.domain := adjoint_gradW_domain ▸ L2TSD_le_Hdiv hA
  refine LinearPMap.mem_ker_iff.2 ⟨⟨A, hdom⟩, rfl, ?_⟩
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [coeFn_adjoint_gradW ⟨A, hdom⟩, hA] with ξ h1 h3
  rw [h1]
  ext a
  simp [divSym_apply, h3.2.2 a]

/-- `curl` maps `H(curl) ∩ L²(TSD)` into `L²(TSD)` (`hd1` of `Kc_propagates`; Lemma 3.5). -/
theorem curlW_mem_L2TSD (u : wholeComplex.d1.domain) (hu : (u : L2M) ∈ L2TSD) :
    wholeComplex.d1 u ∈ L2TSD := by
  change curlW u ∈ L2TSD
  refine mem_fibreSub.2 ?_
  filter_upwards [coeFn_curlW u, hu] with ξ h1 h2
  rw [h1]; exact curlSym_mem_tsd h2

/-- `curl* = curl` maps `L²(TSD)` into itself (`hd1s` of `Kc_propagates`). -/
theorem adjoint_curlW_mem_L2TSD (ρ : wholeComplex.d1†.domain) (hρ : (ρ : L2M) ∈ L2TSD) :
    wholeComplex.d1† ρ ∈ L2TSD := by
  change curlW† ρ ∈ L2TSD
  refine mem_fibreSub.2 ?_
  filter_upwards [coeFn_adjoint_curlW ρ, hρ] with ξ h1 h2
  rw [h1]; exact curlSym_mem_tsd h2

/-- `P_TSD H(curl) ⊆ H(curl)`. -/
theorem projTSD_mem_Hcurl {A : L2M} (hA : A ∈ Hcurl) : L2TSD.starProjection A ∈ Hcurl := by
  refine MemLp.of_le hA (aestronglyMeasurable_apply
    stronglyMeasurable_curlW.aestronglyMeasurable (Lp.aestronglyMeasurable _)) ?_
  filter_upwards [coeFn_projTSD A] with ξ h
  rw [h, ← proj_curlSym]
  exact Submodule.norm_starProjection_apply_le _ _

/-- **The projection hypothesis holds on `ℝ³`** (`hPD` of `Kc_propagates`):
`P_K D(L) ⊆ D(L)` for `K = {0} × L²(TSD) × L²(TSD)`, where
`D(L) = H¹(V) × (H(curl) ∩ H(div)) × H(curl)`.
See [QuennevilleBelair2015, §4.10, Prop 4.17]. -/
theorem projKc_mem_domL : ∀ x ∈ wholeComplex.domL,
    projKc L2V L2TSD L2TSD x ∈ wholeComplex.domL := by
  intro x hx
  rw [Constraints.mem_domL] at hx ⊢
  rw [tot_projKc]
  refine ⟨wholeComplex.d0.domain.zero_mem, ⟨projTSD_mem_Hcurl hx.2.1.1, ?_⟩, ?_⟩
  · exact (LinearPMap.mem_ker_iff.1 (L2TSD_le_ker (L2TSD.starProjection_apply_mem _))).elim
      fun y hy => hy.1 ▸ y.2
  · have h : (tot L2V L2M L2M x).2.2 ∈ curlW.domain := by
      have := hx.2.2; change _ ∈ curlW†.domain at this; rwa [adjoint_curlW] at this
    change _ ∈ curlW†.domain
    rw [adjoint_curlW]
    exact projTSD_mem_Hcurl h

end Complex

section Plancherel

variable (P : Type*) [Fintype P]

/-- **Plancherel**: the Fourier transform `L²(ℝ³; ℂᴾ) ≃ₗᵢ L²(ℝ³_ξ; ℂᴾ)`, Mathlib's
`MeasureTheory.Lp.fourierTransformₗᵢ` (the extension by density of the Fourier transform on
Schwartz functions, `fieldFourierW_toLp`). -/
def fieldFourierW : Lp (EuclideanSpace ℂ P) 2 (volume : Measure Freq) ≃ₗᵢ[ℂ]
    Lp (EuclideanSpace ℂ P) 2 (volume : Measure Freq) :=
  Lp.fourierTransformₗᵢ Freq (EuclideanSpace ℂ P)

/-- On Schwartz fields, `fieldFourierW` is the Fourier transform
`𝓕 f (ξ) = ∫ e^{-2πi ⟪x, ξ⟫} f x dx`. -/
theorem fieldFourierW_toLp (f : SchwartzMap Freq (EuclideanSpace ℂ P)) :
    fieldFourierW P (f.toLp 2) = (FourierTransform.fourier f).toLp 2 :=
  SchwartzMap.toLp_fourier_eq f

/-- `fieldFourierW` preserves the real inner product `Re ⟨·,·⟩` used throughout. -/
theorem inner_fieldFourierW (f g : Lp (EuclideanSpace ℂ P) 2 (volume : Measure Freq)) :
    ⟪fieldFourierW P f, fieldFourierW P g⟫ = ⟪f, g⟫ := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    ← _root_.map_add, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.norm_map]

/-- Vector fields: `L²(ℝ³; ℂ³) ≃ₗᵢ L2V`, the model of `W0`. -/
def vectorFourierW : Lp Vec3 2 (volume : Measure Freq) ≃ₗᵢ[ℂ] L2V := fieldFourierW (Fin 3)

/-- Matrix fields: `L²(ℝ³; ℂ³ˣ³) ≃ₗᵢ L2M`, the model of `W1 = W2`. -/
def matrixFourierW : Lp Mat3 2 (volume : Measure Freq) ≃ₗᵢ[ℂ] L2M :=
  fieldFourierW (Fin 3 × Fin 3)

end Plancherel

section Propagation

/-- **Thesis Prop 4.17 on `ℝ³`, unconditional.** For the whole-space matrix complex
`H¹(V) → H(curl; M) → L²(M)` and the Hodge wave (4.14) (`ξ' = -L ξ`), every strong solution
with data `(0, E₀, B₀)`, `E₀, B₀ ∈ L²(TSD)`, keeps `σ ≡ 0` and `E, B ∈ L²(TSD)` for all
`t ∈ [0, T]`, and `(E, B)` solves the reduced system (4.15). No projection or density hypothesis
is assumed: the projection hypothesis is proved (`projKc_mem_domL`), the density ones are
unnecessary (`Feec.Legacy.Constraints.Kc_propagates`).

Correction: the thesis works on a bounded domain with the boundary conditions of
`H̊¹(V) → H̊(curl; M) → L²(M)`, where both the projection conjecture and the conclusion fail
(`Feec.Legacy.BoundedDomain.thesisComplex_not_projection_hyp`,
`Feec.Legacy.BoundedDomain.thesisComplex_tsd_not_propagates`). This theorem is the
whole-space analogue (no boundary): an isolated source in `ℝ³`.
See [QuennevilleBelair2015, §4.10, Prop 4.17]; cf. [ACBY1997]. -/
theorem whole_Kc_propagates {T : ℝ} {E₀ B₀ : L2M} {U : ℝ → Tot L2V L2M L2M} (hE₀ : E₀ ∈ L2TSD)
    (hB₀ : B₀ ∈ L2TSD) (hU : IsStrongSolution (-wholeComplex.waveOp) T (ini L2V E₀ B₀) 0 U) :
    (∀ t ∈ Icc 0 T, U t ∈ Kc L2V L2TSD L2TSD) ∧
      IsReducedSolution wholeComplex T E₀ B₀ (fun t => (tot L2V L2M L2M (U t)).2.1)
        (fun t => (tot L2V L2M L2M (U t)).2.2) :=
  Kc_propagates L2TSD_le_ker projKc_mem_domL curlW_mem_L2TSD adjoint_curlW_mem_L2TSD hE₀ hB₀ hU

end Propagation

end Feec.Legacy.Whole
