module

public import Feec.Models.Cube.Ident
public import Feec.Models.Cube.Mirror
public import Feec.Models.BoundedDomain.InvariantCore
public import Feec.HilbertComplex.CompressCompact

/-!
# A complete set of eigenvectors on cubes, and `K*` for the thesis' complex on cubes

The wave groups of `H̊¹ → H̊(curl) → L²` and of the mirror complexes have a dense set of
eigenvectors on `Q = (0, ½)³` and on every open cube, which describes `K*` there.

## Main results

* `RowWise.gradCurl_coreSub_spectral_Q`, `Ident.gradCurl_coreSub_spectral_cube`: `K*`.
* `Mirror.eigenDense_complexQ`, `Mirror.eigenDense_complexCube`: the mirror complexes.
-/

open scoped InnerProductSpace
open Set LinearPMap MeasureTheory

@[expose] public noncomputable section

/-! ### Transport with a constant chain-rule factor -/

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W W' : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace 𝕜 (W' i)] [∀ i, CompleteSpace (W' i)]
  [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  [∀ i, NormedSpace ℝ (W' i)] [∀ i, IsScalarTower ℝ 𝕜 (W' i)]
  (H : HilbertComplex 𝕜 c W) {e : ∀ i, W i ≃L[𝕜] W' i} {s : ℝ}

theorem eigenDense_transport_const (hs : 0 < s)
    (he : ∀ i (x y : W i), ⟪e i x, e i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜) {κ : ℝ} (hκ : κ ≠ 0)
    (hD : H.waveGroup.EigenDense) :
    (H.transport e (fun _ _ => (κ : 𝕜)) fun _ _ => RCLike.ofReal_ne_zero.2 hκ).waveGroup.EigenDense := by
  unfold C0Group.EigenDense at hD ⊢
  rw [generator_waveGroup] at hD ⊢
  have hI := wave_transport_const H hs he hκ
  refine LinearPMap.dense_span_isEigenSq_of_map hD (totalMap e) surjective_totalMap.denseRange κ
    fun x => ⟨hI.mapsTo x, ?_⟩
  rw [hI.comm x, LinearPMap.smul_apply, _root_.map_smul]

end Feec.HilbertComplex

/-! ### The thesis' complex on `Q` and on every open cube -/

namespace Feec.Models.Cube.RowWise

open Models.BoundedDomain (Ix tsd tsd₀ gradCurl)
open Domain (L2F)
open Geometry (Q)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3

theorem eigenDense_cubeComplex : cubeComplex.waveGroup.EigenDense :=
  Box.eigenDense_complexBox (a := 0) (ℓ := fun _ => 1 / 2) fun _ => one_half_pos

theorem eigenDense_gradCurl_Q : (gradCurl ℝ Geometry.isOpen_Q).EigenDense :=
  eigenDense_cubeComplex

/-- **`K*` on `Q = (0, ½)³` for the thesis' complex**: its characterization by `coreSub`, and
`K*` consists of stationary data iff there is no nonzero TSD eigenfield. -/
theorem gradCurl_coreSub_spectral_Q :
    (∀ x, (∀ t, 0 ≤ t → (gradCurl ℝ Geometry.isOpen_Q).toHilbertComplex.waveGroup.S t x ∈
        HilbertComplex.totalSub
          (ShortHilbertComplex.family3 ⊥ (tsd (Q (Fin 3))) (tsd (Q (Fin 3))))) ↔
          x ∈ (gradCurl ℝ Geometry.isOpen_Q).coreSub (tsd (Q (Fin 3))) (tsd (Q (Fin 3)))) ∧
    ((gradCurl ℝ Geometry.isOpen_Q).coreSub (tsd (Q (Fin 3))) (tsd (Q (Fin 3))) ≤
        (gradCurl ℝ Geometry.isOpen_Q).stationary ↔
      ∀ v ∈ (gradCurl ℝ Geometry.isOpen_Q).invariantCore₁ (tsd (Q (Fin 3))) (tsd (Q (Fin 3))),
        ∃ h1 : v ∈ (gradCurl ℝ Geometry.isOpen_Q).d₁.domain,
          (gradCurl ℝ Geometry.isOpen_Q).d₁ ⟨v, h1⟩ = 0) ∧
    (¬ (gradCurl ℝ Geometry.isOpen_Q).coreSub (tsd (Q (Fin 3))) (tsd (Q (Fin 3))) ≤
        (gradCurl ℝ Geometry.isOpen_Q).stationary ↔
      ∃ ω : ℝ, 0 < ω ∧ ∃ v : L2F ℝ (Q (Fin 3)) Ix, v ≠ 0 ∧ v ∈ tsd (Q (Fin 3)) ∧
        (gradCurl ℝ Geometry.isOpen_Q).IsEigenfield ω v) ∧
    (∀ ω : ℝ, 0 < ω → ∀ v : L2F ℝ (Q (Fin 3)) Ix, v ∈ tsd (Q (Fin 3)) →
      (gradCurl ℝ Geometry.isOpen_Q).IsEigenfield ω v →
        v ∈ (gradCurl ℝ Geometry.isOpen_Q).invariantCore₁ (tsd (Q (Fin 3))) (tsd (Q (Fin 3))) ∧
          v ∈ tsd₀ (Q (Fin 3)) Geometry.isOpen_Q isBounded_Q ∧
            (v ≠ 0 → ShortHilbertComplex.inj₁ (𝕜 := ℝ) (L2F ℝ (Q (Fin 3)) (Fin 3))
              (L2F ℝ (Q (Fin 3)) Ix) (L2F ℝ (Q (Fin 3)) Ix) v ∉
                (gradCurl ℝ Geometry.isOpen_Q).stationary)) :=
  Box.gradCurl_coreSub_spectral_box (a := 0) (ℓ := fun _ => 1 / 2) fun _ => one_half_pos

end Feec.Models.Cube.RowWise

namespace Feec.Models.Cube.Ident

open Models.BoundedDomain (R3 Ix tsd tsd₀ gradCurl)
open Domain (L2F)
open Geometry (openCube)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3

variable {b : R3} {s : ℝ}

theorem eigenDense_complexCube (hs : 0 < s) : (complexCube b s).waveGroup.EigenDense :=
  Box.eigenDense_complexBox (a := b) (ℓ := fun _ => s) fun _ => hs

/-- **The eigenvector hypothesis of `gradCurl_coreSub_spectral` holds on every open cube.** -/
theorem eigenDense_gradCurl_cube (hs : 0 < s) :
    (gradCurl ℝ (Geometry.isOpen_openCube b s)).EigenDense :=
  eigenDense_complexCube hs

/-- **`K*` on every open cube `∏ (bᵢ, bᵢ + s)` for the thesis' complex**: its characterization by
`coreSub`, and `K*` consists of stationary data iff there is no nonzero TSD eigenfield. -/
theorem gradCurl_coreSub_spectral_cube (hs : 0 < s) :
    (∀ x, (∀ t, 0 ≤ t →
        (gradCurl ℝ (Geometry.isOpen_openCube b s)).toHilbertComplex.waveGroup.S t x ∈
          HilbertComplex.totalSub
            (ShortHilbertComplex.family3 ⊥ (tsd (openCube b s)) (tsd (openCube b s)))) ↔
          x ∈ (gradCurl ℝ (Geometry.isOpen_openCube b s)).coreSub (tsd (openCube b s))
            (tsd (openCube b s))) ∧
    ((gradCurl ℝ (Geometry.isOpen_openCube b s)).coreSub (tsd (openCube b s))
        (tsd (openCube b s)) ≤ (gradCurl ℝ (Geometry.isOpen_openCube b s)).stationary ↔
      ∀ v ∈ (gradCurl ℝ (Geometry.isOpen_openCube b s)).invariantCore₁ (tsd (openCube b s))
          (tsd (openCube b s)),
        ∃ h1 : v ∈ (gradCurl ℝ (Geometry.isOpen_openCube b s)).d₁.domain,
          (gradCurl ℝ (Geometry.isOpen_openCube b s)).d₁ ⟨v, h1⟩ = 0) ∧
    (¬ (gradCurl ℝ (Geometry.isOpen_openCube b s)).coreSub (tsd (openCube b s))
        (tsd (openCube b s)) ≤ (gradCurl ℝ (Geometry.isOpen_openCube b s)).stationary ↔
      ∃ ω : ℝ, 0 < ω ∧ ∃ v : L2F ℝ (openCube b s) Ix, v ≠ 0 ∧ v ∈ tsd (openCube b s) ∧
        (gradCurl ℝ (Geometry.isOpen_openCube b s)).IsEigenfield ω v) ∧
    (∀ ω : ℝ, 0 < ω → ∀ v : L2F ℝ (openCube b s) Ix, v ∈ tsd (openCube b s) →
      (gradCurl ℝ (Geometry.isOpen_openCube b s)).IsEigenfield ω v →
        v ∈ (gradCurl ℝ (Geometry.isOpen_openCube b s)).invariantCore₁ (tsd (openCube b s))
            (tsd (openCube b s)) ∧
          v ∈ tsd₀ (openCube b s) (Geometry.isOpen_openCube b s) (Geometry.isBounded_openCube b s) ∧
            (v ≠ 0 → ShortHilbertComplex.inj₁ (𝕜 := ℝ) (L2F ℝ (openCube b s) (Fin 3))
              (L2F ℝ (openCube b s) Ix) (L2F ℝ (openCube b s) Ix) v ∉
                (gradCurl ℝ (Geometry.isOpen_openCube b s)).stationary)) :=
  Box.gradCurl_coreSub_spectral_box (a := b) (ℓ := fun _ => s) fun _ => hs

end Feec.Models.Cube.Ident

/-! ### The mirror complexes -/

namespace Feec.Models.Cube.Mirror

open Feec.Models.BoundedDomain (R3)

/-- **The mirror complex on `Q = (0, ½)³` has a dense set of eigenvectors.** -/
theorem eigenDense_complexQ : complexQ.waveGroup.EigenDense :=
  HilbertComplex.eigenDense_compress eight_pos inner_J reducingSubcomplex_range
    (Fourier.Torus.eigenDense_waveGroup Fourier.GradCurl.gradCurl)

/-- **The mirror complex on every open cube `∏ (bᵢ, bᵢ + s)` has a dense set of eigenvectors.** -/
theorem eigenDense_complexCube (b : R3) {s : ℝ} (hs : 0 < s) :
    (complexCube b s hs).waveGroup.EigenDense :=
  HilbertComplex.eigenDense_transport_const complexQ (jac_inv_pos hs) (inner_eCube (hs := hs))
    (inv_two_mul_ne hs) eigenDense_complexQ

end Feec.Models.Cube.Mirror
