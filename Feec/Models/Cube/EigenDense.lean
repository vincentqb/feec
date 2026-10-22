module

public import Feec.Models.Cube.Ident
public import Feec.Models.Cube.Mirror
public import Feec.Models.BoundedDomain.InvariantCore
public import Feec.HilbertComplex.CompressCompact

/-!
# A complete set of eigenvectors on cubes

`Feec.Models.BoundedDomain.gradCurl_coreSub_spectral` decides, on a bounded open `Ω ⊆ ℝ³`,
whether the invariant core `K*` of `K = {0} × L²(TSD) × L²(TSD)` contains a moving datum, under
the hypothesis `EigenDense` (a dense set of eigenvectors of `L²`) for the wave group of the
thesis' complex `H̊¹(Ω) → H̊(curl, Ω) → L²(Ω)`. This file proves that hypothesis **on cubes**:

* on `Q = (0, ½)³` the complex is the compression of the real torus grad–curl complex along the
  parity extension (`Feec.Models.Cube.RowWise.cubeComplex_eq_compress`), whose wave group has an
  eigenbasis (the Fourier modes, `Feec.Models.Cube.Parity.eigenDense_torus`), and `EigenDense`
  passes to compressions (`Feec.HilbertComplex.eigenDense_compress`);
* on every open cube `∏ (bᵢ, bᵢ + s)` the complex is the transport of the one on `Q` along the
  affine pull-back, with constant chain-rule factor `1/(2s)` (`Feec.Models.Cube.Ident.complexCube_eq`),
  and `EigenDense` passes to such transports (`HilbertComplex.eigenDense_transport_const`, from
  `HilbertComplex.wave_transport_const`).

This discharges the hypothesis of `gradCurl_coreSub_spectral` on every open cube
(`Ident.eigenDense_gradCurl_cube`). The same holds for the mirror complexes
(`Feec.Models.Cube.Mirror`) on the cube `Q` and every open cube (`Mirror.eigenDense_complexQ`,
`Mirror.eigenDense_complexCube`; on boxes `Feec.Models.Box.Mirror.eigenDense_complexBoxM`).

Boxes with unequal sides are not covered by this file (their pull-back to `Q` rescales each
coordinate by its own factor, so the operator changes instead of being rescaled); they are
treated by the anisotropic parity model of `Feec.Models.Box.EigenDense`
(`Feec.Models.Box.eigenDense_gradCurl_box`). Nothing is claimed for other domains.

## Main results

* `HilbertComplex.eigenDense_transport_const`.
* **`RowWise.eigenDense_cubeComplex`**, `Ident.eigenDense_complexCube`,
  **`Ident.eigenDense_gradCurl_cube`**.
* `Mirror.eigenDense_complexQ`, `Mirror.eigenDense_complexCube`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (Prop 4.17)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6 (the compactness property
  and the eigenvalue problem of the Hodge Laplacian)

Bibliography: [references.bib](../../../docs/references.bib)
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

/-- **`EigenDense` passes to transports with a constant real chain-rule factor `κ ≠ 0`** along
uniformly scaled isometries: `L' e = κ e L` maps eigenvectors of `L²` (eigenvalue `-ω²`) to
eigenvectors of `L'²` (eigenvalue `-(κω)²`). -/
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

attribute [local instance] RealTorus.isScalarTower

/-- **The wave group of the thesis' complex on `Q` has a dense set of eigenvectors**: it is the
compression of the torus wave group, which has the Fourier modes as an eigenbasis. -/
theorem eigenDense_cubeComplex : cubeComplex.waveGroup.EigenDense := by
  rw [cubeComplex_eq_compress]
  exact HilbertComplex.eigenDense_compress _ _ _ Parity.eigenDense_torus

end Feec.Models.Cube.RowWise

namespace Feec.Models.Cube.Ident

open Models.BoundedDomain (R3 Ix tsd tsd₀ gradCurl)
open Domain (L2F)
open RowWise (cubeComplex)
open Geometry (openCube)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3

variable {b : R3} {s : ℝ}

/-- **The wave group of the thesis' complex on every open cube `∏ (bᵢ, bᵢ + s)` has a dense set
of eigenvectors**: it is the transport of the one on `Q`, with time rescaled by `1/(2s)`. -/
theorem eigenDense_complexCube (hs : 0 < s) : (complexCube b s).waveGroup.EigenDense := by
  rw [complexCube_eq hs]
  exact HilbertComplex.eigenDense_transport_const cubeComplex
    (inv_pos.2 (Domain.jac_pos (scale_ne_zero hs))) (inner_pullC hs) (scale_ne_zero hs)
    RowWise.eigenDense_cubeComplex

/-- **The eigenvector hypothesis of `gradCurl_coreSub_spectral` holds on every open cube.** -/
theorem eigenDense_gradCurl_cube (hs : 0 < s) :
    (gradCurl ℝ (Geometry.isOpen_openCube b s)).EigenDense :=
  eigenDense_complexCube hs

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
