import Feec.Instances.EinsteinBianchiSpectral

/-!
# Regression tests: the mirror bands of the Einstein–Bianchi spectral families

The mirror action on the bands `|n|_∞ ≤ N` and the projections onto them were proved for the BGG
complex (5.1) only (`act_mem_band`, `exists_J_eq_starProjection_band`); they are now proved for
every symbol complex on `ℤ³` with mirror reflections and every embedding onto the fixed fields
(`Feec.Instances.EinsteinBianchi.act_mem_torusBand`,
`Feec.Instances.EinsteinBianchi.exists_J_eq_starProjection_torusBand`), which gives the
cosine–sine spectral families of all the mirror complexes
(`Feec.Instances.EinsteinBianchi.mirrorSpectralFamily`). The module
`Feec.Models.Cube.Smoothing` (even Fourier multipliers on the cube, used by nothing: the smoothers
of the finite element method are those of `Feec.Models.Cube.SmoothingEstimates` and
`Feec.Models.Cube.ParitySmoother`) is deleted; its frequency boxes are the bands
`Feec.Fourier.Torus.bandN` and its summability lemma is `Feec.Fourier.hasSum_norm_sq_count`. The
theorems `bridges_old_*` state the deleted results verbatim (with the deleted definition `box`
unfolded) and derive them from the new API.

This file is part of the `FeecCheck` library, not of `Feec`.
-/

namespace FeecCheck.Bridges

open Feec Feec.HilbertComplex Feec.Instances.EinsteinBianchi Feec.Models.Cube.MirrorBGG

/-- The old `act_mem_band`: the mirror action of `(ℤ/2)³` preserves the Fourier bands of the
periodic BGG complex. -/
theorem bridges_old_act_mem_band (N : ℕ) (g : Multiplicative (Fin 3 → ZMod 2)) (i : Fin 3)
    {x : Feec.Models.Torus.BGG.Space i} (hx : x ∈ band N i) : action.act g i x ∈ band N i :=
  act_mem_torusBand symmetries (fun _ _ => rfl) N g i hx

/-- The old `exists_J_eq_starProjection_band`: the band projections preserve the range of the
mirror extensions. -/
theorem bridges_old_exists_J_eq_starProjection_band (N : ℕ) (i : Fin 3) (x : SpaceQ i) :
    ∃ y, embeddingQ.J i y = (band N i).starProjection (embeddingQ.J i x) :=
  exists_J_eq_starProjection_torusBand symmetries (fun _ _ => rfl) embeddingQ range_J N i x

/-- The old `Feec.Models.Cube.DeRham.summable_norm_sq_count`: `‖v q‖²` is summable for
`v ∈ ℓ²(ℤᵈ)`. -/
theorem bridges_old_summable_norm_sq_count {d : Type*} [Fintype d] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : MeasureTheory.Lp E 2 (MeasureTheory.Measure.count : MeasureTheory.Measure (d → ℤ))) :
    Summable fun q => ‖v q‖ ^ 2 :=
  (Feec.Fourier.hasSum_norm_sq_count (𝕜 := ℂ) (E := fun _ : Unit => E) (i := ()) v).summable

/-- The old `Feec.Models.Cube.DeRham.mem_box` (with `box d K` unfolded): the frequency box
`‖q‖_∞ ≤ K` is the band `Feec.Fourier.Torus.bandN K`. -/
theorem bridges_old_mem_box {d : Type*} [Fintype d] [DecidableEq d] {K : ℕ} {q : d → ℤ} :
    q ∈ (Fintype.piFinset fun _ => Finset.Icc (-(K : ℤ)) K) ↔ ∀ a, |q a| ≤ K := by
  change _ ↔ q ∈ Feec.Fourier.Torus.bandN K
  simp only [Fintype.mem_piFinset, Finset.mem_Icc, Feec.Fourier.Torus.bandN, Set.mem_ofPred_eq,
    abs_le]

end FeecCheck.Bridges
