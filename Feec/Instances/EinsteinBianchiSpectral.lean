module

public import Feec.Fourier.SpectralGalerkin
public import Feec.HilbertComplex.Approximation.Spectral
public import Feec.Models.Torus.BGG
public import Feec.Models.Cube.MirrorBGG

/-!
# Spectral discretizations of the Einstein–Bianchi BGG complex

The Fourier bands of the BGG complex (5.1) are a spectral family
(`Feec.HilbertComplex.SpectralFamily`: finite-dimensional reducing subcomplexes whose orthogonal
projections converge strongly to `1`), on `𝕋³` and, through the mirror extensions, on the cube
with mirror boundary conditions. As reducing families (`ReducingFamily.ofSpectral`) they satisfy
the FEEC theorem for reducing families (`ReducingFamily.feec`): the verdict of the approximating
FEEC theorem on all data, the error is the truncation error of the datum at every time, and TSD
is preserved by the truncations; as conforming families (`ConformingFamily.ofSpectral`,
`SpectralFamily.toFEEC`) they are the constrained FEEC discretizations `torusFEEC`, `mirrorFEEC`
of `Feec.Instances.EinsteinBianchi`.

**Instances** (namespace `Feec.Instances.EinsteinBianchi`).

* `bandFamily`: the Fourier bands `|n|_∞ ≤ N` of the periodic BGG complex (5.1) on `𝕋³` (the
  Fourier spectral method); `torusBands`, `torusApprox`, `torusCore` and the headline
  `einsteinBianchi_torus_approxFEEC` (the discretization `torusFEEC` of
  `Feec.Instances.EinsteinBianchi` is `bandFamily.toFEEC (totalSub constraint) isClosed_totalSub`);
* `bandFamilyQ`: their pull-back to the BGG complex on the cube `Q = (0, ½)³` with mirror boundary
  conditions (cosine–sine bands, through the mirror extensions: the mirror action preserves the
  bands, `act_mem_band`); `mirrorBands`, `mirrorApprox`, `mirrorCore`,
  `einsteinBianchi_mirror_approxFEEC` (`mirrorFEEC`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.6 (subcomplexes), §4.12–4.13 (Galerkin approximation of the Hodge wave equation), Ch. 6
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3 (approximation property, bounded cochain projections)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace Topology
open Set Filter MeasureTheory LinearPMap Metric

@[expose] public noncomputable section

namespace Feec.Instances.EinsteinBianchi

open Feec.HilbertComplex

/-! ### The Fourier bands of the periodic BGG complex -/

section Torus

open Feec.Fourier Feec.Fourier.BGG Feec.Models.Torus.BGG

/-- The band-limited fields `|n|_∞ ≤ N` of the periodic BGG complex. -/
abbrev band (N : ℕ) (i : Fin 3) : Submodule ℂ (Space i) :=
  (Fourier.Torus.symbolComplex bggFamily).band (Fourier.Torus.bandN N) i

instance (N : ℕ) (i : Fin 3) : (band N i).HasOrthogonalProjection :=
  Fourier.hasOrthogonalProjection_band _ (Fourier.Torus.finite_bandN N).measurableSet i

/-- **The Fourier spectral family of the periodic BGG complex** (5.1): the bands `|n|_∞ ≤ N`. -/
def bandFamily : SpectralFamily complex where
  B := band
  finiteDimensional N i := Fourier.finiteDimensional_band _ (Fourier.Torus.finite_bandN N) i
  mono N M h i u hu := by
    rw [Fourier.mem_band_iff] at hu ⊢
    filter_upwards [hu] with a ha hM
    exact ha fun hN => hM (Fourier.Torus.bandN_mono h hN)
  reducing N := Fourier.reducingSubcomplex_band _ (Fourier.Torus.finite_bandN N).measurableSet
  tendsto i x := Fourier.tendsto_starProjection_band _
    (fun N => (Fourier.Torus.finite_bandN N).measurableSet) Fourier.Torus.bandN_mono
    Fourier.Torus.exists_mem_bandN i x

end Torus

/-! ### The cosine–sine bands of the mirror BGG complex on the cube -/

section Mirror

open Feec.Fourier Feec.Fourier.GradCurl Feec.Fourier.BGG Feec.Models.Cube.MirrorBGG

theorem flipAt_mem_bandN {k : Fin 3} {n : Fin 3 → ℤ} {N : ℕ} :
    Models.Cube.MirrorExt.flipAt k n ∈ Fourier.Torus.bandN N ↔ n ∈ Fourier.Torus.bandN N := by
  simp only [Fourier.Torus.bandN, mem_ofPred_eq, Models.Cube.MirrorExt.flipAt_apply]
  refine forall_congr' fun j => ?_
  split_ifs <;> simp

/-- **The mirror action preserves the Fourier bands** (`|flip_k n|_∞ = |n|_∞`). -/
theorem act_mem_band (N : ℕ) (g : Multiplicative (Fin 3 → ZMod 2)) (i : Fin 3)
    {x : Feec.Models.Torus.BGG.Space i} (hx : x ∈ band N i) : action.act g i x ∈ band N i := by
  refine symmetries.act_mem_fibreSub
    (K := fun i n => bandFibre (𝕜 := ℂ) (E := ShortHilbertComplex.W3 ℂ Mat VM)
      (Fourier.Torus.bandN N) i n) (fun k i n v hv => ?_) g i hx
  change v ∈ bandFibre _ i (Models.Cube.MirrorExt.flipAt k n) at hv
  by_cases hn : n ∈ Fourier.Torus.bandN N
  · simp [bandFibre, hn]
  · have hn' : Models.Cube.MirrorExt.flipAt k n ∉ Fourier.Torus.bandN N := flipAt_mem_bandN.not.2 hn
    have hv0 : v = 0 := by simpa [bandFibre, hn'] using hv
    simp [bandFibre, hn, hv0]

/-- The band projections preserve the range of the mirror extensions (the fixed fields). -/
theorem exists_J_eq_starProjection_band (N : ℕ) (i : Fin 3) (x : SpaceQ i) :
    ∃ y, embeddingQ.J i y = (band N i).starProjection (embeddingQ.J i x) := by
  have hx : J i x ∈ action.fixed i := range_J i ▸ LinearMap.mem_range_self _ x
  have h := action.starProjection_mem_fixed (fun g y hy => act_mem_band N g i hy) hx
  rw [← range_J] at h
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy⟩

/-- **The cosine–sine spectral family of the mirror BGG complex on `Q`**: the pull-back of the
Fourier bands along the mirror extensions. -/
def bandFamilyQ : SpectralFamily complexQ :=
  bandFamily.comap embeddingQ exists_J_eq_starProjection_band

end Mirror

/-! ### The spectral EB discretizations through the approximating FEEC theorem -/

section TorusApprox

open Feec.Models.Torus.BGG

/-- The Fourier bands `|n|_∞ ≤ N` of the periodic BGG complex as a reducing family. -/
abbrev torusBands : ReducingFamily complex ℕ := .ofSpectral bandFamily

/-- **The Fourier spectral method for the EB system on `𝕋³` as an approximating FEEC
discretization**: `X_N` the band `∏ B_N`, `ι_N` its inclusion, `π_N` the orthogonal projection,
`L_N = L|_{B_N}`, with the TSD constraint. -/
def torusApprox : ApproxFEEC complex ℕ :=
  torusBands.toApprox (totalSub constraint) isClosed_totalSub

/-- Its core: all of `W`, with zero consistency defect. -/
def torusCore : torusApprox.Core := torusBands.toCore (totalSub constraint) isClosed_totalSub

theorem torusApprox_isReducing : complex.wave.IsReducing (totalSub constraint) :=
  reducingSubcomplex.isReducing_wave

/-- **The FEEC theorem for the EB system on `𝕋³`** (Fourier spectral method): the verdict of
`ReducingFamily.feec` (that of `approxFEEC` on all data: well-posedness, propagation iff reducing,
convergence from every convergent family of initial values, rates, constraint residuals; the
error is the truncation error of the datum at every time). [QuennevilleBelair2015], Thm 4.14,
Prop 4.17, Ch. 6 -/
theorem einsteinBianchi_torus_approxFEEC :
    torusBands.Verdict (totalSub constraint) isClosed_totalSub :=
  torusBands.feec _ _

end TorusApprox

section MirrorApprox

open Feec.Models.Cube.MirrorBGG

/-- The cosine–sine bands of the mirror BGG complex on `Q` as a reducing family. -/
abbrev mirrorBands : ReducingFamily complexQ ℕ := .ofSpectral bandFamilyQ

/-- **The cosine–sine spectral method for the EB system on the cube with mirror boundary
conditions as an approximating FEEC discretization**, with the TSD constraint `tsdQ`. -/
def mirrorApprox : ApproxFEEC complexQ ℕ :=
  mirrorBands.toApprox (totalSub tsdQ) isClosed_totalSub

/-- Its core: all of `W`, with zero consistency defect. -/
def mirrorCore : mirrorApprox.Core := mirrorBands.toCore (totalSub tsdQ) isClosed_totalSub

theorem mirrorApprox_isReducing : complexQ.wave.IsReducing (totalSub tsdQ) :=
  reducingSubcomplexQ.isReducing_wave

/-- **The FEEC theorem for the EB system on the cube with mirror boundary conditions**
(cosine–sine spectral method): the verdict of `ReducingFamily.feec`. [QuennevilleBelair2015],
Thm 4.14, Prop 4.17 (corrected), Ch. 6 -/
theorem einsteinBianchi_mirror_approxFEEC :
    mirrorBands.Verdict (totalSub tsdQ) isClosed_totalSub :=
  mirrorBands.feec _ _

end MirrorApprox

end Feec.Instances.EinsteinBianchi
