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

* `bandSpectralFamily`: the Fourier bands `|n|_∞ ≤ N` of every symbol complex on `ℤᵈ` (every
  constant-coefficient complex on `𝕋ᵈ` and its anisotropic versions);
* `bandFamily`: these bands for the periodic BGG complex (5.1) on `𝕋³` (the Fourier spectral
  method); `torusBands`, `torusApprox`, `torusCore` and the headline
  `einsteinBianchi_torus_approxFEEC` (the discretization `torusFEEC` of
  `Feec.Instances.EinsteinBianchi` is `bandFamily.toFEEC (totalSub constraint) isClosed_totalSub`);
* `bandFamilyQ`: their pull-back to the BGG complex on the cube `Q = (0, ½)³` with mirror boundary
  conditions (cosine–sine bands, through the mirror extensions: the mirror action preserves the
  bands, `act_mem_torusBand`; `mirrorSpectralFamily` for every complex embedded onto the fields of
  a symbol complex on `ℤ³` fixed by the mirror flips); `mirrorBands`, `mirrorApprox`, `mirrorCore`,
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

/-! ### The Fourier bands of a constant-coefficient complex on the torus -/

section TorusBands

open Feec.Fourier

variable {d : Type*} [Fintype d] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, FiniteDimensional ℂ (E i)] [∀ i, CompleteSpace (E i)]
  (S : SymbolComplex ℂ (Measure.count : Measure (d → ℤ)) c E)

/-- **The Fourier spectral family of a symbol complex on `ℤᵈ`** (the Fourier side of a
constant-coefficient complex on `𝕋ᵈ`, `Fourier.Torus.symbolComplex`, or of its anisotropic
versions): the bands `|n|_∞ ≤ N`, finite-dimensional, reducing, increasing and exhausting. -/
def bandSpectralFamily : SpectralFamily S.toHilbertComplex :=
  haveI := fun N i =>
    Fourier.hasOrthogonalProjection_band S (Fourier.Torus.finite_bandN (d := d) N).measurableSet i
  { B N := S.band (Fourier.Torus.bandN N)
    finiteDimensional N i := Fourier.finiteDimensional_band _ (Fourier.Torus.finite_bandN N) i
    mono N M h i u hu := by
      rw [Fourier.mem_band_iff] at hu ⊢
      filter_upwards [hu] with a ha hM
      exact ha fun hN => hM (Fourier.Torus.bandN_mono h hN)
    reducing N := Fourier.reducingSubcomplex_band _ (Fourier.Torus.finite_bandN N).measurableSet
    tendsto i x := Fourier.tendsto_starProjection_band _
      (fun N => (Fourier.Torus.finite_bandN N).measurableSet) Fourier.Torus.bandN_mono
      Fourier.Torus.exists_mem_bandN i x }

end TorusBands

/-! ### The Fourier bands of the periodic BGG complex -/

section Torus

open Feec.Fourier Feec.Fourier.BGG Feec.Models.Torus.BGG

/-- The band-limited fields `|n|_∞ ≤ N` of the periodic BGG complex. -/
abbrev band (N : ℕ) (i : Fin 3) : Submodule ℂ (Space i) :=
  (Fourier.Torus.symbolComplex bggFamily).band (Fourier.Torus.bandN N) i

instance (N : ℕ) (i : Fin 3) : (band N i).HasOrthogonalProjection :=
  Fourier.hasOrthogonalProjection_band _ (Fourier.Torus.finite_bandN N).measurableSet i

/-- **The Fourier spectral family of the periodic BGG complex** (5.1): the bands `|n|_∞ ≤ N`. -/
def bandFamily : SpectralFamily complex :=
  bandSpectralFamily (Fourier.Torus.symbolComplex bggFamily)

end Torus

/-! ### The cosine–sine bands of the mirror complexes on the cube -/

section MirrorBands

open Feec.Fourier

theorem flipAt_mem_bandN {k : Fin 3} {n : Fin 3 → ℤ} {N : ℕ} :
    Models.Cube.MirrorExt.flipAt k n ∈ Fourier.Torus.bandN N ↔ n ∈ Fourier.Torus.bandN N := by
  simp only [Fourier.Torus.bandN, mem_ofPred_eq, Models.Cube.MirrorExt.flipAt_apply]
  refine forall_congr' fun j => ?_
  split_ifs <;> simp

variable {ι : Type*} [Fintype ι] {c : ComplexShape ι} {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, FiniteDimensional ℂ (E i)] [∀ i, CompleteSpace (E i)]
  {S : SymbolComplex ℂ (Measure.count : Measure (Fin 3 → ℤ)) c E} (Y : S.Symmetries (Fin 3))

omit [Fintype ι] in
/-- **A mirror action preserves the Fourier bands** (`|flip_k n|_∞ = |n|_∞`): for symmetries of a
torus complex whose frequency reflections are the mirror flips `n ↦ flip_k n`. -/
theorem act_mem_torusBand (hY : ∀ k n, (Y.R k).σ n = Models.Cube.MirrorExt.flipAt k n) (N : ℕ)
    (g : Multiplicative (Fin 3 → ZMod 2)) (i : ι)
    {x : Lp (E i) 2 (Measure.count : Measure (Fin 3 → ℤ))} (hx : x ∈ (bandSpectralFamily S).B N i) :
    Y.toAction.act g i x ∈ (bandSpectralFamily S).B N i := by
  refine Y.act_mem_fibreSub
    (K := fun i n => bandFibre (𝕜 := ℂ) (E := E) (Fourier.Torus.bandN N) i n)
    (fun k i n v hv => ?_) g i hx
  rw [hY] at hv
  by_cases hn : n ∈ Fourier.Torus.bandN N
  · simp [bandFibre, hn]
  · have hn' : Models.Cube.MirrorExt.flipAt k n ∉ Fourier.Torus.bandN N := flipAt_mem_bandN.not.2 hn
    have hv0 : v = 0 := by simpa [bandFibre, hn'] using hv
    simp [bandFibre, hn, hv0]

variable {W' : ι → Type*} [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace ℂ (W' i)]
  [∀ i, CompleteSpace (W' i)] {H' : HilbertComplex ℂ c W'}

omit [Fintype ι] in
/-- **The band projections preserve the fixed fields** of a mirror action, i.e. the range of an
embedding onto them (the method of images). -/
theorem exists_J_eq_starProjection_torusBand
    (hY : ∀ k n, (Y.R k).σ n = Models.Cube.MirrorExt.flipAt k n)
    (e : ScaledEmbedding H' S.toHilbertComplex)
    (he : ∀ i, LinearMap.range (e.J i : W' i →ₗ[ℂ] _) = Y.toAction.fixed i) (N : ℕ) (i : ι)
    (x : W' i) : ∃ y, e.J i y = ((bandSpectralFamily S).B N i).starProjection (e.J i x) := by
  have hx : e.J i x ∈ Y.toAction.fixed i := he i ▸ LinearMap.mem_range_self _ x
  have h := Y.toAction.starProjection_mem_fixed (fun g y hy => act_mem_torusBand Y hY N g i hy) hx
  rw [← he] at h
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy⟩

/-- **The cosine–sine spectral family of a mirror complex**: for a complex `H'` embedded (with a
scaling) in a torus complex onto the fields fixed by a mirror action (`e.J` onto `Y.toAction.fixed`,
the method of images), the pull-back of the Fourier bands `|n|_∞ ≤ N` (the action preserves them,
`act_mem_torusBand`, so their projections preserve the fixed fields). -/
def mirrorSpectralFamily (hY : ∀ k n, (Y.R k).σ n = Models.Cube.MirrorExt.flipAt k n)
    (e : ScaledEmbedding H' S.toHilbertComplex)
    (he : ∀ i, LinearMap.range (e.J i : W' i →ₗ[ℂ] _) = Y.toAction.fixed i) : SpectralFamily H' :=
  (bandSpectralFamily S).comap e (exists_J_eq_starProjection_torusBand Y hY e he)

end MirrorBands

section Mirror

open Feec.Models.Cube.MirrorBGG

/-- **The cosine–sine spectral family of the mirror BGG complex on `Q`**: the pull-back of the
Fourier bands along the mirror extensions. -/
def bandFamilyQ : SpectralFamily complexQ :=
  mirrorSpectralFamily symmetries (fun _ _ => rfl) embeddingQ range_J

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
