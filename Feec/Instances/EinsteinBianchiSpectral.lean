module

public import Feec.Fourier.SpectralGalerkin
public import Feec.HilbertComplex.Approximation.Spectral
public import Feec.Models.Torus.BGG
public import Feec.Models.Cube.MirrorBGG

/-!
# Spectral discretizations of the Einstein–Bianchi BGG complex

The Fourier bands of the BGG complex (5.1) are a spectral family on `𝕋³` and, through the mirror
extensions, on the cube with mirror boundary conditions; as reducing families they satisfy the
FEEC theorem for reducing families with the TSD constraint.

## Main results

* `einsteinBianchi_torus_approxFEEC`, `einsteinBianchi_mirror_approxFEEC`: the FEEC theorem.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

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

/-- The Fourier spectral family of a symbol complex on `ℤᵈ`: the bands `|n|_∞ ≤ N`. -/
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

/-- The Fourier spectral family of the periodic BGG complex (5.1). -/
def bandFamily : SpectralFamily complex :=
  bandSpectralFamily (Fourier.Torus.symbolComplex bggFamily)

end Torus

/-! ### The cosine–sine bands of the mirror complexes on the cube -/

section MirrorBands

open Feec.Fourier

variable {ι : Type*} [Fintype ι] {c : ComplexShape ι} {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, FiniteDimensional ℂ (E i)] [∀ i, CompleteSpace (E i)]
  {S : SymbolComplex ℂ (Measure.count : Measure (Fin 3 → ℤ)) c E} (Y : S.Symmetries (Fin 3))

omit [Fintype ι] in
theorem act_mem_torusBand (hY : ∀ k n, (Y.R k).σ n = Fourier.Torus.flipAt k n) (N : ℕ)
    (g : Multiplicative (Fin 3 → ZMod 2)) (i : ι)
    {x : Lp (E i) 2 (Measure.count : Measure (Fin 3 → ℤ))} (hx : x ∈ (bandSpectralFamily S).B N i) :
    Y.toAction.act g i x ∈ (bandSpectralFamily S).B N i := by
  refine Y.act_mem_fibreSub
    (K := fun i n => bandFibre (𝕜 := ℂ) (E := E) (Fourier.Torus.bandN N) i n)
    (fun k i n v hv => ?_) g i hx
  rw [hY] at hv
  by_cases hn : n ∈ Fourier.Torus.bandN N
  · simp [bandFibre, hn]
  · have hn' : Fourier.Torus.flipAt k n ∉ Fourier.Torus.bandN N :=
      (Fourier.Torus.flipAt_mem_bandN k).not.2 hn
    have hv0 : v = 0 := by simpa [bandFibre, hn'] using hv
    simp [bandFibre, hn, hv0]

variable {W' : ι → Type*} [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace ℂ (W' i)]
  [∀ i, CompleteSpace (W' i)] {H' : HilbertComplex ℂ c W'}

omit [Fintype ι] in
theorem exists_J_eq_starProjection_torusBand
    (hY : ∀ k n, (Y.R k).σ n = Fourier.Torus.flipAt k n)
    (e : ScaledEmbedding H' S.toHilbertComplex)
    (he : ∀ i, LinearMap.range (e.J i : W' i →ₗ[ℂ] _) = Y.toAction.fixed i) (N : ℕ) (i : ι)
    (x : W' i) : ∃ y, e.J i y = ((bandSpectralFamily S).B N i).starProjection (e.J i x) := by
  have hx : e.J i x ∈ Y.toAction.fixed i := he i ▸ LinearMap.mem_range_self _ x
  have h := Y.toAction.starProjection_mem_fixed (fun g y hy => act_mem_torusBand Y hY N g i hy) hx
  rw [← he] at h
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy⟩

/-- The cosine–sine spectral family of a mirror complex: the pull-back of the Fourier bands. -/
def mirrorSpectralFamily (hY : ∀ k n, (Y.R k).σ n = Fourier.Torus.flipAt k n)
    (e : ScaledEmbedding H' S.toHilbertComplex)
    (he : ∀ i, LinearMap.range (e.J i : W' i →ₗ[ℂ] _) = Y.toAction.fixed i) : SpectralFamily H' :=
  (bandSpectralFamily S).comap e (exists_J_eq_starProjection_torusBand Y hY e he)

end MirrorBands

section Mirror

open Feec.Models.Cube.MirrorBGG

/-- The cosine–sine spectral family of the mirror BGG complex on `Q`. -/
def bandFamilyQ : SpectralFamily complexQ :=
  mirrorSpectralFamily symmetries (fun _ _ => rfl) embeddingQ range_J

end Mirror

/-! ### The spectral EB discretizations through the approximating FEEC theorem -/

section TorusApprox

open Feec.Models.Torus.BGG

/-- The Fourier bands `|n|_∞ ≤ N` of the periodic BGG complex as a reducing family. -/
abbrev torusBands : ReducingFamily complex ℕ := .ofSpectral bandFamily

/-- The Fourier spectral method for the EB system on `𝕋³` as an approximating discretization. -/
def torusApprox : ApproxFEEC complex ℕ :=
  torusBands.toApprox (totalSub constraint) isClosed_totalSub

/-- Its core: all of `W`, with zero consistency defect. -/
def torusCore : torusApprox.Core := torusBands.toCore (totalSub constraint) isClosed_totalSub

theorem torusApprox_isReducing : complex.wave.IsReducing (totalSub constraint) :=
  reducingSubcomplex.isReducing_wave

/-- **The FEEC theorem for the EB system on `𝕋³`** with the Fourier spectral method.
[QuennevilleBelair2015], Thm 4.14, Prop 4.17, Ch. 6 -/
theorem einsteinBianchi_torus_approxFEEC :
    torusBands.Verdict (totalSub constraint) isClosed_totalSub :=
  torusBands.feec _ _

end TorusApprox

section MirrorApprox

open Feec.Models.Cube.MirrorBGG

/-- The cosine–sine bands of the mirror BGG complex on `Q` as a reducing family. -/
abbrev mirrorBands : ReducingFamily complexQ ℕ := .ofSpectral bandFamilyQ

/-- The cosine–sine spectral method for the EB system on the mirror cube. -/
def mirrorApprox : ApproxFEEC complexQ ℕ :=
  mirrorBands.toApprox (totalSub tsdQ) isClosed_totalSub

/-- Its core: all of `W`, with zero consistency defect. -/
def mirrorCore : mirrorApprox.Core := mirrorBands.toCore (totalSub tsdQ) isClosed_totalSub

theorem mirrorApprox_isReducing : complexQ.wave.IsReducing (totalSub tsdQ) :=
  reducingSubcomplexQ.isReducing_wave

/-- **The FEEC theorem for the EB system on the cube with mirror boundary conditions**, with the
cosine–sine spectral method. [QuennevilleBelair2015], Thm 4.14, Prop 4.17 (adapted), Ch. 6 -/
theorem einsteinBianchi_mirror_approxFEEC :
    mirrorBands.Verdict (totalSub tsdQ) isClosed_totalSub :=
  mirrorBands.feec _ _

end MirrorApprox

end Feec.Instances.EinsteinBianchi
