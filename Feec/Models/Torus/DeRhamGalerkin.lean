module

public import Feec.Models.Torus.DeRham
public import Feec.HilbertComplex.Approximation.QuasiOptimal

/-!
# Spectral Galerkin approximation of the torus de Rham complex

The band-limited forms `|n|_∞ ≤ N` (`Fourier.Torus.bandN N`) of the `L²` de Rham complex of the
torus form a finite-dimensional subcomplex `bandSubcomplex d N` (a finite-dimensional reducing
subspace lies in the domain, `LinearPMap.IsReducingPair.le_domain`), with the Fourier truncation
as a cochain projection (`bandProj d N`) of graph norm `1`. The harmonic forms (the constant forms) are
band-limited for every `N`, so the harmonic gap `μ` vanishes. The abstract quasi-optimal estimate
of the mixed Hodge Laplacian (`Subcomplex.CochainProjection.norm_sub_le_infDist`, [AFW2010],
Thm 3.9) then applies with the constants `C = 1`, `c_P = (2π)⁻¹`, `μ = 0`, and the spectral Galerkin
solutions converge to the solution of the mixed problem as `N → ∞` (`tendsto_bandGalerkin`).
This shows the hypotheses of the abstract theory are satisfiable by a nontrivial family of
subcomplexes.

## Main results

* `bandSubcomplex`, `bandProj`, `isGraphBounded_bandProj`, `bandProj_harmonic`.
* `norm_sub_le_bandGalerkin`: the quasi-optimal estimate for the spectral Galerkin method.
* **`tendsto_bandGalerkin`**: convergence of the discrete mixed solutions.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3–3.4 (subcomplexes, cochain projections, Thm 3.9)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]
  (cochain projections and stable discretizations)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 5 (approximation of Hilbert
  complexes)

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace Topology
open MeasureTheory LinearPMap Filter Feec.Fourier Feec.Fourier.Exterior

namespace Feec.Models.Torus.DeRham

variable {d : Type*} [Fintype d] [LinearOrder d]

/-- The band-limited `k`-forms `|n|_∞ ≤ N`. -/
abbrev band (N k : ℕ) : Submodule ℂ (L2Form d k) :=
  (Fourier.Torus.symbolComplex (deRham d)).band (Fourier.Torus.bandN N) k

instance (N k : ℕ) : (band (d := d) N k).HasOrthogonalProjection :=
  Fourier.hasOrthogonalProjection_band _ (Fourier.Torus.finite_bandN N).measurableSet k

instance (N k : ℕ) : FiniteDimensional ℂ (band (d := d) N k) :=
  Fourier.finiteDimensional_band _ (Fourier.Torus.finite_bandN N) k

theorem reducingSubcomplex_band (N : ℕ) : (complex d).ReducingSubcomplex (band (d := d) N) :=
  Fourier.reducingSubcomplex_band _ (Fourier.Torus.finite_bandN N).measurableSet

variable (d) in
/-- **The band subcomplex** `Vₕᵏ = {u | û(n) = 0 for |n|_∞ > N}` of the torus de Rham complex. -/
def bandSubcomplex (N : ℕ) : (complex d).Subcomplex where
  V := band N
  le_domain k j :=
    ((reducingSubcomplex_band N).reduces k j).le_domain ((complex d).dense k j)
  mapsTo _ _ x hx := (reducingSubcomplex_band N).mapsTo ⟨x, _⟩ hx

instance (N k : ℕ) : FiniteDimensional ℂ ((bandSubcomplex d N).V k) :=
  inferInstanceAs (FiniteDimensional ℂ (band (d := d) N k))

variable (d) in
/-- **The Fourier truncation** as a cochain projection onto the band subcomplex. -/
def bandProj (N : ℕ) : (bandSubcomplex d N).CochainProjection where
  π k := ((band (d := d) N k).starProjection : L2Form d k →ₗ[ℂ] L2Form d k)
  mem _ x := Submodule.starProjection_apply_mem _ x
  proj _ _ hx := Submodule.starProjection_eq_self_iff.2 hx
  comm k j x := ((reducingSubcomplex_band N).reduces k j).comm x

theorem bandProj_apply (N k : ℕ) (x : L2Form d k) :
    (bandProj d N).π k x = (band (d := d) N k).starProjection x := rfl

/-- The Fourier truncation has graph norm `1`. -/
theorem isGraphBounded_bandProj (N k j : ℕ) : (bandProj d N).IsGraphBounded k j 1 := by
  intro x
  have hc := ((reducingSubcomplex_band (d := d) N).reduces k j).comm x
  have e : (complex d).d k j ⟨(bandProj d N).π k x, (bandSubcomplex d N).le_domain k j
      ((bandProj d N).mem k x)⟩ = (band (d := d) N j).starProjection ((complex d).d k j x) := hc
  rw [e, bandProj_apply, one_pow, one_mul]
  have h1 := Submodule.norm_starProjection_apply_le (band (d := d) N k) (x : L2Form d k)
  have h2 := Submodule.norm_starProjection_apply_le (band (d := d) N j) ((complex d).d k j x)
  gcongr

omit [Fintype d] [LinearOrder d] in
theorem zero_mem_bandN (N : ℕ) : (0 : d → ℤ) ∈ Fourier.Torus.bandN N := fun j => by simp

/-- **Harmonic forms are band-limited**: `π q = q` on `ℌᵏ`, for every `N`. -/
theorem bandProj_harmonic (N : ℕ) {k : ℕ} {q : L2Form d k} (hq : q ∈ (complex d).harmonic k) :
    (bandProj d N).π k q = q := by
  refine (bandProj d N).proj k q ?_
  change q ∈ band N k
  rw [Fourier.mem_band_iff, Measure.ae_count_iff]
  intro n hn
  exact mem_harmonic_iff.1 hq n fun h => hn (h ▸ zero_mem_bandN N)

/-- The harmonic gap of the Fourier truncation vanishes. -/
theorem norm_sub_bandProj_harmonic (N : ℕ) {k : ℕ} :
    ∀ q ∈ (complex d).harmonic k, ‖q - (bandProj d N).π k q‖ ≤ 0 * ‖q‖ := fun q hq => by
  rw [bandProj_harmonic N hq, sub_self, norm_zero, zero_mul]

/-- The Poincaré inequality of the torus in the form of the abstract theory. -/
theorem poincare {i j : ℕ} (hij : (ComplexShape.up ℕ).Rel i j)
    (z : ((complex d).d i j).domain) (hz : (z : L2Form d i) ∈ ((complex d).cycles i)ᗮ) :
    ‖(z : L2Form d i)‖ ≤ (2 * Real.pi)⁻¹ * ‖(complex d).d i j z‖ := by
  obtain rfl : i + 1 = j := hij
  rw [(complex d).cycles_eq (show (ComplexShape.up ℕ).Rel i (i + 1) from rfl)] at hz
  exact norm_le_of_mem_orthogonal z hz

/-- The constant of the spectral Galerkin estimate. -/
def bandConst : ℝ := (1 + 144 * (1 * √(1 + ((2 * Real.pi)⁻¹) ^ 2)) ^ 2) * (1 + 1)

set_option maxHeartbeats 2000000 in
/-- **Quasi-optimality of the spectral Galerkin mixed method** on the torus: the abstract
estimate ([AFW2010], Thm 3.9) with `C = 1`, `c_P = (2π)⁻¹` and `μ = 0`. -/
theorem norm_sub_le_bandGalerkin (N : ℕ) {i j k : ℕ} (hij : (ComplexShape.up ℕ).Rel i j)
    (hjk : (ComplexShape.up ℕ).Rel j k) {f : L2Form d j} {σ : (complex d).domainSpace i}
    {u : (complex d).domainSpace j} {p : (complex d).harmonic j}
    (hs : (complex d).IsMixedSolution i j k f σ u p) :
    ‖σ - (bandSubcomplex d N).embD i
          (HilbertComplex.Subcomplex.CochainProjection.discreteMixedSolution
            (bandSubcomplex d N) hij hjk f).fst‖ +
        ‖u - (bandSubcomplex d N).embD j
          (HilbertComplex.Subcomplex.CochainProjection.discreteMixedSolution
            (bandSubcomplex d N) hij hjk f).snd.fst‖ +
        ‖(p : L2Form d j) - (((HilbertComplex.Subcomplex.CochainProjection.discreteMixedSolution
            (bandSubcomplex d N) hij hjk f).snd.snd : (bandSubcomplex d N).V j) :
              L2Form d j)‖ ≤
      bandConst * (Metric.infDist σ ((bandSubcomplex d N).domainSub i) +
        Metric.infDist u ((bandSubcomplex d N).domainSub j) +
        Metric.infDist (p : L2Form d j) ((bandSubcomplex d N).harmonicW j)) := by
  have h := (bandProj d N).norm_sub_le_infDist hij hjk le_rfl le_rfl
    (poincare hij) (poincare hjk) (isGraphBounded_bandProj N i j) (isGraphBounded_bandProj N j k)
    (norm_sub_bandProj_harmonic N) hs
  rw [zero_mul, add_zero] at h
  refine h.trans_eq ?_
  rfl

/-! ### Convergence -/

variable (d) in
/-- The truncation of a point of `Vⁱ` as a point of the discrete domain space. -/
def truncD (N i : ℕ) (x : (complex d).domainSpace i) : (bandSubcomplex d N).toHilbertComplex.domainSpace i :=
  ((bandSubcomplex d N).toHilbertComplex.d i ((ComplexShape.up ℕ).next i)).toGraphSpace
    ⟨⟨(band (d := d) N i).starProjection ((complex d).domainIncl i x),
      Submodule.starProjection_apply_mem _ _⟩, Submodule.mem_top⟩

set_option maxHeartbeats 2000000 in
/-- `‖x - E(P_N x)‖_V ≤ ‖x - P_N x‖ + ‖d x - P_N d x‖`. -/
theorem norm_sub_embD_truncD_le (N i : ℕ) (x : (complex d).domainSpace i) :
    ‖x - (bandSubcomplex d N).embD i (truncD d N i x)‖ ≤
      ‖(complex d).domainIncl i x - (band (d := d) N i).starProjection ((complex d).domainIncl i x)‖ +
        ‖(complex d).d i ((ComplexShape.up ℕ).next i)
            ((complex d).domainCoord i ((ComplexShape.up ℕ).next i) x) -
          (band (d := d) N ((ComplexShape.up ℕ).next i)).starProjection
            ((complex d).d i ((ComplexShape.up ℕ).next i)
              ((complex d).domainCoord i ((ComplexShape.up ℕ).next i) x))‖ := by
  have hsq := (complex d).norm_sq_domainSpace i (x - (bandSubcomplex d N).embD i (truncD d N i x))
  have h1 : (complex d).domainIncl i (x - (bandSubcomplex d N).embD i (truncD d N i x)) =
      (complex d).domainIncl i x - (band (d := d) N i).starProjection ((complex d).domainIncl i x) := by
    rw [_root_.map_sub]; rfl
  have h2 : (complex d).d i ((ComplexShape.up ℕ).next i) ((complex d).domainCoord i ((ComplexShape.up ℕ).next i)
        (x - (bandSubcomplex d N).embD i (truncD d N i x))) =
      (complex d).d i ((ComplexShape.up ℕ).next i) ((complex d).domainCoord i ((ComplexShape.up ℕ).next i) x) -
        (band (d := d) N ((ComplexShape.up ℕ).next i)).starProjection
          ((complex d).d i ((ComplexShape.up ℕ).next i) ((complex d).domainCoord i ((ComplexShape.up ℕ).next i) x)) := by
    rw [_root_.map_sub, LinearPMap.map_sub]
    congr 1
    exact ((reducingSubcomplex_band (d := d) N).reduces i ((ComplexShape.up ℕ).next i)).comm
      ((complex d).domainCoord i ((ComplexShape.up ℕ).next i) x)
  rw [h1, h2] at hsq
  have hA := norm_nonneg ((complex d).domainIncl i x -
    (band (d := d) N i).starProjection ((complex d).domainIncl i x))
  have hB := norm_nonneg ((complex d).d i ((ComplexShape.up ℕ).next i) ((complex d).domainCoord i ((ComplexShape.up ℕ).next i) x) -
    (band (d := d) N ((ComplexShape.up ℕ).next i)).starProjection
      ((complex d).d i ((ComplexShape.up ℕ).next i) ((complex d).domainCoord i ((ComplexShape.up ℕ).next i) x)))
  refine (abs_le_of_sq_le_sq' ?_ (by positivity)).2
  rw [hsq]; nlinarith

private theorem tendsto_norm_sub_starProjection_band {k : ℕ} (v : L2Form d k) :
    Tendsto (fun N => ‖v - ((Fourier.Torus.symbolComplex (deRham d)).band
      (Fourier.Torus.bandN N) k).starProjection v‖) atTop (𝓝 0) := by
  have h := Fourier.tendsto_starProjection_band (Fourier.Torus.symbolComplex (deRham d))
    (fun N => (Fourier.Torus.finite_bandN N).measurableSet) Fourier.Torus.bandN_mono
    Fourier.Torus.exists_mem_bandN k v
  have := (tendsto_iff_norm_sub_tendsto_zero.1 h)
  simpa only [norm_sub_rev] using this

/-- `dist_V(x, Vₕⁱ) → 0` as `N → ∞`. -/
theorem tendsto_infDist_domainSub (i : ℕ) (x : (complex d).domainSpace i) :
    Tendsto (fun N => Metric.infDist x ((bandSubcomplex d N).domainSub i)) atTop (𝓝 0) := by
  have ht := (tendsto_norm_sub_starProjection_band (d := d) ((complex d).domainIncl i x)).add
    (tendsto_norm_sub_starProjection_band (d := d)
      ((complex d).d i ((ComplexShape.up ℕ).next i)
        ((complex d).domainCoord i ((ComplexShape.up ℕ).next i) x)))
  rw [add_zero] at ht
  refine squeeze_zero (fun _ => Metric.infDist_nonneg) (fun N => ?_) ht
  refine (Metric.infDist_le_dist_of_mem ((bandSubcomplex d N).mem_domainSub (truncD d N i x))).trans ?_
  rw [dist_eq_norm]
  exact norm_sub_embD_truncD_le N i x

/-- Harmonic forms are discrete harmonic forms of every band subcomplex. -/
theorem mem_harmonicW_band (N : ℕ) {j : ℕ} {p : L2Form d j} (hp : p ∈ (complex d).harmonic j) :
    p ∈ (bandSubcomplex d N).harmonicW j := by
  refine (bandSubcomplex d N).mem_harmonicW_iff.2 ⟨?_, (complex d).harmonic_le_cycles j hp,
    fun b hb => ?_⟩
  · rw [← bandProj_harmonic N hp]; exact (bandProj d N).mem j p
  · exact Submodule.inner_right_of_mem_orthogonal ((bandSubcomplex d N).boundariesW_le j hb)
      ((complex d).mem_harmonic_iff.1 hp).2

/-- **Convergence of the spectral Galerkin mixed method** on the torus: the discrete mixed
solutions on the bands `|n|_∞ ≤ N` converge to the solution of the mixed Hodge Laplacian in the
norm of `Vⁱ × Vʲ × Wʲ`. -/
theorem tendsto_bandGalerkin {i j k : ℕ} (hij : (ComplexShape.up ℕ).Rel i j)
    (hjk : (ComplexShape.up ℕ).Rel j k) {f : L2Form d j} {σ : (complex d).domainSpace i}
    {u : (complex d).domainSpace j} {p : (complex d).harmonic j}
    (hs : (complex d).IsMixedSolution i j k f σ u p) :
    Tendsto (fun N => ‖σ - (bandSubcomplex d N).embD i
          (HilbertComplex.Subcomplex.CochainProjection.discreteMixedSolution
            (bandSubcomplex d N) hij hjk f).fst‖ +
        ‖u - (bandSubcomplex d N).embD j
          (HilbertComplex.Subcomplex.CochainProjection.discreteMixedSolution
            (bandSubcomplex d N) hij hjk f).snd.fst‖ +
        ‖(p : L2Form d j) - (((HilbertComplex.Subcomplex.CochainProjection.discreteMixedSolution
            (bandSubcomplex d N) hij hjk f).snd.snd : (bandSubcomplex d N).V j) :
              L2Form d j)‖) atTop (𝓝 0) := by
  refine squeeze_zero (fun _ => by positivity) (fun N => norm_sub_le_bandGalerkin N hij hjk hs) ?_
  have hp : ∀ N, Metric.infDist (p : L2Form d j) ((bandSubcomplex d N).harmonicW j) = 0 :=
    fun N => Metric.infDist_zero_of_mem (mem_harmonicW_band N p.2)
  simp only [hp, add_zero]
  have := ((tendsto_infDist_domainSub i σ).add (tendsto_infDist_domainSub j u)).const_mul bandConst
  simpa using this

end Feec.Models.Torus.DeRham
