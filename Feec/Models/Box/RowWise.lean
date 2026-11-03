module

public import Feec.Models.Cube.RowWiseIdent
public import Feec.Domain.DiagonalPullback

/-!
# The thesis' complex on a box with unequal sides: the anisotropic parity model

For a box `B = ∏ (aᵢ, aᵢ + ℓᵢ)` (`ℓᵢ > 0`, not necessarily equal) the diagonal affine map
`T x = d * (x - a)`, `dᵢ = 1/(2ℓᵢ)`, maps `B` onto the cube `Q = (0, ½)³`. Unlike for a cube
(`Feec.Models.Cube.Ident`), the pull-back does not just rescale the complex: by the chain rule
(`Feec.Domain.ConstCoeffOp.minimal_pullDiag`) the complex `H̊¹(B) → H̊(curl, B) → L²(B)`
(`Feec.Models.BoundedDomain.gradCurl`) becomes on `Q` the **weighted complex** of
`grad_d`, `curl_d` (`∂ᵢ ↦ dᵢ ∂ᵢ`). Its Fourier model is the torus symbol complex of the grad–curl
fibre complex along the **anisotropic frequency map** `n ↦ ξ_d(n) = d * 2πn`
(`Box.symD`, `Feec.Fourier.FibreComplex.toSymbolComplex`), compressed along the row-wise parity
extension `J` of `Feec.Models.Cube.RowWise`.

The comparison goes through the cube: with the column scalings `D = diag d`,
`grad_{ξ_d} = (grad_ξ ·) D` and `curl_{ξ_d} (E D) = det D · (curl_ξ E) D⁻¹` (fibrewise,
`Box.gradCurl_m_dfreq`; on test fields `Feec.Domain.curlOp_diagScale_smul`), so

* the anisotropic torus complex is the transport of the real torus grad–curl complex along the
  constant fibre scalings `Box.phiT` (`Box.realD_eq_torusD`);
* the box complex is the transport of the cube complex along the scalings `Box.phiQ` followed by
  the pull-back (`Box.complexBox_eq_transport`), and the scalings commute with `J` and with the
  row-wise reflections (they act entrywise on the columns, which carry the parities);
* hence the box complex **is the compression** of the anisotropic torus complex along `J ∘ P⁻¹`
  (`Box.complexBox_eq_compress`, from `Feec.Models.Cube.RowWise.cubeComplex_eq_compress`).

The fibre spectral facts only use `ξ ≠ 0`: the nonzero eigenvalue of `-W_ξ²` is `|ξ|²`
(`Feec.Models.Cube.Parity.eq_zero_of_slots`, valid at every `ξ`), the frequencies on a sphere
`|ξ_d(n)| = ω` form a finite set (`Box.finite_dfreq`), `ξ_d(n) = 0` only for `n = 0`; and the
vanishing of trigonometric polynomials in a row-wise parity class that are symmetric and
trace-free on `Q` (`Feec.Models.Cube.Parity.eq_zero_of_finite_of_parity`) does not involve the
frequencies at all. So the spectral results of the torus hold along every frequency map with
finite spheres that vanishes only at `0` (`Feec.Models.Cube.Parity.symAlong`), and in particular
on the anisotropic torus (`Box.mem_invariantCore_torusD_iff`, `Box.mem_stationary_torusD_of`).

## Main definitions

* `Box.openBox`, `Box.dB`, `Box.bB`: the box and the map onto `Q`.
* `Box.dfreq`, `Box.symD`, `Box.realD`: the anisotropic torus complex; `Box.phiT`, `Box.torusD`.
* `Box.phiQ`, `Box.JB`, `Box.complexBox`.

## Main results

* `HilbertComplex.Involutions.transport`, `HilbertComplex.eq_compress_of`,
  `HilbertComplex.transport_transport_compress`.
* `Box.gradCurl_m_dfreq`, **`Box.realD_eq_torusD`**, `Box.eigenDense_torusD`,
  `Box.isPurePoint_torusD`, `Box.finite_dfreq`.
* **`Box.complexBox_eq_compress`**.
* **`Box.mem_invariantCore_torusD_iff`**, `Box.mem_stationary_torusD_of`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (the complex `H̊¹ → H̊(curl) → L²`, Prop 4.17)
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.2 (extension by reflection, change of variables)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory Set LinearPMap Feec.Fourier Feec.ShortHilbertComplex

@[expose] public noncomputable section

/-! ### Transport, compression and involutions -/

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W V V' : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)] [∀ i, CompleteSpace (V i)]
  [∀ i, NormedAddCommGroup (V' i)] [∀ i, InnerProductSpace 𝕜 (V' i)] [∀ i, CompleteSpace (V' i)]

/-- **Involutions commuting with the weights pass to the transport** (chain-rule factors `1`). -/
def Involutions.transport {H : HilbertComplex 𝕜 c W} {κ : Type*} (I : H.Involutions κ)
    (e : ∀ i, W i ≃L[𝕜] W i) (he : ∀ k i x, e i (I.R k i x) = I.R k i (e i x)) :
    (H.transport e (fun _ _ => 1) fun _ _ => one_ne_zero).Involutions κ where
  R := I.R
  invol := I.invol
  comm := I.comm
  mapsTo k i j x := by
    have hs : (e i).symm (I.R k i x) = I.R k i ((e i).symm x) := by
      apply (e i).injective
      rw [ContinuousLinearEquiv.apply_symm_apply, he, ContinuousLinearEquiv.apply_symm_apply]
    change (e i).symm (I.R k i x) ∈ (H.d i j).domain
    rw [hs]
    exact I.mapsTo k i j ⟨_, x.2⟩
  comm_d k i j x := by
    have hs : (e i).symm (I.R k i x) = I.R k i ((e i).symm x) := by
      apply (e i).injective
      rw [ContinuousLinearEquiv.apply_symm_apply, he, ContinuousLinearEquiv.apply_symm_apply]
    change (1 : 𝕜) • e j (H.d i j ⟨(e i).symm (I.R k i x), _⟩) =
      I.R k j ((1 : 𝕜) • e j (H.d i j ⟨(e i).symm x, x.2⟩))
    rw [one_smul, one_smul, ← he]
    refine congrArg (e j) ((apply_congr' (H.d i j) _ (I.mapsTo k i j ⟨_, x.2⟩) hs).trans ?_)
    exact I.comm_d k i j ⟨_, x.2⟩

variable {H : HilbertComplex 𝕜 c W} {J : ∀ i, V i →L[𝕜] W i} {s : ℝ}
  [∀ i, (LinearMap.range (J i : V i →ₗ[𝕜] W i)).HasOrthogonalProjection]

/-- **A criterion for compressions**: a complex `H'` whose domains are the preimages of those of
`H` under `J` and whose differentials are intertwined by `J` is the compression of `H`. -/
theorem eq_compress_of (hs : 0 < s) (hJ : ∀ i (x y : V i), ⟪J i x, J i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜)
    (hR : H.ReducingSubcomplex fun i => LinearMap.range (J i : V i →ₗ[𝕜] W i))
    {H' : HilbertComplex 𝕜 c V}
    (hdom : ∀ i j (x : V i), x ∈ (H'.d i j).domain ↔ J i x ∈ (H.d i j).domain)
    (hcomm : ∀ i j (x : (H'.d i j).domain),
      J j (H'.d i j x) = H.d i j ⟨J i x, (hdom i j x).1 x.2⟩) :
    H' = H.compress J hs hJ hR := by
  refine ext_d (funext fun i => funext fun j => ?_)
  refine LinearPMap.ext (Submodule.ext fun x => ?_) fun x hx hx' => ?_
  · rw [mem_compress_domain_iff]; exact hdom i j x
  · refine (ScaledEmbedding.ofCompress hs hJ hR).J_injective j ?_
    change J j _ = J j _
    rw [J_compress_d, hcomm i j ⟨x, hx⟩]

/-- **Transports of a compression are compressions of a transport**: if `J φ = ψ J`, then
transporting the compression `H_J` along `φ` and then along `P` is the compression of the
transport of `H` along `ψ`, along `J ∘ P⁻¹`. -/
theorem transport_transport_compress (hs : 0 < s)
    (hJ : ∀ i (x y : V i), ⟪J i x, J i y⟫_𝕜 = (s : 𝕜) * ⟪x, y⟫_𝕜)
    (hR : H.ReducingSubcomplex fun i => LinearMap.range (J i : V i →ₗ[𝕜] W i))
    (φ : ∀ i, V i ≃L[𝕜] V i) (ψ : ∀ i, W i ≃L[𝕜] W i) (hφψ : ∀ i x, J i (φ i x) = ψ i (J i x))
    (P : ∀ i, V i ≃L[𝕜] V' i) {s' : ℝ} (hs' : 0 < s')
    (hJ' : ∀ i (x y : V' i), ⟪(J i ∘L ((P i).symm : V' i →L[𝕜] V i)) x,
      (J i ∘L ((P i).symm : V' i →L[𝕜] V i)) y⟫_𝕜 = (s' : 𝕜) * ⟪x, y⟫_𝕜)
    [∀ i, (LinearMap.range ((J i ∘L ((P i).symm : V' i →L[𝕜] V i)) :
      V' i →ₗ[𝕜] W i)).HasOrthogonalProjection]
    (hR' : (H.transport ψ (fun _ _ => 1) fun _ _ => one_ne_zero).ReducingSubcomplex fun i =>
      LinearMap.range ((J i ∘L ((P i).symm : V' i →L[𝕜] V i)) : V' i →ₗ[𝕜] W i)) :
    ((H.compress J hs hJ hR).transport φ (fun _ _ => 1) fun _ _ => one_ne_zero).transport P
        (fun _ _ => 1) (fun _ _ => one_ne_zero) =
      (H.transport ψ (fun _ _ => 1) fun _ _ => one_ne_zero).compress
        (fun i => J i ∘L ((P i).symm : V' i →L[𝕜] V i)) hs' hJ' hR' := by
  have hψ : ∀ i y, (ψ i).symm (J i y) = J i ((φ i).symm y) := fun i y => by
    rw [ContinuousLinearEquiv.symm_apply_eq, ← hφψ, ContinuousLinearEquiv.apply_symm_apply]
  have hdom : ∀ i j (x : V' i), x ∈ ((((H.compress J hs hJ hR).transport φ (fun _ _ => 1)
      fun _ _ => one_ne_zero).transport P (fun _ _ => 1) fun _ _ => one_ne_zero).d i j).domain ↔
      (J i ∘L ((P i).symm : V' i →L[𝕜] V i)) x ∈
        ((H.transport ψ (fun _ _ => 1) fun _ _ => one_ne_zero).d i j).domain := fun i j x => by
    change (φ i).symm ((P i).symm x) ∈ ((H.compress J hs hJ hR).d i j).domain ↔
      (ψ i).symm (J i ((P i).symm x)) ∈ (H.d i j).domain
    rw [mem_compress_domain_iff, hψ]
  refine eq_compress_of hs' hJ' hR' hdom fun i j x => ?_
  have hx : (φ i).symm ((P i).symm (x : V' i)) ∈ ((H.compress J hs hJ hR).d i j).domain := x.2
  change J j ((P j).symm ((1 : 𝕜) • P j ((1 : 𝕜) • φ j ((H.compress J hs hJ hR).d i j
      ⟨(φ i).symm ((P i).symm x), hx⟩)))) =
    (1 : 𝕜) • ψ j (H.d i j ⟨(ψ i).symm (J i ((P i).symm x)), _⟩)
  rw [one_smul, one_smul, one_smul, ContinuousLinearEquiv.symm_apply_apply, hφψ, J_compress_d]
  exact congrArg (ψ j) (apply_congr' _ _ _ (hψ i _).symm)

end Feec.HilbertComplex

namespace Feec.Models.Box

open Feec.Models.Torus.GradCurl (Space)
open Feec.Fourier.GradCurl
open Models.BoundedDomain (R3 Ix)
open Models.Cube (Parity.colR Parity.fib Parity.cjF)
open Models.Cube.MirrorTorus (sgn)

/- Over `ℝ`, the real structure of `W3` is the one of its inner product space. -/
attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3

attribute [local instance] Models.Cube.RealTorus.isScalarTower

/-! ### The column scalings -/

variable {d : R3}

/-- The column weights `(a, b) ↦ d_b` of `E ↦ E D`. -/
def w1 (d : R3) : Ix → ℝ := fun p => d p.2

/-- The column weights `(a, b) ↦ d_{b+1} d_{b+2}` of `B ↦ det D · B D⁻¹`. -/
def w2 (d : R3) : Ix → ℝ := fun p => d (p.2 + 1) * d (p.2 + 2)

theorem w1_ne_zero (hd : ∀ i, 0 < d i) (p : Ix) : w1 d p ≠ 0 := (hd _).ne'

theorem w2_ne_zero (hd : ∀ i, 0 < d i) (p : Ix) : w2 d p ≠ 0 := (mul_pos (hd _) (hd _)).ne'

/-- The entrywise scaling `v ↦ (wₚ vₚ)ₚ` of `ℂ^P` by real weights. -/
def eScale {P : Type*} [Fintype P] (w : P → ℝ) (hw : ∀ p, w p ≠ 0) :
    EuclideanSpace ℂ P ≃L[ℂ] EuclideanSpace ℂ P :=
  (PiLp.continuousLinearEquiv 2 ℂ _).trans
    ((ContinuousLinearEquiv.piCongrRight fun p =>
      Domain.ConstCoeffOp.scaleL ((w p : ℝ) : ℂ) (Complex.ofReal_ne_zero.2 (hw p))).trans
      (PiLp.continuousLinearEquiv 2 ℂ _).symm)

@[simp] theorem eScale_apply {P : Type*} [Fintype P] (w : P → ℝ) (hw : ∀ p, w p ≠ 0)
    (v : EuclideanSpace ℂ P) (p : P) : eScale w hw v p = (w p : ℂ) * v p := rfl

@[simp] theorem eScale_symm_apply {P : Type*} [Fintype P] (w : P → ℝ) (hw : ∀ p, w p ≠ 0)
    (v : EuclideanSpace ℂ P) (p : P) : (eScale w hw).symm v p = ((w p : ℂ))⁻¹ * v p := rfl

/-- The fibre scalings of the three slots: `σ ↦ σ`, `E ↦ E D`, `B ↦ det D · B D⁻¹`. -/
def fibW (hd : ∀ i, 0 < d i) : ∀ i : Fin 3, W3 Vec Mat Mat i ≃L[ℂ] W3 Vec Mat Mat i
  | 0 => ContinuousLinearEquiv.refl ℂ Vec
  | 1 => eScale (w1 d) (w1_ne_zero hd)
  | 2 => eScale (w2 d) (w2_ne_zero hd)

/-- The anisotropic frequencies `ξ_d(n) = d * 2πn`. -/
def dfreq (d : R3) (n : Fin 3 → ℤ) : Freq := WithLp.toLp 2 fun j => d j * Fourier.Torus.freq n j

@[simp] theorem dfreq_apply (d : R3) (n : Fin 3 → ℤ) (j : Fin 3) :
    dfreq d n j = d j * (2 * Real.pi * n j) := rfl

theorem grad_dfreq (hd : ∀ i, 0 < d i) (n : Fin 3 → ℤ) (u : Vec) :
    grad (dfreq d n) u = eScale (w1 d) (w1_ne_zero hd) (grad (Fourier.Torus.freq n) u) := by
  ext ⟨a, b⟩
  simp only [grad_apply, eScale_apply, dfreq_apply, Fourier.Torus.freq_apply, w1]
  push_cast
  ring

theorem curl_dfreq (hd : ∀ i, 0 < d i) (n : Fin 3 → ℤ) (M : Mat) :
    curl (dfreq d n) M = eScale (w2 d) (w2_ne_zero hd)
      (curl (Fourier.Torus.freq n) ((eScale (w1 d) (w1_ne_zero hd)).symm M)) := by
  ext ⟨a, b⟩
  have h0 : (d 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hd 0).ne'
  have h1 : (d 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hd 1).ne'
  have h2 : (d 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hd 2).ne'
  simp only [curl_apply, eScale_apply, eScale_symm_apply, dfreq_apply,
    Fourier.Torus.freq_apply, w1, w2, Fin.sum_univ_three, leviCivita3_apply]
  fin_cases b <;> simp <;> field_simp

/-- **The fibre identity**: `grad_{ξ_d} = (grad_ξ ·) D` and
`curl_{ξ_d} = (det D · (·) D⁻¹) ∘ curl_ξ ∘ (· D)⁻¹`. -/
theorem gradCurl_m_dfreq (hd : ∀ i, 0 < d i) (i j : Fin 3) (n : Fin 3 → ℤ)
    (v : W3 Vec Mat Mat i) :
    gradCurl.m i j (dfreq d n) v =
      fibW hd j (gradCurl.m i j (Fourier.Torus.freq n) ((fibW hd i).symm v)) := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact grad_dfreq hd n v
    | exact curl_dfreq hd n v
    | (change (0 : _ →L[ℂ] _) _ = fibW hd _ ((0 : _ →L[ℂ] _) _); simp)

/-! ### The anisotropic torus complex -/

theorem compLpL_count_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (L : E →L[ℂ] E) (u : Lp E 2 (Measure.count : Measure (Fin 3 → ℤ))) (n : Fin 3 → ℤ) :
    (L.compLpL 2 (Measure.count : Measure (Fin 3 → ℤ)) u : (Fin 3 → ℤ) → E) n = L (u n) :=
  Measure.ae_count_iff.1 (ContinuousLinearMap.coeFn_compLpL L u) n

/-- The constant fibre map `u ↦ (L (u n))ₙ` of `L²(ℤ³, count)`. -/
def cfib {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (L : E ≃L[ℂ] E) :
    Lp E 2 (Measure.count : Measure (Fin 3 → ℤ)) ≃L[ℂ]
      Lp E 2 (Measure.count : Measure (Fin 3 → ℤ)) :=
  ContinuousLinearEquiv.equivOfInverse
    ((L : E →L[ℂ] E).compLpL 2 (Measure.count : Measure (Fin 3 → ℤ)))
    ((L.symm : E →L[ℂ] E).compLpL 2 (Measure.count : Measure (Fin 3 → ℤ)))
    (fun u => Lp.ext_count fun n => by
      rw [compLpL_count_apply, compLpL_count_apply]
      exact L.symm_apply_apply _)
    (fun u => Lp.ext_count fun n => by
      rw [compLpL_count_apply, compLpL_count_apply]
      exact L.apply_symm_apply _)

theorem coeFn_cfib {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (L : E ≃L[ℂ] E)
    (u : Lp E 2 (Measure.count : Measure (Fin 3 → ℤ))) (n : Fin 3 → ℤ) :
    (cfib L u : (Fin 3 → ℤ) → E) n = L (u n) :=
  compLpL_count_apply _ u n

theorem coeFn_cfib_symm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (L : E ≃L[ℂ] E) (u : Lp E 2 (Measure.count : Measure (Fin 3 → ℤ))) (n : Fin 3 → ℤ) :
    ((cfib L).symm u : (Fin 3 → ℤ) → E) n = L.symm (u n) :=
  compLpL_count_apply _ u n

/-- The weights of the anisotropic torus complex: the constant fibre scalings `fibW`, as real
isomorphisms of the torus spaces. -/
def phiT (hd : ∀ i, 0 < d i) (i : Fin 3) : Space i ≃L[ℝ] Space i :=
  (cfib (fibW hd i)).restrictScalars ℝ

theorem coeFn_phiT (hd : ∀ i, 0 < d i) (i : Fin 3) (u : Space i) (n : Fin 3 → ℤ) :
    (phiT hd i u : (Fin 3 → ℤ) → W3 Vec Mat Mat i) n = fibW hd i (u n) :=
  coeFn_cfib _ u n

theorem coeFn_phiT_symm (hd : ∀ i, 0 < d i) (i : Fin 3) (u : Space i) (n : Fin 3 → ℤ) :
    ((phiT hd i).symm u : (Fin 3 → ℤ) → W3 Vec Mat Mat i) n = (fibW hd i).symm (u n) :=
  coeFn_cfib_symm _ u n

variable (d) in
/-- **The anisotropic torus symbol complex**: the grad–curl fibre complex along the frequency
map `n ↦ ξ_d(n) = d * 2πn`. -/
abbrev symD : SymbolComplex ℂ (Measure.count : Measure (Fin 3 → ℤ)) ComplexShape.fin3
    (W3 Vec Mat Mat) :=
  Models.Cube.Parity.symAlong (dfreq d)

@[simp] theorem symD_m (i j : Fin 3) (n : Fin 3 → ℤ) :
    (symD d).m i j n = gradCurl.m i j (dfreq d n) := rfl

variable (d) in
/-- The anisotropic torus complex over `ℂ`. -/
abbrev complexD : HilbertComplex ℂ ComplexShape.fin3 Space := (symD d).toHilbertComplex

variable (d) in
/-- **The anisotropic torus complex over `ℝ`.** -/
abbrev realD : HilbertComplex ℝ ComplexShape.fin3 Space := (complexD d).restrictScalars

/-- The transport of the real torus grad–curl complex along the fibre scalings. -/
abbrev torusD (hd : ∀ i, 0 < d i) : HilbertComplex ℝ ComplexShape.fin3 Space :=
  Models.Cube.RealTorus.gradCurl.transport (phiT hd) (fun _ _ => 1) fun _ _ => one_ne_zero

/-- **The anisotropic torus complex is the transport of the torus complex along the column
scalings** (domains included). -/
theorem realD_eq_torusD (hd : ∀ i, 0 < d i) : realD d = torusD hd := by
  refine HilbertComplex.ext_d (funext fun i => funext fun j => ?_)
  have hpt : ∀ x : Space i, ∀ n, (symD d).m i j n ((x : (Fin 3 → ℤ) → W3 Vec Mat Mat i) n) =
      fibW hd j (gradCurl.m i j (Fourier.Torus.freq n)
        (((phiT hd i).symm x : (Fin 3 → ℤ) → W3 Vec Mat Mat i) n)) := fun x n => by
    rw [symD_m, gradCurl_m_dfreq hd, coeFn_phiT_symm]
  refine LinearPMap.ext (Submodule.ext fun x => ?_) fun x hx hx' => ?_
  · change MemLp (fun n => (symD d).m i j n ((x : (Fin 3 → ℤ) → W3 Vec Mat Mat i) n)) 2 _ ↔
      MemLp (fun n => gradCurl.m i j (Fourier.Torus.freq n)
        (((phiT hd i).symm x : (Fin 3 → ℤ) → W3 Vec Mat Mat i) n)) 2 _
    simp only [hpt]
    constructor
    · intro h
      have := ((fibW hd j).symm : W3 Vec Mat Mat j →L[ℂ] W3 Vec Mat Mat j).comp_memLp' h
      refine this.ae_eq (Filter.Eventually.of_forall fun n => ?_)
      exact (fibW hd j).symm_apply_apply _
    · intro h
      exact ((fibW hd j : W3 Vec Mat Mat j →L[ℂ] W3 Vec Mat Mat j)).comp_memLp' h
  · refine Lp.ext_count fun n => ?_
    change ((symD d).toHilbertComplex.d i j ⟨x, hx⟩ : (Fin 3 → ℤ) → W3 Vec Mat Mat j) n =
      (((1 : ℝ) • phiT hd j (Models.Torus.GradCurl.complex.d i j ⟨(phiT hd i).symm x, hx'⟩) :
        Space j) : (Fin 3 → ℤ) → W3 Vec Mat Mat j) n
    rw [one_smul, coeFn_phiT, Fourier.coeFn_d_count, hpt]
    congr 1
    exact (Fourier.coeFn_d_count (Fourier.Torus.symbolComplex gradCurl)
      ⟨(phiT hd i).symm x, hx'⟩ n).symm

/-! ### The spectrum of the anisotropic torus complex -/

section Spectral

open Models.Cube (rowAction)

theorem dfreq_eq_zero_iff {n : Fin 3 → ℤ} (hd : ∀ i, 0 < d i) : dfreq d n = 0 ↔ n = 0 := by
  constructor
  · intro h
    funext j
    have := congrArg (fun ξ : Freq => ξ j) h
    simp only [dfreq_apply, PiLp.zero_apply] at this
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    have : (n j : ℝ) = 0 := by
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd h1 (hd j).ne'
      · rcases mul_eq_zero.1 h1 with h2 | h2
        · exact absurd h2 hpi
        · exact h2
    exact_mod_cast this
  · rintro rfl
    ext j
    simp

/-- **The anisotropic torus wave group has an eigenbasis** (the Fourier modes,
`Feec.Models.Cube.Parity.eigenDense_symAlong`). -/
theorem eigenDense_torusD (hd : ∀ i, 0 < d i) : (torusD hd).waveGroup.EigenDense := by
  rw [← realD_eq_torusD hd]; exact Models.Cube.Parity.eigenDense_symAlong _

/-- **The anisotropic torus wave group has pure point spectrum.** -/
theorem isPurePoint_torusD (hd : ∀ i, 0 < d i) : (torusD hd).waveGroup.IsPurePoint :=
  (torusD hd).isIsometric_waveGroup.isPurePoint_of_eigenDense (eigenDense_torusD hd)

/-- **The anisotropic frequencies on a sphere `|ξ_d(n)| = ω` form a finite set.** -/
theorem finite_dfreq (hd : ∀ i, 0 < d i) (ω : ℝ) : {n : Fin 3 → ℤ | ‖dfreq d n‖ = ω}.Finite := by
  refine (Fourier.Torus.finite_bandN (Nat.ceil (ω * ∑ j, (d j)⁻¹))).subset fun n hn j => ?_
  have hn : ‖dfreq d n‖ = ω := hn
  have h1 : ‖(dfreq d n) j‖ ≤ ω := hn ▸ PiLp.norm_apply_le _ j
  rw [dfreq_apply, Real.norm_eq_abs, abs_mul, abs_of_pos (hd j), abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h1
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.two_le_pi]
  have h2 : |(n j : ℝ)| ≤ ω * (d j)⁻¹ := by
    rw [le_mul_inv_iff₀ (hd j)]
    have : |(n j : ℝ)| * d j ≤ d j * (2 * Real.pi * |(n j : ℝ)|) := by
      nlinarith [mul_nonneg (mul_nonneg (hd j).le (abs_nonneg (n j : ℝ))) (sub_nonneg.2 hpi)]
    linarith
  have h3 : ω * (d j)⁻¹ ≤ ω * ∑ j, (d j)⁻¹ := by
    have hω : 0 ≤ ω := hn ▸ norm_nonneg _
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun j => (d j)⁻¹)
      (fun j _ => (inv_pos.2 (hd j)).le) (Finset.mem_univ j)) hω
  have : |(n j : ℝ)| ≤ (Nat.ceil (ω * ∑ j, (d j)⁻¹) : ℝ) := (h2.trans h3).trans (Nat.le_ceil _)
  exact_mod_cast this

/-- **`K*` on the anisotropic torus**: for closed `S₁, S₂` of symmetric trace-free (on `Q`) fields
of the electric and magnetic parity classes, the invariant core of `{0} × S₁ × S₂` under the
anisotropic torus wave group consists of its stationary data. -/
theorem mem_invariantCore_torusD_iff (hd : ∀ i, 0 < d i) {S1 : Submodule ℝ (Space 1)}
    {S2 : Submodule ℝ (Space 2)} [S1.HasOrthogonalProjection] [S2.HasOrthogonalProjection]
    (hS1 : S1 ≤ rowAction.fixed 1 ⊓ Models.Cube.Parity.boxSym ⊓ Models.Cube.Parity.boxTr)
    (hS2 : S2 ≤ rowAction.fixed 2 ⊓ Models.Cube.Parity.boxSym ⊓ Models.Cube.Parity.boxTr)
    (y : PiLp 2 Space) :
    y ∈ (torusD hd).waveGroup.invariantCore
        (HilbertComplex.totalSub (Models.Cube.Parity.constraint S1 S2)) ↔
      y ∈ HilbertComplex.totalSub (Models.Cube.Parity.constraint S1 S2) ∧
        y ∈ (torusD hd).waveGroup.stationary := by
  rw [← realD_eq_torusD hd]
  exact Models.Cube.Parity.mem_invariantCore_symAlong_iff _ (finite_dfreq hd) hS1 hS2 y

/-- **Stationary data `(σ, E, B)` of the anisotropic torus complex with `E` of electric parity
have `E = 0`** (the electric harmonic fields vanish). -/
theorem mem_stationary_torusD_of (hd : ∀ i, 0 < d i) {y : PiLp 2 Space}
    (h1 : (y 1 : Space 1) ∈ rowAction.fixed 1)
    (hst : y ∈ (torusD hd).waveGroup.stationary) : (y 1 : Space 1) = 0 := by
  rw [← realD_eq_torusD hd] at hst
  exact Models.Cube.Parity.eq_zero_of_mem_stationary_symAlong _
    (fun _ => (dfreq_eq_zero_iff hd).1) h1 hst

end Spectral

/-! ### The parity extension and the weights -/

section Weights

open Models.Cube (rowAction)
open Models.Cube.Parity (fib cjF colR realR realInvolutions)
open Models.Cube.Geometry (Q)
open Models.Cube.RowWise (J JR WQ)

theorem fibW_fib (hd : ∀ i, 0 < d i) (k i : Fin 3) (v : W3 Vec Mat Mat i) :
    fibW hd i (fib k i v) = fib k i (fibW hd i v) := by
  fin_cases i
  · rfl
  · revert v
    show ∀ v : Mat, eScale (w1 d) (w1_ne_zero hd) (-colR k v) =
      -colR k (eScale (w1 d) (w1_ne_zero hd) v)
    intro v; ext p; simp only [eScale_apply, PiLp.neg_apply, Models.Cube.Parity.colR_apply]; ring
  · revert v
    show ∀ v : Mat, eScale (w2 d) (w2_ne_zero hd) (colR k v) =
      colR k (eScale (w2 d) (w2_ne_zero hd) v)
    intro v; ext p; simp only [eScale_apply, Models.Cube.Parity.colR_apply]; ring

theorem fibW_cjF (hd : ∀ i, 0 < d i) (i : Fin 3) (v : W3 Vec Mat Mat i) :
    fibW hd i (cjF i v) = cjF i (fibW hd i v) := by
  fin_cases i
  · rfl
  · revert v
    show ∀ v : Mat, eScale (w1 d) (w1_ne_zero hd) (entryConj v) =
      entryConj (eScale (w1 d) (w1_ne_zero hd) v)
    intro v; ext p; simp [eScale_apply, entryConj_apply]
  · revert v
    show ∀ v : Mat, eScale (w2 d) (w2_ne_zero hd) (entryConj v) =
      entryConj (eScale (w2 d) (w2_ne_zero hd) v)
    intro v; ext p; simp [eScale_apply, entryConj_apply]

/-- **The weights commute with the row-wise reflections and the conjugation.** -/
theorem phiT_realR (hd : ∀ i, 0 < d i) (k : Option (Fin 3)) (i : Fin 3) (x : Space i) :
    phiT hd i (realR k i x) = realR k i (phiT hd i x) := by
  cases k with
  | none =>
    refine Lp.ext_count fun n => ?_
    change (phiT hd i (Models.Cube.Parity.cnj i x) : (Fin 3 → ℤ) → W3 Vec Mat Mat i) n =
      (Models.Cube.Parity.cnj i (phiT hd i x) : (Fin 3 → ℤ) → W3 Vec Mat Mat i) n
    rw [coeFn_phiT, Models.Cube.Parity.coeFn_cnj, Models.Cube.Parity.coeFn_cnj, coeFn_phiT,
      fibW_cjF]
  | some k =>
    refine Lp.ext_count fun n => ?_
    change (phiT hd i (Models.Cube.Parity.refl k i x) : (Fin 3 → ℤ) → W3 Vec Mat Mat i) n =
      (Models.Cube.Parity.refl k i (phiT hd i x) : (Fin 3 → ℤ) → W3 Vec Mat Mat i) n
    rw [coeFn_phiT, Models.Cube.Parity.coeFn_refl, Models.Cube.Parity.coeFn_refl, coeFn_phiT,
      fibW_fib]

/-- The row-wise reflections and the conjugation of the anisotropic torus complex. -/
def realInvolutionsD (hd : ∀ i, 0 < d i) : (torusD hd).Involutions (Option (Fin 3)) :=
  realInvolutions.transport (phiT hd) fun k i x => phiT_realR hd k i x

theorem fixed_realInvolutionsD (hd : ∀ i, 0 < d i) (i : Fin 3) :
    (realInvolutionsD hd).toAction.fixed i = Models.Cube.Parity.realAction.fixed i := by
  ext x
  rw [HilbertComplex.Involutions.mem_fixed_toAction, HilbertComplex.Involutions.mem_fixed_toAction]
  rfl

/-- **The real parity fields reduce the anisotropic torus complex.** -/
theorem reducingSubcomplex_range (hd : ∀ i, 0 < d i) :
    (torusD hd).ReducingSubcomplex fun i => LinearMap.range (J i : WQ i →ₗ[ℝ] Space i) := by
  have h := (realInvolutionsD hd).toAction.reducingSubcomplex_fixed
  refine ⟨fun i j => ?_⟩
  convert h.reduces i j using 1 <;> rw [fixed_realInvolutionsD, Models.Cube.RowWise.range_J]

/-- The weights of the cube complex: `σ ↦ σ`, `E ↦ E D`, `B ↦ det D · B D⁻¹`, entrywise. -/
def phiQ (hd : ∀ i, 0 < d i) : ∀ i : Fin 3, WQ i ≃L[ℝ] WQ i
  | 0 => Domain.ConstCoeffOp.scaleF (fun _ => (1 : ℝ)) fun _ => one_ne_zero
  | 1 => Domain.ConstCoeffOp.scaleF (w1 d) (w1_ne_zero hd)
  | 2 => Domain.ConstCoeffOp.scaleF (w2 d) (w2_ne_zero hd)

theorem JR_scaleF {P : Type*} [Fintype P] (pc : P → Fin 3 → ℂ) (w : P → ℝ) (hw : ∀ p, w p ≠ 0)
    (u : Domain.L2F ℝ (Q (Fin 3)) P) :
    JR pc (Domain.ConstCoeffOp.scaleF w hw u) = cfib (eScale w hw) (JR pc u) := by
  refine Lp.ext_count fun n => ?_
  ext p
  rw [coeFn_cfib, eScale_apply, Models.Cube.RowWise.coeff_JR, Models.Cube.RowWise.coeff_JR,
    Domain.ConstCoeffOp.scaleF_apply]
  have : Models.Cube.RowWise.ofRealL _ (w p • u p) =
      ((w p : ℂ)) • Models.Cube.RowWise.ofRealL _ (u p) := by
    rw [_root_.map_smul]
    exact RCLike.real_smul_eq_coe_smul (K := ℂ) _ _
  rw [this, _root_.map_smul, Models.Cube.RowWise.mFourierCoeff_smul]

/-- **The parity extension commutes with the weights**: `J ∘ φ_Q = φ_𝕋 ∘ J`. -/
theorem J_phiQ (hd : ∀ i, 0 < d i) (i : Fin 3) (u : WQ i) :
    J i (phiQ hd i u) = phiT hd i (J i u) := by
  fin_cases i
  · refine (congrArg (J 0) (?_ : phiQ hd 0 u = u)).trans ?_
    · refine PiLp.ext fun a => ?_
      exact one_smul ℝ _
    · refine Lp.ext_count fun n => ?_
      rw [coeFn_phiT]; rfl
  · exact JR_scaleF _ _ _ u
  · exact JR_scaleF _ _ _ u

end Weights

/-! ### The box and its complex -/

section BoxComplex

open Models.Cube.Geometry (Q)
open Models.Cube.RowWise (J WQ cubeComplex)
open Models.BoundedDomain (gradCurl)
open Domain (L2F)

/-- **The open box** `∏ (aᵢ, aᵢ + ℓᵢ)`. -/
def openBox (a ℓ : R3) : Set R3 := univ.pi fun i => Ioo (a i) (a i + ℓ i)

theorem isOpen_openBox (a ℓ : R3) : IsOpen (openBox a ℓ) :=
  isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo

theorem isBounded_openBox (a ℓ : R3) : Bornology.IsBounded (openBox a ℓ) :=
  (Metric.isBounded_Icc a fun i => a i + ℓ i).subset fun _ hy =>
    ⟨fun i => (hy i (mem_univ i)).1.le, fun i => (hy i (mem_univ i)).2.le⟩

theorem nonempty_openBox (a : R3) {ℓ : R3} (hℓ : ∀ i, 0 < ℓ i) : (openBox a ℓ).Nonempty :=
  ⟨fun i => a i + ℓ i / 2, fun i _ => ⟨by linarith [hℓ i], by linarith [hℓ i]⟩⟩

variable {a ℓ : R3}

/-- The scalings `dᵢ = 1/(2ℓᵢ)` of the map `T x = d * (x - a)` of the box onto `Q`. -/
def dB (ℓ : R3) : R3 := fun i => (2 * ℓ i)⁻¹

theorem dB_pos (hℓ : ∀ i, 0 < ℓ i) (i : Fin 3) : 0 < dB ℓ i := inv_pos.2 (by linarith [hℓ i])

theorem dB_ne_zero (hℓ : ∀ i, 0 < ℓ i) (i : Fin 3) : dB ℓ i ≠ 0 := (dB_pos hℓ i).ne'

/-- The shift `-d * a` of `T x = d * x - d * a`. -/
def bB (a ℓ : R3) : R3 := -(dB ℓ * a)

theorem preimage_Q (hℓ : ∀ i, 0 < ℓ i) :
    Domain.diagAff (dB ℓ) (bB a ℓ) ⁻¹' Q (Fin 3) = openBox a ℓ := by
  ext x
  simp only [mem_preimage, Models.Cube.Geometry.mem_Q, openBox, mem_pi, mem_univ, true_implies,
    mem_Ioo, Domain.diagAff_apply, bB, dB, Pi.neg_apply, Pi.mul_apply]
  refine forall_congr' fun i => ?_
  have h2 : 0 < 2 * ℓ i := by linarith [hℓ i]
  have e : (2 * ℓ i)⁻¹ * x i + -((2 * ℓ i)⁻¹ * a i) = (x i - a i) / (2 * ℓ i) := by ring
  rw [e, div_pos_iff_of_pos_right h2, div_lt_iff₀ h2]
  constructor <;> rintro ⟨h, h'⟩ <;> constructor <;> linarith

/-- The spaces of the complex on the box. -/
abbrev WB (a ℓ : R3) : Fin 3 → Type :=
  W3 (L2F ℝ (openBox a ℓ) (Fin 3)) (L2F ℝ (openBox a ℓ) Ix) (L2F ℝ (openBox a ℓ) Ix)

/-- **The thesis' complex on the box** `∏ (aᵢ, aᵢ + ℓᵢ)`: `H̊¹ → H̊(curl) → L²`, the minimal
realizations of `grad` and `curl`. -/
abbrev complexBox (a ℓ : R3) : HilbertComplex ℝ ComplexShape.fin3 (WB a ℓ) :=
  (gradCurl ℝ (isOpen_openBox a ℓ)).toHilbertComplex

/-- The pull-back `u ↦ u ∘ T` from `Q` to the box, slot by slot. -/
def pullB (hℓ : ∀ i, 0 < ℓ i) : ∀ i, WQ i ≃L[ℝ] WB a ℓ i
  | 0 => Domain.pullDiagF (dB_ne_zero hℓ) (bB a ℓ) Models.Cube.Geometry.measurableSet_Q
      (preimage_Q hℓ) (Fin 3)
  | 1 => Domain.pullDiagF (dB_ne_zero hℓ) (bB a ℓ) Models.Cube.Geometry.measurableSet_Q
      (preimage_Q hℓ) Ix
  | 2 => Domain.pullDiagF (dB_ne_zero hℓ) (bB a ℓ) Models.Cube.Geometry.measurableSet_Q
      (preimage_Q hℓ) Ix

theorem inner_pullB (hℓ : ∀ i, 0 < ℓ i) (i : Fin 3) (x y : WQ i) :
    ⟪pullB (a := a) hℓ i x, pullB hℓ i y⟫_ℝ =
      (((Domain.jacD (dB ℓ))⁻¹ : ℝ) : ℝ) * ⟪x, y⟫_ℝ := by
  fin_cases i
  · exact Domain.inner_pullDiagF _ _ _ _ x y
  · exact Domain.inner_pullDiagF _ _ _ _ x y
  · exact Domain.inner_pullDiagF _ _ _ _ x y

/-- **The box complex is the cube complex reweighted by the column scalings and pulled back**:
`H̊¹(B) → H̊(curl, B) → L²(B)` is the transport of `H̊¹(Q) → H̊(curl, Q) → L²(Q)` along
`φ_Q` (`grad_d = (grad ·) D`, `curl_d (· D) = det D · (curl ·) D⁻¹`) and then along the
pull-back (`Feec.Domain.ConstCoeffOp.minimal_pullDiag`). -/
theorem complexBox_eq_transport (hℓ : ∀ i, 0 < ℓ i) :
    complexBox a ℓ = (cubeComplex.transport (phiQ (dB_pos hℓ)) (fun _ _ => 1)
      fun _ _ => one_ne_zero).transport (pullB hℓ) (fun _ _ => 1) fun _ _ => one_ne_zero := by
  refine HilbertComplex.ext_d (funext fun i => funext fun j => ?_)
  by_cases hij : ComplexShape.fin3.Rel i j
  · fin_cases i <;> fin_cases j <;> simp [ComplexShape.window] at hij
    · have h1 := Domain.ConstCoeffOp.minimal_pullDiag (A := (Domain.gradOp 3 3 :
          Domain.ConstCoeffOp R3 ℝ (Fin 3) Ix)) (dB_ne_zero hℓ) (bB a ℓ)
        Models.Cube.Geometry.measurableSet_Q (preimage_Q hℓ) Models.Cube.Geometry.isOpen_Q
      have h2 := Domain.ConstCoeffOp.minimal_eq_conj_scaleF
        (A := (Domain.gradOp 3 3 : Domain.ConstCoeffOp R3 ℝ (Fin 3) Ix))
        (B := Domain.ConstCoeffOp.diagScale (dB ℓ) (Domain.gradOp 3 3))
        (w := fun _ => (1 : ℝ)) (w' := w1 (dB ℓ)) (fun _ => one_ne_zero)
        (w1_ne_zero (dB_pos hℓ)) (fun ψ _ => Domain.gradOp_diagScale_smul (dB ℓ) ψ)
        Models.Cube.Geometry.isOpen_Q
      rw [h2] at h1
      exact h1
    · have h1 := Domain.ConstCoeffOp.minimal_pullDiag (A := (Domain.curlOp 3 :
          Domain.ConstCoeffOp R3 ℝ Ix Ix)) (dB_ne_zero hℓ) (bB a ℓ)
        Models.Cube.Geometry.measurableSet_Q (preimage_Q hℓ) Models.Cube.Geometry.isOpen_Q
      have h2 := Domain.ConstCoeffOp.minimal_eq_conj_scaleF
        (A := (Domain.curlOp 3 : Domain.ConstCoeffOp R3 ℝ Ix Ix))
        (B := Domain.ConstCoeffOp.diagScale (dB ℓ) (Domain.curlOp 3))
        (w := w1 (dB ℓ)) (w' := w2 (dB ℓ)) (w1_ne_zero (dB_pos hℓ))
        (w2_ne_zero (dB_pos hℓ))
        (fun ψ hψ => Domain.curlOp_diagScale_smul (dB ℓ)
          (fun p => (hψ p).differentiable (by simp)))
        Models.Cube.Geometry.isOpen_Q
      rw [h2] at h1
      exact h1
  · rw [(complexBox a ℓ).shape i j hij, HilbertComplex.transport_d,
      HilbertComplex.transportD_eq_zero ((cubeComplex.transport (phiQ (dB_pos hℓ))
        (fun _ _ => 1) fun _ _ => one_ne_zero).shape i j hij)]

/-- The parity extension of fields on the box: `J ∘ P⁻¹`. -/
abbrev JB (hℓ : ∀ i, 0 < ℓ i) (i : Fin 3) : WB a ℓ i →L[ℝ] Space i :=
  J i ∘L ((pullB (a := a) hℓ i).symm : WB a ℓ i →L[ℝ] WQ i)

theorem JB_apply (hℓ : ∀ i, 0 < ℓ i) (i : Fin 3) (x : WB a ℓ i) :
    JB hℓ i x = J i ((pullB hℓ i).symm x) := rfl

/-- `JB` scales inner products by `8 |∏ dᵢ|`. -/
theorem inner_JB (hℓ : ∀ i, 0 < ℓ i) (i : Fin 3) (x y : WB a ℓ i) :
    ⟪JB hℓ i x, JB hℓ i y⟫_ℝ = ((8 * Domain.jacD (dB ℓ) : ℝ) : ℝ) * ⟪x, y⟫_ℝ := by
  rw [JB_apply, JB_apply, Models.Cube.RowWise.inner_J]
  have h := inner_pullB (a := a) hℓ i ((pullB hℓ i).symm x) ((pullB hℓ i).symm y)
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply] at h
  have hj := Domain.jacD_pos (dB_ne_zero hℓ)
  have : ⟪(pullB hℓ i).symm x, (pullB hℓ i).symm y⟫_ℝ = Domain.jacD (dB ℓ) * ⟪x, y⟫_ℝ := by
    rw [h]; field_simp
  change (8 : ℝ) * _ = _
  rw [this]; ring

theorem range_JB (hℓ : ∀ i, 0 < ℓ i) (i : Fin 3) :
    LinearMap.range (JB (a := a) hℓ i : WB a ℓ i →ₗ[ℝ] Space i) =
      LinearMap.range (J i : WQ i →ₗ[ℝ] Space i) := by
  change LinearMap.range ((J i : WQ i →ₗ[ℝ] Space i).comp
    ((pullB (a := a) hℓ i).symm : WB a ℓ i →ₗ[ℝ] WQ i)) = _
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.2 (pullB (a := a) hℓ i).symm.surjective)

instance instHasOrthogonalProjectionRangeJB (hℓ : ∀ i, 0 < ℓ i) (i : Fin 3) :
    (LinearMap.range (JB (a := a) hℓ i : WB a ℓ i →ₗ[ℝ] Space i)).HasOrthogonalProjection := by
  rw [range_JB]; infer_instance

theorem reducingSubcomplex_rangeJB (hℓ : ∀ i, 0 < ℓ i) :
    (torusD (dB_pos hℓ)).ReducingSubcomplex fun i =>
      LinearMap.range (JB (a := a) hℓ i : WB a ℓ i →ₗ[ℝ] Space i) := by
  have h := reducingSubcomplex_range (dB_pos hℓ)
  refine ⟨fun i j => ?_⟩
  convert h.reduces i j using 1 <;> exact range_JB hℓ _

theorem scaleJB_pos (hℓ : ∀ i, 0 < ℓ i) : (0 : ℝ) < 8 * Domain.jacD (dB ℓ) :=
  mul_pos (by norm_num) (Domain.jacD_pos (dB_ne_zero hℓ))

/-- **The box complex is the compression of the anisotropic torus complex** along the parity
extension of the pulled-back fields. -/
theorem complexBox_eq_compress (hℓ : ∀ i, 0 < ℓ i) :
    complexBox a ℓ = (torusD (dB_pos hℓ)).compress (JB hℓ) (scaleJB_pos hℓ) (inner_JB hℓ)
      (reducingSubcomplex_rangeJB hℓ) := by
  rw [complexBox_eq_transport hℓ]
  have h := HilbertComplex.transport_transport_compress (by norm_num : (0 : ℝ) < 8)
    Feec.Models.Cube.RowWise.inner_J Models.Cube.RowWise.reducingSubcomplex_range
    (phiQ (dB_pos hℓ)) (phiT (dB_pos hℓ)) (J_phiQ (dB_pos hℓ)) (pullB (a := a) hℓ)
    (scaleJB_pos hℓ) (inner_JB hℓ) (reducingSubcomplex_rangeJB hℓ)
  rw [← Models.Cube.RowWise.cubeComplex_eq_compress] at h
  exact h

end BoxComplex

end Feec.Models.Box
