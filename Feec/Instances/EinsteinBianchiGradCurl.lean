module

public import Feec.Instances.EuclideanBand
public import Feec.Physics.EinsteinBianchi.Constraints
public import Feec.Models.Euclidean.SymCurl
public import Feec.Models.Torus.SymCurl
public import Feec.Models.Cube.MirrorDirichlet
public import Feec.Models.Box.Mirror
public import Feec.Fourier.TorusSpectral

/-!
# The Einstein–Bianchi system with strong symmetry as instances of the FEEC theorem

The linearized Einstein–Bianchi system ([QuennevilleBelair2015], Prop 3.4) is the Hodge wave
equation of the grad–curl complex (4.14) and of the strong-symmetry complex (4.16) with the TSD
constraint; this file applies the FEEC theorem to it on `𝕋³`, on mirror cubes and boxes, and on
`ℝ³`.

## Main results

* `GradCurl.torus_verdict`, `SymCurl.torus_verdict`: the Fourier spectral method on `𝕋³`.
* `GradCurl.planeWave_verdict`: the TT gravitational plane waves on `𝕋³`.
* `GradCurl.euclidean_verdict`, `SymCurl.euclidean_verdict`: the frequency truncation on `ℝ³`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]
* [R. M. Wald, *General Relativity*][Wald1984]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace FourierTransform SchwartzMap
open Set Filter MeasureTheory Metric

@[expose] public noncomputable section

namespace Feec.Instances.EinsteinBianchi

open Feec.HilbertComplex _root_.Feec.HodgeWave Feec.Fourier Feec.Instances.EuclideanBand

/-! ### The grad–curl complex (4.14) -/

namespace GradCurl

open Feec.Fourier.GradCurl Feec.ShortHilbertComplex

section Torus

open Feec.Models.Torus.GradCurl

/-- The Fourier spectral discretization of the EB system (4.14) on `𝕋³`, with the TSD constraint. -/
def torusFEEC : ConstrainedFEEC complex ℕ :=
  (bandSpectralFamily (Fourier.Torus.symbolComplex gradCurl)).toFEEC (totalSub constraint)
    isClosed_totalSub

/-- **The FEEC verdict for the EB system (4.14) on `𝕋³`**, with the TSD clauses below. -/
structure TorusVerdict : Prop extends torusFEEC.Verdict where
  isReducing : complex.wave.IsReducing torusFEEC.K
  /-- TSD data stay TSD along strong solutions with TSD forcing -/
  tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution complex.wave (Icc a b) F U) (h0 : U a ∈ torusFEEC.K)
    (hF : ∀ t ∈ Icc a b, F t ∈ torusFEEC.K) : ∀ t ∈ Icc a b, U t ∈ torusFEEC.K
  /-- the TSD residual of the discrete solutions tends to `0` uniformly on `[0, T]` -/
  tsd_residual_tendsto (x : complex.wave.domain) (hxK : (x : PiLp 2 Space) ∈ torusFEEC.K) (T : ℝ) :
    TendstoUniformlyOn
      (fun N t => infDist (complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex x) t))
        (torusFEEC.K : Set (PiLp 2 Space))) (fun _ => 0) torusFEEC.l (Icc 0 T)

/-- **The FEEC theorem for the EB system (4.14) on `𝕋³`**: `TorusVerdict`. [QuennevilleBelair2015],
Thm 4.14, Prop 4.17 -/
theorem torus_verdict : TorusVerdict :=
  have V := constrainedFEEC torusFEEC
  { V with
    isReducing := reducingSubcomplex.isReducing_wave
    tsd_propagates := _root_.Feec.EinsteinBianchi.torus_tsd_propagates
    tsd_residual_tendsto := V.residual_tendsto reducingSubcomplex.isReducing_wave }

/-! #### TT gravitational plane waves -/

open _root_.Feec.EinsteinBianchi (ampE ampB waveE waveB)

/-- The frequency `(0, 0, m)` of a plane wave travelling along `x₃`. -/
def waveFreq (m : ℤ) : Fin 3 → ℤ := ![0, 0, m]

/-- The fibre `(0, E₀, B₀)` of the TT plane wave: `E₀ = ampE A₊ Aₓ`, `B₀ = ampB A₊ Aₓ`. -/
def planeWaveFibre (Ap Ax : ℝ) : PiLp 2 (W3 Vec Mat Mat) :=
  inj₁ (𝕜 := ℂ) Vec Mat Mat (ofRealMat (ampE Ap Ax)) +
    inj₂ (𝕜 := ℂ) Vec Mat Mat (ofRealMat (ampB Ap Ax))

@[simp] theorem planeWaveFibre_zero (Ap Ax : ℝ) : planeWaveFibre Ap Ax 0 = 0 :=
  add_zero (0 : Vec)

@[simp] theorem planeWaveFibre_one (Ap Ax : ℝ) : planeWaveFibre Ap Ax 1 = ofRealMat (ampE Ap Ax) :=
  add_zero (ofRealMat (ampE Ap Ax))

@[simp] theorem planeWaveFibre_two (Ap Ax : ℝ) : planeWaveFibre Ap Ax 2 = ofRealMat (ampB Ap Ax) :=
  zero_add (ofRealMat (ampB Ap Ax))

/-- The field `x ↦ e^{2πi m x₃} A` on `𝕋³`, on the physical side. -/
def torusWave (m : ℤ) (A : Matrix (Fin 3) (Fin 3) ℝ) :=
  WithLp.toLp 2 fun q : Fin 3 × Fin 3 => (A q.1 q.2 : ℂ) • UnitAddTorus.mFourierLp 2 (waveFreq m)

/-- The TT gravitational plane wave on `𝕋³`: the single mode `δ_{(0,0,m)} (0, E₀, B₀)`. -/
def planeWave (m : ℤ) (Ap Ax : ℝ) : PiLp 2 Space :=
  SymbolComplex.modeField (waveFreq m) (planeWaveFibre Ap Ax)

theorem curl_ampB (m : ℤ) (Ap Ax : ℝ) :
    curl (Fourier.Torus.freq (waveFreq m)) (ofRealMat (ampB Ap Ax)) =
      ((2 * Real.pi * m : ℝ) * Complex.I) • ofRealMat (ampE Ap Ax) := by
  ext ⟨a, b⟩
  rw [curl_apply]
  simp only [Fin.sum_univ_three, Fourier.Torus.freq_apply, waveFreq, ofRealMat,
    PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  fin_cases a <;> fin_cases b <;> simp [leviCivita3_apply, ampB, ampE] <;> ring

theorem curl_ampE (m : ℤ) (Ap Ax : ℝ) :
    curl (Fourier.Torus.freq (waveFreq m)) (ofRealMat (ampE Ap Ax)) =
      -(((2 * Real.pi * m : ℝ) * Complex.I) • ofRealMat (ampB Ap Ax)) := by
  ext ⟨a, b⟩
  rw [curl_apply]
  simp only [Fin.sum_univ_three, Fourier.Torus.freq_apply, waveFreq, ofRealMat, PiLp.neg_apply,
    PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  fin_cases a <;> fin_cases b <;> simp [leviCivita3_apply, ampB, ampE] <;> ring

theorem div_ampE (m : ℤ) (Ap Ax : ℝ) :
    div (Fourier.Torus.freq (waveFreq m)) (ofRealMat (ampE Ap Ax)) = 0 := by
  ext a
  rw [div_apply]
  simp only [Fin.sum_univ_three, Fourier.Torus.freq_apply, waveFreq, ofRealMat,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  fin_cases a <;> simp [ampE]

theorem waveSym_planeWaveFibre (m : ℤ) (Ap Ax : ℝ) :
    (Fourier.Torus.symbolComplex gradCurl).waveSym (waveFreq m) (planeWaveFibre Ap Ax) =
      (-((2 * Real.pi * m : ℝ) * Complex.I)) • planeWaveFibre Ap Ax := by
  set c : ℂ := (2 * Real.pi * m : ℝ) * Complex.I
  -- the fibres typed as `W3 Vec Mat Mat i`, for `simp` to match the components of the symbol
  set E₀ : W3 Vec Mat Mat 1 := ofRealMat (ampE Ap Ax)
  set B₀ : W3 Vec Mat Mat 2 := ofRealMat (ampB Ap Ax)
  have v0 : planeWaveFibre Ap Ax 0 = 0 := planeWaveFibre_zero Ap Ax
  have v1 : planeWaveFibre Ap Ax 1 = E₀ := planeWaveFibre_one Ap Ax
  have v2 : planeWaveFibre Ap Ax 2 = B₀ := planeWaveFibre_two Ap Ax
  have dE :
      ContinuousLinearMap.adjoint (gradCurl.m 0 1 (Fourier.Torus.freq (waveFreq m))) E₀ = 0 := by
    change ContinuousLinearMap.adjoint (grad (Fourier.Torus.freq (waveFreq m)))
      (ofRealMat (ampE Ap Ax)) = 0
    rw [adjoint_grad]; exact div_ampE m Ap Ax
  have cB : ContinuousLinearMap.adjoint (gradCurl.m 1 2 (Fourier.Torus.freq (waveFreq m))) B₀ =
      c • E₀ := by
    change ContinuousLinearMap.adjoint (curl (Fourier.Torus.freq (waveFreq m)))
      (ofRealMat (ampB Ap Ax)) = _
    rw [adjoint_curl]; exact curl_ampB m Ap Ax
  have cE : gradCurl.m 1 2 (Fourier.Torus.freq (waveFreq m)) E₀ = -(c • B₀) := curl_ampE m Ap Ax
  have z : ∀ {i j : Fin 3}, ¬ ComplexShape.fin3.Rel i j → ∀ ξ, gradCurl.m i j ξ = 0 :=
    fun h => gradCurl_m_eq_zero h
  have h0 : (Fourier.Torus.symbolComplex gradCurl).waveSym (waveFreq m) (planeWaveFibre Ap Ax) 0 =
      ((-c) • planeWaveFibre Ap Ax) 0 := by
    simp only [SymbolComplex.waveSym_apply, Fin.sum_univ_three, Fourier.Torus.symbolComplex_m,
      z (i := 0) (j := 0) (by simp), z (i := 1) (j := 0) (by simp), z (i := 2) (j := 0) (by simp),
      z (i := 0) (j := 2) (by simp), PiLp.smul_apply, v0, v1, v2, dE]
    simp [-gradCurl_m01, -gradCurl_m12]
  have h1 : (Fourier.Torus.symbolComplex gradCurl).waveSym (waveFreq m) (planeWaveFibre Ap Ax) 1 =
      ((-c) • planeWaveFibre Ap Ax) 1 := by
    simp only [SymbolComplex.waveSym_apply, Fin.sum_univ_three, Fourier.Torus.symbolComplex_m,
      z (i := 1) (j := 1) (by simp), z (i := 2) (j := 1) (by simp), z (i := 1) (j := 0) (by simp),
      PiLp.smul_apply, v0, v1, v2, cB]
    simp [-gradCurl_m01, -gradCurl_m12]
  have h2 : (Fourier.Torus.symbolComplex gradCurl).waveSym (waveFreq m) (planeWaveFibre Ap Ax) 2 =
      ((-c) • planeWaveFibre Ap Ax) 2 := by
    simp only [SymbolComplex.waveSym_apply, Fin.sum_univ_three, Fourier.Torus.symbolComplex_m,
      z (i := 0) (j := 2) (by simp), z (i := 2) (j := 2) (by simp), z (i := 2) (j := 0) (by simp),
      z (i := 2) (j := 1) (by simp), PiLp.smul_apply, v0, v1, v2, cE]
    simp [-gradCurl_m01, -gradCurl_m12]
  ext j
  fin_cases j
  exacts [h0, h1, h2]

theorem ofRealMat_mem_tsd {m : ℤ} {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.transpose = A)
    (htr : A.trace = 0) (h2 : ∀ a, A a 2 = 0) :
    ofRealMat A ∈ tsd (Fourier.Torus.freq (waveFreq m)) := by
  refine mem_tsd.2 ⟨?_, ?_, ?_⟩
  · ext a b
    simpa [ofRealMat] using congrArg (fun M => (M a b : ℂ)) hA
  · simpa [Matrix.trace, ofRealMat, Fin.sum_univ_three] using congrArg (fun r : ℝ => (r : ℂ)) htr
  · ext a
    simp [Matrix.mulVec, dotProduct, ofRealMat, cfreq, Fin.sum_univ_three, waveFreq, h2 a]

theorem planeWave_mem_constraint (m : ℤ) (Ap Ax : ℝ) :
    planeWave m Ap Ax ∈ totalSub constraint := by
  have key : ∀ i, planeWaveFibre Ap Ax i ∈ tsdK i (Fourier.Torus.freq (waveFreq m)) := by
    intro i
    fin_cases i
    · exact (Submodule.mem_bot ℂ).2 (planeWaveFibre_zero Ap Ax)
    · exact (planeWaveFibre_one Ap Ax).symm ▸ ofRealMat_mem_tsd
        (by ext a b; fin_cases a <;> fin_cases b <;> simp [ampE])
        (by simp [ampE, Matrix.trace, Fin.sum_univ_three]) (fun a => by fin_cases a <;> simp [ampE])
    · exact (planeWaveFibre_two Ap Ax).symm ▸ ofRealMat_mem_tsd
        (by ext a b; fin_cases a <;> fin_cases b <;> simp [ampB])
        (by simp [ampB, Matrix.trace, Fin.sum_univ_three]) (fun a => by fin_cases a <;> simp [ampB])
  intro i
  refine Operator.mem_fibreSub.2 (Measure.ae_count_iff.2 fun n => ?_)
  change ((planeWave m Ap Ax i : Lp _ 2 _) : (Fin 3 → ℤ) → _) n ∈ tsdK i (Fourier.Torus.freq n)
  rw [planeWave, SymbolComplex.coe_modeField, Pi.single_apply]
  split_ifs with hn
  · subst hn; exact key i
  · exact Submodule.zero_mem _

theorem planeWave_mem_band (m : ℤ) (Ap Ax : ℝ) {N : ℕ} (hN : |m| ≤ N) :
    planeWave m Ap Ax ∈
      totalSub ((bandSpectralFamily (Fourier.Torus.symbolComplex gradCurl)).B N) := fun i =>
  (Fourier.mem_band_iff (S := Fourier.Torus.symbolComplex gradCurl)).2
    (Measure.ae_count_iff.2 fun n hn => by
      rw [planeWave, SymbolComplex.coe_modeField, Pi.single_eq_of_ne]
      rintro rfl
      exact hn fun j => by fin_cases j <;> simp [waveFreq, hN])

theorem planeWave_eq_fieldFourier (m : ℤ) (Ap Ax : ℝ) :
    @Eq (Lp Mat 2 Measure.count) (planeWave m Ap Ax 1)
        (Fourier.Torus.fieldFourier (Fin 3) (Fin 3 × Fin 3) (torusWave m (ampE Ap Ax))) ∧
      @Eq (Lp Mat 2 Measure.count) (planeWave m Ap Ax 2)
        (Fourier.Torus.fieldFourier (Fin 3) (Fin 3 × Fin 3) (torusWave m (ampB Ap Ax))) := by
  refine ⟨Lp.ext_count fun a => ?_, Lp.ext_count fun a => ?_⟩
  · have h := congrFun (SymbolComplex.coe_modeField (waveFreq m) (planeWaveFibre Ap Ax) 1) a
    rw [planeWaveFibre_one] at h
    exact h.trans (congrFun (Fourier.Torus.coe_fieldFourier_mFourierLp (P := Fin 3 × Fin 3)
      (waveFreq m) (ofRealMat (ampE Ap Ax))) a).symm
  · have h := congrFun (SymbolComplex.coe_modeField (waveFreq m) (planeWaveFibre Ap Ax) 2) a
    rw [planeWaveFibre_two] at h
    exact h.trans (congrFun (Fourier.Torus.coe_fieldFourier_mFourierLp (P := Fin 3 × Fin 3)
      (waveFreq m) (ofRealMat (ampB Ap Ax))) a).symm

/-- **The TT gravitational plane waves through the FEEC theorem on `𝕋³`**, with the clauses below.
[QuennevilleBelair2015], §3.5, §2.8; [Wald1984], §4.4 -/
structure PlaneWaveVerdict (m : ℤ) (Ap Ax : ℝ) : Prop where
  /-- the Weyl field of the TT metric perturbation solves the linearized EB system -/
  physical {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) (p : Fin 4 → ℝ) :
    LinearizedGravity.Rjet (LinearizedGravity.jet2 (fun y => Matrix.of fun a b =>
        LinearizedGravity.ttAmp Ap Ax a b *
          f (LinearizedGravity.phaseL (LinearizedGravity.kTT (2 * Real.pi * m)) y)) p) =
      DoubleForm.ofBlocks (waveE (2 * Real.pi * m) Ap Ax f p) (waveB (2 * Real.pi * m) Ap Ax f p)
        (waveB (2 * Real.pi * m) Ap Ax f p) (-waveE (2 * Real.pi * m) Ap Ax f p) ∧
    _root_.Feec.EinsteinBianchi.EBJet
      (_root_.Feec.EinsteinBianchi.jet4 (waveE (2 * Real.pi * m) Ap Ax f) p)
      (_root_.Feec.EinsteinBianchi.jet4 (waveB (2 * Real.pi * m) Ap Ax f) p)
  /-- the physical fields are the profile `(κ²/2) f''(κ(x³ - t))` times `E₀`, `B₀` -/
  amplitude (f : ℝ → ℝ) (p : Fin 4 → ℝ) :
    ofRealMat (waveE (2 * Real.pi * m) Ap Ax f p) =
        (((2 * Real.pi * m) ^ 2 / 2 * deriv (deriv f)
          (LinearizedGravity.phaseL (LinearizedGravity.kTT (2 * Real.pi * m)) p) : ℝ) : ℂ) •
          ofRealMat (ampE Ap Ax) ∧
      ofRealMat (waveB (2 * Real.pi * m) Ap Ax f p) =
        (((2 * Real.pi * m) ^ 2 / 2 * deriv (deriv f)
          (LinearizedGravity.phaseL (LinearizedGravity.kTT (2 * Real.pi * m)) p) : ℝ) : ℂ) •
          ofRealMat (ampB Ap Ax)
  /-- the mode is the Fourier image of `e^{2πi m x₃} (0, E₀, B₀)` -/
  fourier :
    @Eq (Lp Mat 2 Measure.count) (planeWave m Ap Ax 1)
        (Fourier.Torus.fieldFourier (Fin 3) (Fin 3 × Fin 3) (torusWave m (ampE Ap Ax))) ∧
      @Eq (Lp Mat 2 Measure.count) (planeWave m Ap Ax 2)
        (Fourier.Torus.fieldFourier (Fin 3) (Fin 3 × Fin 3) (torusWave m (ampB Ap Ax)))
  mem_constraint : planeWave m Ap Ax ∈ torusFEEC.K
  mem_domain : planeWave m Ap Ax ∈ complex.wave.domain
  /-- the mode is an eigenvector of `L`, `L X = -2πim X` -/
  wave_eq : complex.wave ⟨planeWave m Ap Ax, mem_domain⟩ =
    (-((2 * Real.pi * m : ℝ) * Complex.I)) • planeWave m Ap Ax
  /-- its orbit is the plane wave `e^{-2πimt} X` -/
  waveGroup_eq (t : ℝ) : complex.waveGroup.S t (planeWave m Ap Ax) =
    NormedSpace.exp (t • (-((2 * Real.pi * m : ℝ) * Complex.I))) • planeWave m Ap Ax
  /-- the discrete solutions of `torusFEEC` from it are exact once `|m| ≤ N` -/
  discrete_eq {N : ℕ} (hN : |m| ≤ N) (t : ℝ) :
    complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex ⟨_, mem_domain⟩) t) =
      complex.waveGroup.S t (planeWave m Ap Ax)

/-- **The TT gravitational plane waves through the FEEC theorem on `𝕋³`**: `PlaneWaveVerdict`.
[QuennevilleBelair2015], §3.5, Prop 4.17, Ch. 6 -/
theorem planeWave_verdict (m : ℤ) (Ap Ax : ℝ) : PlaneWaveVerdict m Ap Ax :=
  have hL : complex.wave ⟨planeWave m Ap Ax, SymbolComplex.modeField_mem_wave_domain _ _ _⟩ =
      (-((2 * Real.pi * m : ℝ) * Complex.I)) • planeWave m Ap Ax :=
    (SymbolComplex.wave_modeField _ _ _).trans (by
      rw [waveSym_planeWaveFibre, SymbolComplex.modeField_smul]; rfl)
  { physical := fun hf p => ⟨(_root_.Feec.EinsteinBianchi.planeWave_EB hf _ Ap Ax p).1,
      (_root_.Feec.EinsteinBianchi.planeWave_EB hf _ Ap Ax p).2.2.2⟩
    amplitude := fun f p =>
      ⟨by ext q; simp [waveE, ofRealMat], by ext q; simp [waveB, ofRealMat]⟩
    fourier := planeWave_eq_fieldFourier m Ap Ax
    mem_constraint := planeWave_mem_constraint m Ap Ax
    mem_domain := SymbolComplex.modeField_mem_wave_domain _ _ _
    wave_eq := hL
    waveGroup_eq := SymbolComplex.waveGroup_modeField _ _ (waveSym_planeWaveFibre m Ap Ax)
    discrete_eq := fun hN t =>
      (torusFEEC.graphFst_discrete_of_wave_eq_smul (x := ⟨_, _⟩) _ (planeWave_mem_band m Ap Ax hN)
        hL t).trans
        (SymbolComplex.waveGroup_modeField _ _ (waveSym_planeWaveFibre m Ap Ax) t).symm }

end Torus

section Mirror

open Feec.Models.Cube.Mirror
open Feec.Models.BoundedDomain (R3)

/-- The cosine–sine spectral family of the grad–curl complex on the mirror cube `Q`. -/
def mirrorFamilyQ : SpectralFamily complexQ :=
  mirrorSpectralFamily symmetries (fun _ _ => rfl) embeddingQ range_J

/-- The spectral discretization of the EB system (4.14) on the mirror cube `Q`. -/
def mirrorFEEC : ConstrainedFEEC complexQ ℕ :=
  mirrorFamilyQ.toFEEC (totalSub tsdQ) isClosed_totalSub

/-- **The FEEC verdict for the EB system (4.14) on the mirror cube `Q`**, with the clauses below. -/
structure MirrorVerdict : Prop extends mirrorFEEC.Verdict where
  /-- the mirror complex lies between the Dirichlet and the natural realizations -/
  between : (Models.BoundedDomain.gradCurl ℂ Models.Cube.Geometry.isOpen_Q).d₀ ≤ complexQ.d 0 1 ∧
    (Models.BoundedDomain.gradCurl ℂ Models.Cube.Geometry.isOpen_Q).d₁ ≤ complexQ.d 1 2 ∧
    complexQ.d 0 1 ≤ (Models.BoundedDomain.gradCurlMax ℂ Models.Cube.Geometry.isOpen_Q).d₀ ∧
    complexQ.d 1 2 ≤ (Models.BoundedDomain.gradCurlMax ℂ Models.Cube.Geometry.isOpen_Q).d₁
  isReducing : complexQ.wave.IsReducing mirrorFEEC.K
  /-- TSD data stay TSD along strong solutions with TSD forcing -/
  tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 SpaceQ}
    (hU : Evolution.IsStrongSolution complexQ.wave (Icc a b) F U) (h0 : U a ∈ mirrorFEEC.K)
    (hF : ∀ t ∈ Icc a b, F t ∈ mirrorFEEC.K) : ∀ t ∈ Icc a b, U t ∈ mirrorFEEC.K
  /-- the TSD residual of the discrete solutions tends to `0` uniformly on `[0, T]` -/
  tsd_residual_tendsto (x : complexQ.wave.domain) (hxK : (x : PiLp 2 SpaceQ) ∈ mirrorFEEC.K)
    (T : ℝ) :
    TendstoUniformlyOn
      (fun N t => infDist (complexQ.totalD.graphFst (mirrorFEEC.discrete N (waveLift complexQ x) t))
        (mirrorFEEC.K : Set (PiLp 2 SpaceQ))) (fun _ => 0) mirrorFEEC.l (Icc 0 T)

/-- **The FEEC theorem for the EB system (4.14) on `Q` with mirror boundary conditions**:
`MirrorVerdict`. [QuennevilleBelair2015], Thm 4.14, Prop 4.17 (adapted) -/
theorem mirror_verdict : MirrorVerdict :=
  have V := constrainedFEEC mirrorFEEC
  { V with
    between := ⟨minimal_le_d₀, minimal_le_d₁, d₀_le_maximal, d₁_le_maximal⟩
    isReducing := reducingSubcomplexQ.isReducing_wave
    tsd_propagates := propagatesQ
    tsd_residual_tendsto := V.residual_tendsto reducingSubcomplexQ.isReducing_wave }

variable (b : R3) {s : ℝ} (hs : 0 < s)

/-- The spectral discretization of the EB system (4.14) on an open cube with mirror conditions. -/
def mirrorCubeFEEC : ConstrainedFEEC (complexCube b s hs) ℕ :=
  (mirrorFamilyQ.comap (embeddingCube hs) fun N i x =>
      ⟨eCube b s hs i ((mirrorFamilyQ.B N i).starProjection ((eCube b s hs i).symm x)),
        (eCube b s hs i).symm_apply_apply _⟩).toFEEC (totalSub (tsdCube b s hs)) isClosed_totalSub

/-- **The FEEC verdict for the EB system (4.14) on an open mirror cube**, with the clauses below. -/
structure MirrorCubeVerdict : Prop extends (mirrorCubeFEEC b hs).Verdict where
  isReducing : (complexCube b s hs).wave.IsReducing (mirrorCubeFEEC b hs).K
  /-- TSD data stay TSD along strong solutions with TSD forcing -/
  tsd_propagates {a c : ℝ} {F U : ℝ → PiLp 2 (SpaceCube b s)}
    (hU : Evolution.IsStrongSolution (complexCube b s hs).wave (Icc a c) F U)
    (h0 : U a ∈ (mirrorCubeFEEC b hs).K) (hF : ∀ t ∈ Icc a c, F t ∈ (mirrorCubeFEEC b hs).K) :
    ∀ t ∈ Icc a c, U t ∈ (mirrorCubeFEEC b hs).K
  /-- the TSD residual of the discrete solutions tends to `0` uniformly on `[0, T]` -/
  tsd_residual_tendsto (x : (complexCube b s hs).wave.domain)
    (hxK : (x : PiLp 2 (SpaceCube b s)) ∈ (mirrorCubeFEEC b hs).K) (T : ℝ) :
    TendstoUniformlyOn
      (fun N t => infDist ((complexCube b s hs).totalD.graphFst
        ((mirrorCubeFEEC b hs).discrete N (waveLift (complexCube b s hs) x) t))
        ((mirrorCubeFEEC b hs).K : Set (PiLp 2 (SpaceCube b s)))) (fun _ => 0)
      (mirrorCubeFEEC b hs).l (Icc 0 T)

/-- **The FEEC theorem for the EB system (4.14) on every open cube with mirror boundary
conditions**: `MirrorCubeVerdict`. [QuennevilleBelair2015], Thm 4.14, Prop 4.17 (adapted) -/
theorem mirrorCube_verdict : MirrorCubeVerdict b hs :=
  have V := constrainedFEEC (mirrorCubeFEEC b hs)
  { V with
    isReducing := (reducingSubcomplexCube hs).isReducing_wave
    tsd_propagates := _root_.Feec.EinsteinBianchi.cube_tsd_propagates hs
    tsd_residual_tendsto := V.residual_tendsto (reducingSubcomplexCube hs).isReducing_wave }

end Mirror

section BoxMirror

open Feec.Models.Box.Mirror
open Feec.Models.BoundedDomain (R3)

variable (a ℓ : R3) (hℓ : ∀ i, 0 < ℓ i)

/-- The cosine–sine spectral family of the weighted mirror complex on `Q`, `dᵢ = 1/(2ℓᵢ)`. -/
def mirrorFamilyQD : SpectralFamily (complexQD (Models.Box.dB ℓ)) :=
  mirrorSpectralFamily (symmetriesD (Models.Box.dB ℓ)) (fun _ _ => rfl)
    (embeddingQD (Models.Box.dB ℓ)) range_JD

/-- The spectral discretization of the EB system (4.14) on a box with mirror boundary conditions. -/
def mirrorBoxFEEC : ConstrainedFEEC (complexBoxM a ℓ hℓ) ℕ :=
  ((mirrorFamilyQD ℓ).comap (embeddingBox (a := a) hℓ) fun N i x =>
      ⟨pullBC hℓ i (((mirrorFamilyQD ℓ).B N i).starProjection ((pullBC hℓ i).symm x)),
        (pullBC hℓ i).symm_apply_apply _⟩).toFEEC (totalSub (tsdBox a ℓ hℓ)) isClosed_totalSub

/-- **The FEEC verdict for the EB system (4.14) on a mirror box**, with the TSD clauses below. -/
structure MirrorBoxVerdict : Prop extends (mirrorBoxFEEC a ℓ hℓ).Verdict where
  isReducing : (complexBoxM a ℓ hℓ).wave.IsReducing (mirrorBoxFEEC a ℓ hℓ).K
  /-- TSD data stay TSD along strong solutions with TSD forcing -/
  tsd_propagates {s t : ℝ} {F U : ℝ → PiLp 2 (SpaceBox a ℓ)}
    (hU : Evolution.IsStrongSolution (complexBoxM a ℓ hℓ).wave (Icc s t) F U)
    (h0 : U s ∈ (mirrorBoxFEEC a ℓ hℓ).K) (hF : ∀ τ ∈ Icc s t, F τ ∈ (mirrorBoxFEEC a ℓ hℓ).K) :
    ∀ τ ∈ Icc s t, U τ ∈ (mirrorBoxFEEC a ℓ hℓ).K
  /-- the TSD residual of the discrete solutions tends to `0` uniformly on `[0, T]` -/
  tsd_residual_tendsto (x : (complexBoxM a ℓ hℓ).wave.domain)
    (hxK : (x : PiLp 2 (SpaceBox a ℓ)) ∈ (mirrorBoxFEEC a ℓ hℓ).K) (T : ℝ) :
    TendstoUniformlyOn
      (fun N t => infDist ((complexBoxM a ℓ hℓ).totalD.graphFst
        ((mirrorBoxFEEC a ℓ hℓ).discrete N (waveLift (complexBoxM a ℓ hℓ) x) t))
        ((mirrorBoxFEEC a ℓ hℓ).K : Set (PiLp 2 (SpaceBox a ℓ)))) (fun _ => 0)
      (mirrorBoxFEEC a ℓ hℓ).l (Icc 0 T)

/-- **The FEEC theorem for the EB system (4.14) on every box with mirror boundary conditions**:
`MirrorBoxVerdict`. [QuennevilleBelair2015], Thm 4.14, Prop 4.17 (adapted) -/
theorem mirrorBox_verdict : MirrorBoxVerdict a ℓ hℓ :=
  have V := constrainedFEEC (mirrorBoxFEEC a ℓ hℓ)
  { V with
    isReducing := (reducingSubcomplexBox hℓ).isReducing_wave
    tsd_propagates := propagatesBox hℓ
    tsd_residual_tendsto := V.residual_tendsto (reducingSubcomplexBox hℓ).isReducing_wave }

end BoxMirror

section Euclidean

open Feec.Models.Euclidean.GradCurl

/-- The frequency truncation `|ξ| ≤ N` of the EB system (4.14) on `ℝ³`, a reducing family. -/
abbrev euclideanBands : ReducingFamily complex ℕ :=
  bands (Euclidean.symbolComplex gradCurl) (continuous_symbolComplex_m gradCurl)

/-- **The FEEC verdict for the EB system (4.14) on `ℝ³`**, with the TSD clauses below. -/
structure EuclideanVerdict : Prop
    extends toReducing : euclideanBands.Verdict (totalSub constraint) isClosed_totalSub where
  isReducing : complex.wave.IsReducing (totalSub constraint)
  starProjection_mem (N : ℕ) {x : PiLp 2 Space} (hx : x ∈ totalSub constraint) :
    (euclideanBands.B N).starProjection x ∈ totalSub constraint
  /-- TSD data stay TSD along strong solutions with TSD forcing -/
  tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution complex.wave (Icc a b) F U)
    (h0 : U a ∈ totalSub constraint) (hF : ∀ t ∈ Icc a b, F t ∈ totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ totalSub constraint
  /-- the electric constraint is the physical TSD space -/
  physical (f : Lp (W3 Vec Mat Mat 1) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))) :
    𝓕 f ∈ constraint 1 ↔
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))), f x ∈ tsd 0) ∧
        ∀ φ : 𝓢(EuclideanSpace ℝ (Fin 3), W3 Vec Mat Mat 0),
          ⟪f, (Weak.symbolOp (gradCurl.m 0 1) φ).toLp 2⟫_ℂ = 0

/-- **The FEEC theorem for the EB system (4.14) on `ℝ³`**: `EuclideanVerdict`.
[QuennevilleBelair2015], §3.4, Prop 4.17 -/
theorem euclidean_verdict : EuclideanVerdict :=
  ⟨euclideanBands.feec _ _, reducingSubcomplex.isReducing_wave,
    fun N _ hx => starProjection_totalSub_band_mem _ (fun _ _ hu =>
      starProjection_band_mem_fibreSub _ (measurableSet_freqBall N) hu) hx,
    _root_.Feec.EinsteinBianchi.euclidean_tsd_propagates, fourier_mem_constraint_iff⟩

end Euclidean

end GradCurl

/-! ### The strong-symmetry complex (4.16) -/

namespace SymCurl

open Feec.Fourier.SymCurl Feec.ShortHilbertComplex

section Torus

open Feec.Models.Torus.SymCurl

/-- The Fourier spectral discretization of the strong-symmetry EB system (4.18) on `𝕋³`. -/
def torusFEEC : ConstrainedFEEC complex ℕ :=
  (bandSpectralFamily (Fourier.Torus.symbolComplex symCurl)).toFEEC (totalSub constraint)
    isClosed_totalSub

/-- **The FEEC verdict for the strong-symmetry EB system on `𝕋³`**, with the TSD clauses below. -/
structure TorusVerdict : Prop extends torusFEEC.Verdict where
  isReducing : complex.wave.IsReducing torusFEEC.K
  /-- TSD data stay TSD along strong solutions with TSD forcing -/
  tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution complex.wave (Icc a b) F U) (h0 : U a ∈ torusFEEC.K)
    (hF : ∀ t ∈ Icc a b, F t ∈ torusFEEC.K) : ∀ t ∈ Icc a b, U t ∈ torusFEEC.K
  /-- the TSD residual of the discrete solutions tends to `0` uniformly on `[0, T]` -/
  tsd_residual_tendsto (x : complex.wave.domain) (hxK : (x : PiLp 2 Space) ∈ torusFEEC.K) (T : ℝ) :
    TendstoUniformlyOn
      (fun N t => infDist (complex.totalD.graphFst (torusFEEC.discrete N (waveLift complex x) t))
        (torusFEEC.K : Set (PiLp 2 Space))) (fun _ => 0) torusFEEC.l (Icc 0 T)

/-- **The FEEC theorem for the strong-symmetry EB system on `𝕋³`**: `TorusVerdict`.
[QuennevilleBelair2015], Thm 4.14, Prop 4.19 -/
theorem torus_verdict : TorusVerdict :=
  have V := constrainedFEEC torusFEEC
  { V with
    isReducing := reducingSubcomplex.isReducing_wave
    tsd_propagates := Models.Torus.SymCurl.tsd_propagates
    tsd_residual_tendsto := V.residual_tendsto reducingSubcomplex.isReducing_wave }

end Torus

section Euclidean

open Feec.Models.Euclidean.SymCurl

/-- The frequency truncation of the strong-symmetry EB system on `ℝ³`, a reducing family. -/
abbrev euclideanBands : ReducingFamily complex ℕ :=
  bands (Euclidean.symbolComplex symCurl) (continuous_symbolComplex_m symCurl)

/-- **The FEEC verdict for the strong-symmetry EB system on `ℝ³`**, with the TSD clauses below. -/
structure EuclideanVerdict : Prop
    extends toReducing : euclideanBands.Verdict (totalSub constraint) isClosed_totalSub where
  isReducing : complex.wave.IsReducing (totalSub constraint)
  starProjection_mem (N : ℕ) {x : PiLp 2 Space} (hx : x ∈ totalSub constraint) :
    (euclideanBands.B N).starProjection x ∈ totalSub constraint
  /-- TSD data stay TSD along strong solutions with TSD forcing -/
  tsd_propagates {a b : ℝ} {F U : ℝ → PiLp 2 Space}
    (hU : Evolution.IsStrongSolution complex.wave (Icc a b) F U)
    (h0 : U a ∈ totalSub constraint) (hF : ∀ t ∈ Icc a b, F t ∈ totalSub constraint) :
    ∀ t ∈ Icc a b, U t ∈ totalSub constraint

/-- **The FEEC theorem for the strong-symmetry EB system on `ℝ³`**: `EuclideanVerdict`.
[QuennevilleBelair2015], Prop 4.19 -/
theorem euclidean_verdict : EuclideanVerdict :=
  ⟨euclideanBands.feec _ _, reducingSubcomplex.isReducing_wave,
    fun N _ hx => starProjection_totalSub_band_mem _ (fun _ _ hu =>
      starProjection_band_mem_fibreSub _ (measurableSet_freqBall N) hu) hx,
    Models.Euclidean.SymCurl.tsd_propagates⟩

end Euclidean

end SymCurl

end Feec.Instances.EinsteinBianchi
