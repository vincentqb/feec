module

public import Feec.Models.BoundedDomain.GradCurl

/-!
# Bounded domains: TSD constraints for the grad–curl complex (thesis Prop 4.17 refuted)

On an open `Ω ⊆ ℝ³` the thesis' Einstein–Bianchi complex is the minimal grad–curl complex
`H̊¹ --grad--> H̊(curl) --curl--> L²` (`Feec.Models.BoundedDomain.gradCurl`), with the constraint
`L²(TSD)` (symmetric, trace-free, weakly divergence-free, no boundary condition). Every field of
`L²(TSD) ∩ H̊(curl)` has zero mean (`Feec.Models.BoundedDomain.integral_eq_zero_of_mem_tsd`), so
on every nonempty bounded open `Ω`:

* the constant field `diag(1, -1, 0)` lies in the obstruction of `L²(TSD)` for `H̊(curl)`
  (`obstruction_ne_bot`), so `L²(TSD) ∩ H̊(curl)` is not dense in `L²(TSD)`
  (`not_dense_tsd_inter`) — the density claimed in the proof of Prop 4.17 fails;
* the projection hypothesis fails (`exists_projTSD_not_mem_domain`), and
  `{0} × L²(TSD) × S₂` reduces the wave operator of **no** short complex with
  `D(d₁) ⊆ H̊(curl)` containing the test fields (`not_isReducing_tsd`);
* TSD data do **not propagate**: from `(0, 0, β)`, `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ)`, every strong
  solution of the Hodge wave equation of every short complex with `d₁ ⊆ curl_min` leaves the
  constraint (`tsd_not_propagates`), through the `Ė(0)` obstruction
  `Feec.ShortHilbertComplex.not_propagates_of_inner_ne_zero`.

Propagation holds instead on `ℝ³`, on the torus and on cubes with mirror boundary conditions
(`Feec.EinsteinBianchi.{euclidean,torus,cube}_tsd_propagates`).

The Models names of wave 5 (`Feec.Models.BoundedDomain.not_propagates`, …) are deprecated
aliases.

## References

* [QuennevilleBelair2015], §3.4 (Lemma 3.5), §4.10 (Prop 4.17)
* [Arnold2018], §6.2
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ContDiff Matrix ComplexConjugate LinearPMap
open MeasureTheory Set Filter Topology Feec.Domain Feec.Models.BoundedDomain

namespace Feec.Counterexamples.BoundedDomainTSD

variable {Ω : Set R3}

/-! ### Constant fields and the obstruction -/

/-- The constant matrix field `A` on a bounded open `Ω`. -/
def constField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    L2F ℝ Ω Ix :=
  toL2F fun ij => memLp_of_continuous hΩ.measurableSet hb
    (continuous_const : Continuous fun _ : R3 => A ij.1 ij.2)

theorem coeFn_constField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (ij : Ix) :
    (constField hΩ hb A ij : R3 → ℝ) =ᵐ[volume.restrict Ω] fun _ => A ij.1 ij.2 :=
  MemLp.coeFn_toLp (memLp_of_continuous hΩ.measurableSet hb
    (continuous_const : Continuous fun _ : R3 => A ij.1 ij.2))

/-- `⟪F, A⟫ = Σ_{ij} A_{ij} ∫_Ω F_{ij}`. -/
theorem inner_constField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (F : L2F ℝ Ω Ix) :
    ⟪F, constField hΩ hb A⟫_ℝ = ∑ ij : Ix, A ij.1 ij.2 * ∫ x, F ij x ∂volume.restrict Ω := by
  rw [constField, inner_toL2F_eq]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

theorem integral_constField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (ij : Ix) :
    ∫ x, constField hΩ hb A ij x ∂volume.restrict Ω = volume.real Ω * A ij.1 ij.2 := by
  rw [integral_congr_ae (coeFn_constField hΩ hb A ij), integral_const,
    measureReal_restrict_apply_univ, smul_eq_mul]

/-- **Constant symmetric trace-free fields are in `L²(TSD)`** (no boundary condition). -/
theorem constField_mem_tsd (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ = A) (htrA : A.trace = 0) :
    constField hΩ hb A ∈ tsd Ω := by
  set K := constField hΩ hb A
  have hKc := coeFn_constField hΩ hb A
  refine ⟨fun i j => ?_, ?_, fun φ hφ => ?_⟩
  · refine Lp.ext ?_
    filter_upwards [hKc (i, j), hKc (j, i)] with x h1 h2
    rw [h1, h2]
    show A i j = A j i
    rw [← Matrix.transpose_apply A j i, hA]
  · simp only [Fin.sum_univ_three]
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add (K (0, 0) + K (1, 1)) (K (2, 2)),
      Lp.coeFn_add (K (0, 0)) (K (1, 1)), hKc (0, 0), hKc (1, 1), hKc (2, 2),
      Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x h1 h2 h3 h4 h5 h6
    rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, h5, h6]
    simpa [Matrix.trace, Fin.sum_univ_three] using htrA
  · rw [inner_grad_testField _ hφ]
    refine Finset.sum_eq_zero fun ij _ => ?_
    rw [integral_congr_ae (g := fun x => A ij.1 ij.2 * pd ij.2 (φ ij.1) x)
      ((hKc ij).mono fun x hx => by simp only; rw [hx]), integral_const_mul]
    have h0 := integral_pd_mul (hφ ij.1) (contDiff_const (c := (1 : ℝ))) ij.2
    simp only [mul_one] at h0
    rw [h0]
    simp [pd]

/-- The matrix `diag(1, -1, 0)`. -/
def diagA : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, -1, 0; 0, 0, 0]

theorem diagA_transpose : diagA.transpose = diagA := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem diagA_trace : diagA.trace = 0 := by simp [diagA, Matrix.trace, Fin.sum_univ_three]

/-- Fields of `L²(TSD) ∩ H̊(curl)` are orthogonal to every constant field. -/
theorem inner_constField_eq_zero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (A : Matrix (Fin 3) (Fin 3) ℝ) {F : L2F ℝ Ω Ix}
    (hF : F ∈ tsd Ω ⊓ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain) :
    ⟪F, constField hΩ hb A⟫_ℝ = 0 := by
  rw [inner_constField]
  refine Finset.sum_eq_zero fun ij _ => ?_
  rw [integral_eq_zero_of_mem_tsd hΩ hb ⟨F, hF.2⟩ hF.1, mul_zero]

/-- **The obstruction of `L²(TSD)` for `H̊(curl)` contains the constant symmetric trace-free
fields**: they lie in `L²(TSD)` and are orthogonal to `L²(TSD) ∩ H̊(curl)`. -/
theorem constField_mem_obstruction (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ = A) (htrA : A.trace = 0) :
    constField hΩ hb A ∈
      obstruction ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain (tsd Ω) :=
  mem_obstruction.2 ⟨constField_mem_tsd hΩ hb hA htrA, fun _ hz =>
    inner_constField_eq_zero hΩ hb A hz⟩

theorem volume_real_pos (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    0 < volume.real Ω := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos (hΩ.measure_pos volume hne).ne' hb.measure_lt_top.ne

theorem constField_diagA_ne_zero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) : constField hΩ hb diagA ≠ 0 := by
  intro h
  have := integral_constField hΩ hb diagA (0, 0)
  rw [h, show ((0 : L2F ℝ Ω Ix) (0, 0)) = (0 : L2 ℝ Ω) from rfl,
    integral_congr_ae (Lp.coeFn_zero ℝ 2 (volume.restrict Ω))] at this
  have hpos := volume_real_pos hΩ hb hne
  simp [diagA] at this
  linarith

/-- **The density claimed in the proof of Prop 4.17 fails on every nonempty bounded open `Ω`:**
`H̊(curl) ∩ L²(TSD)` is not dense in `L²(TSD)`; the obstruction is nonzero. Thesis: Prop 4.17 -/
theorem obstruction_ne_bot (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    obstruction ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain (tsd Ω) ≠ ⊥ := by
  intro h
  have := constField_mem_obstruction hΩ hb diagA_transpose diagA_trace
  rw [h, Submodule.mem_bot] at this
  exact constField_diagA_ne_zero hΩ hb hne this

theorem not_dense_tsd_inter (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    (tsd Ω ⊓ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain).topologicalClosure ≠
      tsd Ω := fun h =>
  obstruction_ne_bot hΩ hb hne ((dense_iff_obstruction_eq_bot isClosed_tsd).1 h)

/-- A nonnegative test function with positive integral (a bump at a point of `Ω`). -/
theorem exists_isTest_integral_pos (hΩ : IsOpen Ω) (hne : Ω.Nonempty) :
    ∃ g : R3 → ℝ, IsTest Ω g ∧ 0 < ∫ x, g x ∂volume.restrict Ω := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ c hc
  let f : ContDiffBump c := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have ht : tsupport f ⊆ Ω := by
    rw [f.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by show ε / 2 < ε; linarith)).trans hball
  refine ⟨f, ⟨f.contDiff, f.hasCompactSupport, ht⟩, ?_⟩
  rw [integral_restrict_of_eq_zero fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (ht h)]
  exact f.integral_pos

/-- **The projection hypothesis of Prop 4.17 fails** on every nonempty bounded open `Ω`: for
`E = g · diag(1, -1, 0) ∈ C_c^∞(Ω; ℝ³ˣ³)` (any bump `g ≥ 0`, `g ≠ 0`),
`P_{L²(TSD)} E ∉ H̊(curl)`. Thesis: Prop 4.17 -/
theorem exists_projTSD_not_mem_domain (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) : ∃ (Φ : Ix → R3 → ℝ) (hΦ : IsTestField Ω Φ),
      (tsd Ω).starProjection (testField hΦ) ∉
        ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain := by
  obtain ⟨g, hg, hgpos⟩ := exists_isTest_integral_pos hΩ hne
  let Φ : Ix → R3 → ℝ := fun ij x => diagA ij.1 ij.2 * g x
  have hΦ : IsTestField Ω Φ := fun ij => hg.const_mul (diagA ij.1 ij.2)
  refine ⟨Φ, hΦ, fun hP => ?_⟩
  have h1 : ⟪(tsd Ω).starProjection (testField hΦ), constField hΩ hb diagA⟫_ℝ =
      ⟪testField hΦ, constField hΩ hb diagA⟫_ℝ := by
    rw [Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 (constField_mem_tsd hΩ hb diagA_transpose diagA_trace)]
  have h2 := inner_constField_eq_zero hΩ hb diagA
    ⟨Submodule.starProjection_apply_mem _ _, hP⟩
  have hI : ∀ ij : Ix, ∫ x, testField hΦ ij x ∂volume.restrict Ω =
      diagA ij.1 ij.2 * ∫ x, g x ∂volume.restrict Ω := fun ij => by
    rw [← integral_const_mul]
    exact integral_congr_ae (coeFn_testField hΦ ij)
  rw [h1, inner_constField] at h2
  simp only [hI, Fintype.sum_prod_type, Fin.sum_univ_three] at h2
  simp [diagA] at h2
  linarith

/-! ### Failure of TSD propagation for the Einstein–Bianchi system -/

-- Over `𝕜 = ℝ` the generic real structure on the window spaces (needed for time derivatives
-- over a general `𝕜`) duplicates the inner-product one; use the latter.
attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-- **`K = {0} × L²(TSD) × S₂` does not reduce the wave operator** (the projection hypothesis
`P_K D(L) ⊆ D(L)` of Prop 4.17 fails) for every short complex with `D(d₁) ⊆ H̊(curl)` containing
the test fields in `D(d₁) ∩ D(d₀†)`, on every nonempty bounded open `Ω`. Thesis: Prop 4.17 -/
theorem not_isReducing_tsd (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    {W₀ W₂ : Type} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] [CompleteSpace W₀]
    [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂] [CompleteSpace W₂]
    (S : ShortHilbertComplex ℝ W₀ (L2F ℝ Ω Ix) W₂) (S₂ : Submodule ℝ W₂)
    [S₂.HasOrthogonalProjection]
    (hd₁ : S.d₁.domain ≤ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain)
    (htest : ∀ (Φ : Ix → R3 → ℝ) (hΦ : IsTestField Ω Φ),
      testField hΦ ∈ S.d₁.domain ∧ testField hΦ ∈ S.d₀†.domain) :
    ¬ S.wave.IsReducing
      (HilbertComplex.totalSub (ShortHilbertComplex.family3 (⊥ : Submodule ℝ W₀) (tsd Ω) S₂)) := by
  intro hred
  obtain ⟨Φ, hΦ, hnot⟩ := exists_projTSD_not_mem_domain hΩ hb hne
  let x : PiLp 2 (ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) W₂) :=
    WithLp.toLp 2 (Pi.single (M := ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) W₂) 1 (testField hΦ))
  have hx0 : (x 0 : W₀) = 0 := rfl
  have hx1 : (x 1 : L2F ℝ Ω Ix) = testField hΦ := rfl
  have hx2 : (x 2 : W₂) = 0 := rfl
  have hxD : x ∈ S.wave.domain := by
    rw [S.mem_wave_domain, hx0, hx1, hx2]
    exact ⟨Submodule.zero_mem _, (htest Φ hΦ).1, (htest Φ hΦ).2, Submodule.zero_mem _⟩
  have hP := hred.proj_mem ⟨x, hxD⟩
  rw [S.mem_wave_domain] at hP
  have h1 := hP.2.1
  rw [HilbertComplex.totalSub_starProjection_apply] at h1
  exact hnot (hd₁ h1)

/-- The magnetic datum `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ)`. -/
def betaField : Ix → R3 → ℝ := fun ij =>
  if ij = (0, 1) ∨ ij = (1, 0) then (fun x : R3 => x 2) else 0

theorem contDiff_betaField (ij : Ix) : ContDiff ℝ ∞ (betaField ij) := by
  unfold betaField
  split_ifs
  exacts [contDiff_apply ℝ (fun _ : Fin 3 => ℝ) 2, contDiff_const]

/-- `curl β = -diag(1, -1, 0)`. -/
theorem curlM_betaField (ij : Ix) (x : R3) : curlM betaField ij x = -diagA ij.1 ij.2 := by
  obtain ⟨i, k⟩ := ij
  simp only [curlM, betaField, pd_ite_zero, pd_coord]
  fin_cases i <;> fin_cases k <;> simp [diagA]

/-- `β` as an element of `L²(Ω; ℝ³ˣ³)` (`Ω` bounded). -/
def betaL2 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : L2F ℝ Ω Ix :=
  toL2F fun ij => memLp_of_continuous hΩ.measurableSet hb (contDiff_betaField ij).continuous

/-- `β ∈ L²(TSD)`. -/
theorem betaL2_mem_tsd (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : betaL2 hΩ hb ∈ tsd Ω := by
  set K := betaL2 hΩ hb
  have hKc : ∀ ij, (K ij : R3 → ℝ) =ᵐ[volume.restrict Ω] betaField ij := fun ij =>
    MemLp.coeFn_toLp (memLp_of_continuous hΩ.measurableSet hb (contDiff_betaField ij).continuous)
  have hsym : ∀ i j, betaField (i, j) = betaField (j, i) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [betaField]
  have hdiag : ∀ i, betaField (i, i) = 0 := by
    intro i
    fin_cases i <;> simp [betaField]
  refine ⟨fun i j => ?_, ?_, fun φ hφ => ?_⟩
  · refine Lp.ext ?_
    filter_upwards [hKc (i, j), hKc (j, i)] with x h1 h2
    rw [h1, h2, hsym]
  · simp only [Fin.sum_univ_three]
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add (K (0, 0) + K (1, 1)) (K (2, 2)),
      Lp.coeFn_add (K (0, 0)) (K (1, 1)), hKc (0, 0), hKc (1, 1), hKc (2, 2),
      Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x h1 h2 h3 h4 h5 h6
    rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, h5, h6, hdiag, hdiag, hdiag]
    simp
  · have hpd : ∀ ij : Ix, ∀ x, pd ij.2 (betaField ij) x = 0 := by
      rintro ⟨i, j⟩ x
      fin_cases i <;> fin_cases j <;> simp [betaField, pd_coord, pd_zero]
    rw [inner_grad_testField _ hφ]
    refine Finset.sum_eq_zero fun ij _ => ?_
    rw [integral_congr_ae (g := fun x => pd ij.2 (φ ij.1) x * betaField ij x)
      ((hKc ij).mono fun x hx => by simp only; rw [hx, mul_comm]),
      integral_pd_mul (hφ ij.1) ((contDiff_betaField ij).of_le (by simp)) ij.2]
    simp [hpd]

/-- `β ∈ D(d₁†)` with `d₁† β = curl β = -diag(1, -1, 0)`, for every complex with
`d₁ ⊆ curl_min`. -/
theorem betaL2_mem_adjoint (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {W₀ : Type*}
    [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] [CompleteSpace W₀]
    (S : ShortHilbertComplex ℝ W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))
    (hd₁ : S.d₁ ≤ (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω) :
    ∃ h : betaL2 hΩ hb ∈ S.d₁†.domain, S.d₁† ⟨_, h⟩ = -constField hΩ hb diagA := by
  have hmax : ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω)† ≤ S.d₁† :=
    LinearPMap.adjoint_le_adjoint_of_le S.dense₁ hd₁
  have hcurl : ∀ ij, MemLp ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.apply betaField ij) 2
      (volume.restrict Ω) := fun ij => by
    rw [← curlM_eq_formalAdj_apply]
    exact memLp_of_continuous hΩ.measurableSet hb
      (continuous_curlM (fun ij => (contDiff_betaField ij).of_le (by simp)) ij)
  obtain ⟨hmem, hval⟩ := (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.smooth_mem_maximal_domain
    hΩ (N := 1) curlOp_isOrderLE.formalAdj (fun ij => (contDiff_betaField ij).of_le (by simp))
    (fun ij => memLp_of_continuous hΩ.measurableSet hb (contDiff_betaField ij).continuous) hcurl
  have e := (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).adjoint_minimal (Ω := Ω)
  have hmem' : betaL2 hΩ hb ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω)†.domain := by
    rw [e]; exact hmem
  have hval' : ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω)† ⟨_, hmem'⟩ = toL2F hcurl := by
    have key : ∀ T : L2F ℝ Ω Ix →ₗ.[ℝ] L2F ℝ Ω Ix,
        T = (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.maximal Ω →
        ∀ h : betaL2 hΩ hb ∈ T.domain, T ⟨_, h⟩ = toL2F hcurl := by
      rintro _ rfl h; exact hval
    exact key _ e _
  refine ⟨hmax.1 hmem', ?_⟩
  rw [← hmax.2 (x := ⟨_, hmem'⟩) (y := ⟨_, hmax.1 hmem'⟩) rfl, hval']
  refine (WithLp.ext_iff 2).2 (funext fun ij => Lp.ext ?_)
  filter_upwards [MemLp.coeFn_toLp (hcurl ij), Lp.coeFn_neg (constField hΩ hb diagA ij),
    coeFn_constField hΩ hb diagA ij] with x h1 h2 h3
  simp only [toL2F, PiLp.neg_apply] at h1 h2 ⊢
  rw [h1, h2, Pi.neg_apply, h3, ← curlM_eq_formalAdj_apply, curlM_betaField]

/-- **TSD data do not propagate** (the conclusion of thesis Prop 4.17 fails on every nonempty
bounded open `Ω ⊆ ℝ³`): for every short complex `W₀ → L²(Ω; ℝ³ˣ³) → L²(Ω; ℝ³ˣ³)` with
`d₁ ⊆ curl_min` (the electric boundary condition), the TSD datum `(0, 0, β)` lies in
`D(L) ∩ K`, `K = {0} × L²(TSD) × L²(TSD)`, and for every `T > 0` **every** strong solution of
`U' = L U` on `[0, T]` from it leaves `K`. Proof: the `Ė(0)` obstruction
(`ShortHilbertComplex.not_propagates_of_inner_ne_zero`) with `G = diag(1, -1, 0)`, orthogonal
to `L²(TSD) ∩ H̊(curl)` by the zero-mean theorem, and `⟪G, d₁† β⟫ = -2 |Ω| ≠ 0`.
Thesis: Prop 4.17 -/
theorem tsd_not_propagates (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    {W₀ : Type} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] [CompleteSpace W₀]
    (S : ShortHilbertComplex ℝ W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))
    (hd₁ : S.d₁ ≤ (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω) :
    ∃ U₀ ∈ S.wave.domain, U₀ ∈ HilbertComplex.totalSub
        (ShortHilbertComplex.family3 (⊥ : Submodule ℝ W₀) (tsd Ω) (tsd Ω)) ∧
      ∀ T > 0, ∀ U : ℝ → PiLp 2 (ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix)), U 0 = U₀ →
        Evolution.IsStrongSolution S.wave (Icc 0 T) 0 U →
          ∃ t ∈ Icc 0 T, U t ∉ HilbertComplex.totalSub
            (ShortHilbertComplex.family3 (⊥ : Submodule ℝ W₀) (tsd Ω) (tsd Ω)) := by
  obtain ⟨hβ, hβv⟩ := betaL2_mem_adjoint hΩ hb S hd₁
  let U₀ : PiLp 2 (ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix)) :=
    WithLp.toLp 2
      (Pi.single (M := ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix)) 2 (betaL2 hΩ hb))
  have h0 : (U₀ 0 : W₀) = 0 := rfl
  have h1 : (U₀ 1 : L2F ℝ Ω Ix) = 0 := rfl
  have h2 : (U₀ 2 : L2F ℝ Ω Ix) = betaL2 hΩ hb := rfl
  have hD : U₀ ∈ S.wave.domain := by
    rw [S.mem_wave_domain, h0, h1, h2]
    exact ⟨Submodule.zero_mem _, Submodule.zero_mem _, Submodule.zero_mem _, hβ⟩
  have hK : U₀ ∈ HilbertComplex.totalSub
      (ShortHilbertComplex.family3 (⊥ : Submodule ℝ W₀) (tsd Ω) (tsd Ω)) := by
    intro i
    match i with
    | 0 =>
      show (U₀ 0 : W₀) ∈ (⊥ : Submodule ℝ W₀)
      rw [h0]; exact Submodule.zero_mem _
    | 1 => exact h1 ▸ Submodule.zero_mem _
    | 2 => exact h2 ▸ betaL2_mem_tsd hΩ hb
  refine ⟨U₀, hD, hK, fun T hT U hU0 hU => ?_⟩
  have hG : constField hΩ hb diagA ∈ (tsd Ω ⊓ S.d₁.domain)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    exact inner_constField_eq_zero hΩ hb diagA ⟨hz.1, hd₁.1 hz.2⟩
  have hne0 : ⟪constField hΩ hb diagA, S.d₁† ⟨_, hβ⟩⟫_ℝ ≠ 0 := by
    rw [hβv, inner_neg_right, real_inner_comm, inner_constField]
    simp only [integral_constField, Fintype.sum_prod_type, Fin.sum_univ_three]
    have hpos := volume_real_pos hΩ hb hne
    simp [diagA]
    positivity
  obtain ⟨t, ht, hnot⟩ := S.not_propagates_of_inner_ne_zero hG ⟨_, hβ⟩ hne0 hT hU
    (by rw [hU0]; exact h0) (by rw [hU0]; exact h2)
  exact ⟨t, ht, fun hmem => hnot (hmem 1)⟩

end Feec.Counterexamples.BoundedDomainTSD

/-! ### Deprecated names -/

namespace Feec.Models.BoundedDomain

@[deprecated (since := "2026-10-17")] alias constField :=
  Counterexamples.BoundedDomainTSD.constField
@[deprecated (since := "2026-10-17")] alias coeFn_constField :=
  Counterexamples.BoundedDomainTSD.coeFn_constField
@[deprecated (since := "2026-10-17")] alias inner_constField :=
  Counterexamples.BoundedDomainTSD.inner_constField
@[deprecated (since := "2026-10-17")] alias integral_constField :=
  Counterexamples.BoundedDomainTSD.integral_constField
@[deprecated (since := "2026-10-17")] alias constField_mem_tsd :=
  Counterexamples.BoundedDomainTSD.constField_mem_tsd
@[deprecated (since := "2026-10-17")] alias diagA :=
  Counterexamples.BoundedDomainTSD.diagA
@[deprecated (since := "2026-10-17")] alias diagA_transpose :=
  Counterexamples.BoundedDomainTSD.diagA_transpose
@[deprecated (since := "2026-10-17")] alias diagA_trace :=
  Counterexamples.BoundedDomainTSD.diagA_trace
@[deprecated (since := "2026-10-17")] alias inner_constField_eq_zero :=
  Counterexamples.BoundedDomainTSD.inner_constField_eq_zero
@[deprecated (since := "2026-10-17")] alias constField_mem_obstruction :=
  Counterexamples.BoundedDomainTSD.constField_mem_obstruction
@[deprecated (since := "2026-10-17")] alias volume_real_pos :=
  Counterexamples.BoundedDomainTSD.volume_real_pos
@[deprecated (since := "2026-10-17")] alias constField_diagA_ne_zero :=
  Counterexamples.BoundedDomainTSD.constField_diagA_ne_zero
@[deprecated (since := "2026-10-17")] alias obstruction_ne_bot :=
  Counterexamples.BoundedDomainTSD.obstruction_ne_bot
@[deprecated (since := "2026-10-17")] alias not_dense_tsd_inter :=
  Counterexamples.BoundedDomainTSD.not_dense_tsd_inter
@[deprecated (since := "2026-10-17")] alias exists_isTest_integral_pos :=
  Counterexamples.BoundedDomainTSD.exists_isTest_integral_pos
@[deprecated (since := "2026-10-17")] alias exists_projTSD_not_mem_domain :=
  Counterexamples.BoundedDomainTSD.exists_projTSD_not_mem_domain
@[deprecated (since := "2026-10-17")] alias not_isReducing_wave_tsd :=
  Counterexamples.BoundedDomainTSD.not_isReducing_tsd
@[deprecated (since := "2026-10-17")] alias betaField :=
  Counterexamples.BoundedDomainTSD.betaField
@[deprecated (since := "2026-10-17")] alias contDiff_betaField :=
  Counterexamples.BoundedDomainTSD.contDiff_betaField
@[deprecated (since := "2026-10-17")] alias curlM_betaField :=
  Counterexamples.BoundedDomainTSD.curlM_betaField
@[deprecated (since := "2026-10-17")] alias betaL2 :=
  Counterexamples.BoundedDomainTSD.betaL2
@[deprecated (since := "2026-10-17")] alias betaL2_mem_tsd :=
  Counterexamples.BoundedDomainTSD.betaL2_mem_tsd
@[deprecated (since := "2026-10-17")] alias betaL2_mem_adjoint :=
  Counterexamples.BoundedDomainTSD.betaL2_mem_adjoint
@[deprecated (since := "2026-10-17")] alias not_propagates :=
  Counterexamples.BoundedDomainTSD.tsd_not_propagates

end Feec.Models.BoundedDomain

namespace Feec.EinsteinBianchi

@[deprecated (since := "2026-10-17")] alias boundedDomain_tsd_not_propagates :=
  Counterexamples.BoundedDomainTSD.tsd_not_propagates

end Feec.EinsteinBianchi
