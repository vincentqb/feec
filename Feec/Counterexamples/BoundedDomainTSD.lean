module

public import Feec.Models.BoundedDomain.Interior

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
* the projection hypothesis fails (`exists_projTSD_not_mem_domain`), `D(L) ∩ K` is not dense in
  `K` (`not_mem_closure_wave_domain_inter`), and
  `{0} × L²(TSD) × S₂` reduces the wave operator of **no** short complex with
  `D(d₁) ⊆ H̊(curl)` containing the test fields (`not_isReducing_tsd`);
* TSD data do **not propagate**: from `(0, 0, β)`, `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ)`, every strong
  solution of the Hodge wave equation of every short complex with `d₁ ⊆ curl_min` leaves the
  constraint (`tsd_not_propagates`), through the `Ė(0)` obstruction
  `Feec.ShortHilbertComplex.not_propagates_of_inner_ne_zero`.
  With existence (the wave group orbit): `exists_isStrongSolution_tsd_not_propagates`; for every
  datum `(0, E₀, β)`, any `E₀`: `betaL2_not_propagates` (`d₁† β = curl β ∉ L²(TSD₀)`).
* the **magnetic** projection hypothesis fails too, independently: `P_{L²(TSD)} D(d₁†) ⊄ D(d₁†)`
  for every short complex with `d₁ ⊆ curl_min` (`not_starProjection_mem_adjoint_domain`, by the
  closed graph theorem; `H(curl)` form `not_starProjection_mem_curl_maximal`, Bochner form
  `not_starProjection_mem_curl_maximal_bochner`, both parts `not_projection_magnetic`), and
  `P_{L²(TSD)}` is unbounded in the `H(curl)` graph norm (`projection_unbounded`);
* **the density gap** (`density_dichotomy`, `density_gap`): on domains star-shaped with respect to
  a ball, the literal density conjectures hold and `cl (L²(TSD) ∩ H(curl)) = L²(TSD)`, but
  `cl (L²(TSD) ∩ H̊(curl)) = L²(TSD₀) ≠ L²(TSD)`;
* **the corrected Prop 4.17** (`invariantCore_tsd`): the invariant core `K*` of
  `K = {0} × L²(TSD) × L²(TSD)` is `{0} × S₁* × S₂*`, a reducing subcomplex, the largest one, with
  `S₁* ⊆ L²(TSD₀)`, `diag(1, -1, 0) ∈ L²(TSD) \ S₁*`, `β ∈ L²(TSD) \ S₂*`, and the nonzero
  stationary datum `diag(1, -1, 0) ∈ S₂*`;
* the violation is confined to the **boundary layer** `Ω \ depDomain Ω t`
  (`beta_violation_boundary_layer`, `violation_boundary_layer`), by the interior finite speed of
  propagation of `Feec.Models.BoundedDomain.tsd_depDomain`.

Propagation holds instead on `ℝ³`, on the torus and on cubes with mirror boundary conditions
(`Feec.EinsteinBianchi.{euclidean,torus,cube}_tsd_propagates`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §3.4 (Lemma 3.5), §4.10 (Prop 4.17)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], §6.2

Bibliography: [references.bib](../../docs/references.bib)
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
    rw [integral_congr_ae (g := fun x => A ij.1 ij.2 * partialDeriv ij.2 (φ ij.1) x)
      ((hKc ij).mono fun x hx => by simp only; rw [hx]), integral_const_mul]
    have h0 := integral_pd_mul (hφ ij.1) (contDiff_const (c := (1 : ℝ))) ij.2
    simp only [mul_one] at h0
    rw [h0]
    simp [partialDeriv]

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
`H̊(curl) ∩ L²(TSD)` is not dense in `L²(TSD)`; the obstruction is nonzero. [QuennevilleBelair2015], Prop 4.17 -/
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
`P_{L²(TSD)} E ∉ H̊(curl)`. [QuennevilleBelair2015], Prop 4.17 -/
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

/-- **A projection that leaves the middle domain**: if `y ∈ D(d₁) ∩ D(d₀†)` and
`P_{K₁} y ∉ D(d₁)`, then `{0} × K₁ × S₂` does not reduce the wave operator, for every `S₂`
(the projection of `(0, y, 0) ∈ D(L)` is not in `D(L)`). -/
theorem not_isReducing_of_starProjection_not_mem {W₀ W₁ W₂ : Type}
    [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] [CompleteSpace W₀]
    [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁] [CompleteSpace W₁]
    [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂] [CompleteSpace W₂]
    (S : ShortHilbertComplex ℝ W₀ W₁ W₂) (K₁ : Submodule ℝ W₁) [K₁.HasOrthogonalProjection]
    (S₂ : Submodule ℝ W₂) [S₂.HasOrthogonalProjection] {y : W₁} (hy : y ∈ S.d₁.domain)
    (hy' : y ∈ S.d₀†.domain) (hP : K₁.starProjection y ∉ S.d₁.domain) :
    ¬ S.wave.IsReducing
      (HilbertComplex.totalSub (ShortHilbertComplex.family3 (⊥ : Submodule ℝ W₀) K₁ S₂)) := by
  intro hred
  let x : PiLp 2 (ShortHilbertComplex.W3 W₀ W₁ W₂) :=
    WithLp.toLp 2 (Pi.single (M := ShortHilbertComplex.W3 W₀ W₁ W₂) 1 y)
  have hxD : x ∈ S.wave.domain := by
    rw [S.mem_wave_domain, show (x 0 : W₀) = 0 from rfl, show (x 1 : W₁) = y from rfl,
      show (x 2 : W₂) = 0 from rfl]
    exact ⟨Submodule.zero_mem _, hy, hy', Submodule.zero_mem _⟩
  have hP' := hred.proj_mem ⟨x, hxD⟩
  rw [S.mem_wave_domain] at hP'
  have h1 := hP'.2.1
  rw [HilbertComplex.totalSub_starProjection_apply] at h1
  exact hP h1

/-- **`K = {0} × L²(TSD) × S₂` does not reduce the wave operator** (the projection hypothesis
`P_K D(L) ⊆ D(L)` of Prop 4.17 fails) for every short complex with `D(d₁) ⊆ H̊(curl)` containing
the test fields in `D(d₁) ∩ D(d₀†)`, on every nonempty bounded open `Ω`. [QuennevilleBelair2015], Prop 4.17 -/
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
  obtain ⟨Φ, hΦ, hnot⟩ := exists_projTSD_not_mem_domain hΩ hb hne
  exact not_isReducing_of_starProjection_not_mem S _ S₂ (htest Φ hΦ).1 (htest Φ hΦ).2
    fun h => hnot (hd₁ h)

/-- **`D(L) ∩ K` is not dense in `K`** for `K = {0} × L²(TSD) × S₂` and every short complex with
`D(d₁) ⊆ H̊(curl)`: the datum `(0, diag(1, -1, 0), 0) ∈ K` is orthogonal to the middle
components of `D(L) ∩ K`, so it is not in the closure (the density hypothesis of Prop 4.17
fails). [QuennevilleBelair2015], Prop 4.17 -/
theorem not_mem_closure_wave_domain_inter (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) {W₀ W₂ : Type} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀]
    [CompleteSpace W₀] [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂] [CompleteSpace W₂]
    (S : ShortHilbertComplex ℝ W₀ (L2F ℝ Ω Ix) W₂) (S₂ : Submodule ℝ W₂)
    (hd₁ : S.d₁.domain ≤ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain) :
    ∃ k ∈ HilbertComplex.totalSub (ShortHilbertComplex.family3 (⊥ : Submodule ℝ W₀) (tsd Ω) S₂),
      k ∉ closure ((S.wave.domain : Set (PiLp 2 (ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) W₂))) ∩
        HilbertComplex.totalSub (ShortHilbertComplex.family3 (⊥ : Submodule ℝ W₀) (tsd Ω) S₂)) := by
  set G := constField hΩ hb diagA
  let k : PiLp 2 (ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) W₂) :=
    WithLp.toLp 2 (Pi.single (M := ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) W₂) 1 G)
  have hk1 : (k 1 : L2F ℝ Ω Ix) = G :=
    Pi.single_eq_same (M := ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) W₂) 1 G
  have hkK : k ∈ HilbertComplex.totalSub
      (ShortHilbertComplex.family3 (⊥ : Submodule ℝ W₀) (tsd Ω) S₂) := by
    intro i
    match i with
    | 0 => exact Submodule.zero_mem _
    | 1 => exact hk1 ▸ constField_mem_tsd hΩ hb diagA_transpose diagA_trace
    | 2 => exact Submodule.zero_mem _
  refine ⟨k, hkK, fun hcl => ?_⟩
  let f : PiLp 2 (ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) W₂) → ℝ :=
    fun y => ⟪(y 1 : L2F ℝ Ω Ix), G⟫_ℝ
  have hf : Continuous f :=
    ((PiLp.continuous_apply 2 _ 1).inner continuous_const)
  have hsub : (S.wave.domain : Set (PiLp 2 (ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) W₂))) ∩
      HilbertComplex.totalSub (ShortHilbertComplex.family3 (⊥ : Submodule ℝ W₀) (tsd Ω) S₂) ⊆
      f ⁻¹' {0} := by
    rintro y ⟨hyD, hyK⟩
    have hyD' : y ∈ S.wave.domain := hyD
    rw [S.mem_wave_domain] at hyD'
    exact inner_constField_eq_zero hΩ hb diagA ⟨hyK 1, hd₁ hyD'.2.1⟩
  have h0 := closure_minimal hsub (isClosed_singleton.preimage hf) hcl
  simp only [Set.mem_preimage, Set.mem_singleton_iff, f, hk1] at h0
  exact constField_diagA_ne_zero hΩ hb hne (inner_self_eq_zero.1 h0)

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
  simp only [curlM, betaField, pd_ite_zero, partialDeriv_apply_coord]
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
  · have hpd : ∀ ij : Ix, ∀ x, partialDeriv ij.2 (betaField ij) x = 0 := by
      rintro ⟨i, j⟩ x
      fin_cases i <;> fin_cases j <;> simp [betaField, partialDeriv_apply_coord, partialDeriv_zero]
    rw [inner_grad_testField _ hφ]
    refine Finset.sum_eq_zero fun ij _ => ?_
    rw [integral_congr_ae (g := fun x => partialDeriv ij.2 (φ ij.1) x * betaField ij x)
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

/-- **The `Ė(0)` obstruction for the datum `(0, 0, β)`**: for a short complex
`W₀ → W₁ → W₂`, constraint spaces `K₁ ⊆ W₁`, `K₂ ⊆ W₂`, `β ∈ D(d₁†) ∩ K₂` and
`G ⊥ K₁ ∩ D(d₁)` with `⟪G, d₁† β⟫ ≠ 0`, the datum `(0, 0, β)` lies in `D(L) ∩ K`,
`K = {0} × K₁ × K₂`, and for every `T > 0` every strong solution of `U' = L U` on `[0, T]` from
it leaves `K` (`ShortHilbertComplex.not_propagates_of_inner_ne_zero`). -/
theorem exists_single_two_not_propagates {W₀ W₁ W₂ : Type}
    [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] [CompleteSpace W₀]
    [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁] [CompleteSpace W₁]
    [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂] [CompleteSpace W₂]
    (S : ShortHilbertComplex ℝ W₀ W₁ W₂) {K₁ : Submodule ℝ W₁} {K₂ : Submodule ℝ W₂} {β : W₂}
    (hβ : β ∈ S.d₁†.domain) (hβK : β ∈ K₂) {G : W₁} (hG : G ∈ (K₁ ⊓ S.d₁.domain)ᗮ)
    (hne : ⟪G, S.d₁† ⟨β, hβ⟩⟫_ℝ ≠ 0) :
    ∃ U₀ ∈ S.wave.domain,
      U₀ ∈ HilbertComplex.totalSub (ShortHilbertComplex.family3 (⊥ : Submodule ℝ W₀) K₁ K₂) ∧
      ∀ T > 0, ∀ U : ℝ → PiLp 2 (ShortHilbertComplex.W3 W₀ W₁ W₂), U 0 = U₀ →
        Evolution.IsStrongSolution S.wave (Icc 0 T) 0 U →
          ∃ t ∈ Icc 0 T, U t ∉
            HilbertComplex.totalSub (ShortHilbertComplex.family3 (⊥ : Submodule ℝ W₀) K₁ K₂) := by
  let U₀ : PiLp 2 (ShortHilbertComplex.W3 W₀ W₁ W₂) :=
    WithLp.toLp 2 (Pi.single (M := ShortHilbertComplex.W3 W₀ W₁ W₂) 2 β)
  have h0 : (U₀ 0 : W₀) = 0 := rfl
  have h2 : (U₀ 2 : W₂) = β := rfl
  refine ⟨U₀, ?_, ShortHilbertComplex.single_two_mem_totalSub_family3 _ _ _ hβK,
    fun T hT U hU0 hU => ?_⟩
  · rw [S.mem_wave_domain, h0, show (U₀ 1 : W₁) = 0 from rfl, h2]
    exact ⟨Submodule.zero_mem _, Submodule.zero_mem _, Submodule.zero_mem _, hβ⟩
  obtain ⟨t, ht, hnot⟩ := S.not_propagates_of_inner_ne_zero hG ⟨β, hβ⟩ hne hT hU
    (by rw [hU0]; exact h0) (by rw [hU0]; exact h2)
  exact ⟨t, ht, fun hmem => hnot (hmem 1)⟩

/-- **TSD data do not propagate** (the conclusion of thesis Prop 4.17 fails on every nonempty
bounded open `Ω ⊆ ℝ³`): for every short complex `W₀ → L²(Ω; ℝ³ˣ³) → L²(Ω; ℝ³ˣ³)` with
`d₁ ⊆ curl_min` (the electric boundary condition), the TSD datum `(0, 0, β)` lies in
`D(L) ∩ K`, `K = {0} × L²(TSD) × L²(TSD)`, and for every `T > 0` **every** strong solution of
`U' = L U` on `[0, T]` from it leaves `K`. Proof: the `Ė(0)` obstruction
(`ShortHilbertComplex.not_propagates_of_inner_ne_zero`) with `G = diag(1, -1, 0)`, orthogonal
to `L²(TSD) ∩ H̊(curl)` by the zero-mean theorem, and `⟪G, d₁† β⟫ = -2 |Ω| ≠ 0`.
[QuennevilleBelair2015], Prop 4.17 -/
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
  refine exists_single_two_not_propagates S hβ (betaL2_mem_tsd hΩ hb)
    ((Submodule.mem_orthogonal _ _).2 fun z hz =>
      inner_constField_eq_zero hΩ hb diagA ⟨hz.1, hd₁.1 hz.2⟩) ?_
  rw [hβv, inner_neg_right, real_inner_comm, inner_constField]
  simp only [integral_constField, Fintype.sum_prod_type, Fin.sum_univ_three]
  have hpos := volume_real_pos hΩ hb hne
  simp [diagA]
  positivity

/-! ### Every datum `(0, E₀, β)` leaves the constraint; existence of the solutions -/

/-- `curl β = -diag(1, -1, 0)` as an `L²` field. -/
theorem curl_betaL2 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    smoothField hΩ hb (curlM betaField)
      (continuous_curlM fun ij => (contDiff_betaField ij).of_le (by simp)) =
      -constField hΩ hb diagA := by
  refine (WithLp.ext_iff 2).2 (funext fun ij => Lp.ext ?_)
  filter_upwards [coeFn_smoothField hΩ hb (curlM betaField)
    (continuous_curlM fun ij => (contDiff_betaField ij).of_le (by simp)) ij,
    Lp.coeFn_neg (constField hΩ hb diagA ij), coeFn_constField hΩ hb diagA ij] with x h1 h2 h3
  simp only [PiLp.neg_apply] at h2 ⊢
  rw [h1, h2, Pi.neg_apply, h3, curlM_betaField]

/-- Constant fields are orthogonal to `L²(TSD₀)`. -/
theorem constField_mem_orthogonal_tsd₀ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (A : Matrix (Fin 3) (Fin 3) ℝ) : constField hΩ hb A ∈ (tsd₀ Ω hΩ hb)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro B hB
  rw [real_inner_comm, inner_constField]
  exact Finset.sum_eq_zero fun ij _ => by rw [integral_eq_zero_of_mem_tsd₀ hΩ hb hB, mul_zero]

/-- `diag(1, -1, 0) ∉ L²(TSD₀)` on a nonempty `Ω`: it has nonzero mean. -/
theorem constField_diagA_not_mem_tsd₀ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) : constField hΩ hb diagA ∉ tsd₀ Ω hΩ hb := by
  intro h
  have h0 := integral_eq_zero_of_mem_tsd₀ hΩ hb h 0 0
  rw [integral_constField] at h0
  have hpos := volume_real_pos hΩ hb hne
  simp [diagA] at h0
  exact hpos.ne' h0

/-- `curl β ∉ L²(TSD₀)`. -/
theorem curl_betaL2_not_mem_tsd₀ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) : smoothField hΩ hb (curlM betaField)
      (continuous_curlM fun ij => (contDiff_betaField ij).of_le (by simp)) ∉ tsd₀ Ω hΩ hb := by
  rw [curl_betaL2]
  intro hm
  exact constField_diagA_not_mem_tsd₀ hΩ hb hne (by simpa using (tsd₀ Ω hΩ hb).neg_mem hm)

/-- **Every datum `(0, E₀, β)` leaves `L²(TSD)` at once**: for every short complex with
`d₁ ⊆ curl_min`, every `E₀` and every `T > 0`, every strong solution of `U' = L U` on `[0, T]` from
`(0, E₀, β)` has its electric field outside `L²(TSD)` at some `t ∈ [0, T]`, because
`d₁† β = curl β ∉ L²(TSD₀)` (`Feec.Models.BoundedDomain.adjoint_mem_tsd₀_of_propagates`).
[QuennevilleBelair2015], Prop 4.17 -/
theorem betaL2_not_propagates (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    {W₀ : Type} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] [CompleteSpace W₀]
    (S : ShortHilbertComplex ℝ W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))
    (hd₁ : S.d₁ ≤ (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω) {T : ℝ} (hT : 0 < T)
    {U : ℝ → PiLp 2 (ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))}
    (hU : Evolution.IsStrongSolution S.wave (Icc 0 T) 0 U)
    (h0 : ((U 0 : PiLp 2 (ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))) 0 : W₀) = 0)
    (h2 : ((U 0 : PiLp 2 (ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))) 2 :
      L2F ℝ Ω Ix) = betaL2 hΩ hb) :
    ∃ t ∈ Icc 0 T,
      ((U t : PiLp 2 (ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))) 1 : L2F ℝ Ω Ix) ∉
        tsd Ω := by
  by_contra hall
  push Not at hall
  obtain ⟨hB, hm⟩ := adjoint_mem_tsd₀_of_propagates hΩ hb S hd₁ hT hU h0 hall
  obtain ⟨hβ, hβv⟩ := smoothField_mem_adjoint hΩ hb S hd₁
    (fun ij => (contDiff_betaField ij).of_le (by simp))
  have e : (⟨_, hB⟩ : S.d₁†.domain) = ⟨_, hβ⟩ := Subtype.ext h2
  rw [e, hβv] at hm
  exact curl_betaL2_not_mem_tsd₀ hΩ hb hne hm

/-- **TSD data do not propagate, with existence**: for every short complex with
`d₁ ⊆ curl_min` the TSD datum `(0, 0, β) ∈ D(L) ∩ K` has, on every `[0, T]`, `T > 0`, a strong
solution (the wave group orbit, Stone's theorem), and every strong solution from it leaves
`K = {0} × L²(TSD) × L²(TSD)`. [QuennevilleBelair2015], Prop 4.17 -/
theorem exists_isStrongSolution_tsd_not_propagates (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) {W₀ : Type} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀]
    [CompleteSpace W₀] (S : ShortHilbertComplex ℝ W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))
    (hd₁ : S.d₁ ≤ (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω) :
    ∃ U₀ ∈ S.wave.domain, U₀ ∈ HilbertComplex.totalSub
        (ShortHilbertComplex.family3 (⊥ : Submodule ℝ W₀) (tsd Ω) (tsd Ω)) ∧
      ∀ T > 0, Evolution.IsStrongSolution S.wave (Icc 0 T) 0
          (fun t => S.toHilbertComplex.waveGroup.S t U₀) ∧
        ∀ U : ℝ → PiLp 2 (ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix)), U 0 = U₀ →
          Evolution.IsStrongSolution S.wave (Icc 0 T) 0 U →
            ∃ t ∈ Icc 0 T, U t ∉ HilbertComplex.totalSub
              (ShortHilbertComplex.family3 (⊥ : Submodule ℝ W₀) (tsd Ω) (tsd Ω)) := by
  obtain ⟨U₀, hD, hK, hall⟩ := tsd_not_propagates hΩ hb hne S hd₁
  exact ⟨U₀, hD, hK, fun T hT =>
    ⟨S.toHilbertComplex.isStrongSolution_waveGroup hD T, hall T hT⟩⟩

/-! ### The magnetic projection hypothesis fails: `P_{L²(TSD)} H(curl) ⊄ H(curl)` -/

/-- `E_t = (2/t) ∇(e^{-t x₁} sin(t x₂) e₃)`: third row `(-2 a_t, 2 p_t, 0)`; curl-free. -/
def gradFld (t : ℝ) : Ix → R3 → ℝ := fun ij =>
  if ij = (2, 0) then (fun x => -(2 * expSin t x))
  else if ij = (2, 1) then (fun x => 2 * expCos t x) else 0

/-- `B_t = sym E_t`. -/
def symFld (t : ℝ) : Ix → R3 → ℝ := fun ij =>
  if ij = (0, 2) ∨ ij = (2, 0) then (fun x => -expSin t x)
  else if ij = (1, 2) ∨ ij = (2, 1) then expCos t else 0

/-- `S_t = skew E_t = E_t - B_t`. -/
def skewFld (t : ℝ) : Ix → R3 → ℝ := fun ij =>
  if ij = (2, 0) then (fun x => -expSin t x) else if ij = (0, 2) then expSin t
  else if ij = (2, 1) then expCos t else if ij = (1, 2) then (fun x => -expCos t x) else 0

theorem curlM_gradFld (t : ℝ) (ij : Ix) (x : R3) : curlM (gradFld t) ij x = 0 := by
  obtain ⟨i, k⟩ := ij
  simp only [curlM, gradFld]
  fin_cases i <;> fin_cases k <;>
    simp [partialDeriv_neg, partialDeriv_const_mul (differentiable_expSin t _),
      partialDeriv_const_mul (differentiable_expCos t _),
      pd_expSin, pd_expCos]

theorem curlM_symFld (t : ℝ) (ij : Ix) (x : R3) : curlM (symFld t) ij x =
    if ij = (0, 0) then -t * expCos t x else if ij = (0, 1) then -t * expSin t x
    else if ij = (1, 0) then -t * expSin t x else if ij = (1, 1) then t * expCos t x else 0 := by
  obtain ⟨i, k⟩ := ij
  simp only [curlM, symFld]
  fin_cases i <;> fin_cases k <;> simp [partialDeriv_neg, pd_expSin, pd_expCos]

theorem div_symFld (t : ℝ) (i : Fin 3) (x : R3) : ∑ j, partialDeriv j (symFld t (i, j)) x = 0 := by
  simp only [symFld, Fin.sum_univ_three]
  fin_cases i <;> simp [partialDeriv_neg, pd_expSin, pd_expCos]

theorem symFld_symm (t : ℝ) (i j : Fin 3) : symFld t (i, j) = symFld t (j, i) := by
  fin_cases i <;> fin_cases j <;> simp [symFld]

theorem symFld_diag (t : ℝ) (i : Fin 3) : symFld t (i, i) = 0 := by
  fin_cases i <;> simp [symFld]

theorem gradFld_eq (t : ℝ) (ij : Ix) (x : R3) :
    gradFld t ij x = symFld t ij x + skewFld t ij x := by
  obtain ⟨i, j⟩ := ij
  fin_cases i <;> fin_cases j <;> simp [gradFld, symFld, skewFld] <;> ring

theorem skewFld_skew (t : ℝ) (i j : Fin 3) (x : R3) :
    skewFld t (j, i) x = -skewFld t (i, j) x := by
  fin_cases i <;> fin_cases j <;> simp [skewFld]

/-- `|E_t|² = 4 e^{-2 t x₁}`. -/
theorem sum_sq_gradFld (t : ℝ) (x : R3) :
    ∑ ij, gradFld t ij x ^ 2 = 4 * Real.exp (-(t * x 0)) ^ 2 := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, gradFld, expSin, expCos]
  simp
  have := Real.sin_sq_add_cos_sq (t * x 1)
  linear_combination 4 * Real.exp (-(t * x 0)) ^ 2 * this

/-- **`|curl B_t|² = (t²/2) |E_t|²`**: `curl B_t` costs one derivative more than `E_t`. -/
theorem sum_sq_curlM_symFld (t : ℝ) (x : R3) :
    ∑ ij, curlM (symFld t) ij x ^ 2 = t ^ 2 / 2 * ∑ ij, gradFld t ij x ^ 2 := by
  rw [sum_sq_gradFld]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, curlM_symFld, expSin, expCos]
  simp
  have := Real.sin_sq_add_cos_sq (t * x 1)
  linear_combination 2 * t ^ 2 * Real.exp (-(t * x 0)) ^ 2 * this

theorem contDiff_gradFld (t : ℝ) (ij : Ix) : ContDiff ℝ ∞ (gradFld t ij) := by
  unfold gradFld
  split_ifs
  exacts [(contDiff_const.mul (contDiff_expSin t)).neg, contDiff_const.mul (contDiff_expCos t),
    contDiff_const]

theorem contDiff_symFld (t : ℝ) (ij : Ix) : ContDiff ℝ ∞ (symFld t ij) := by
  unfold symFld
  split_ifs
  exacts [(contDiff_expSin t).neg, contDiff_expCos t, contDiff_const]

/-- `E_t` as an `L²` field. -/
abbrev gradFldL2 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (t : ℝ) : L2F ℝ Ω Ix :=
  smoothField hΩ hb (gradFld t) fun ij => (contDiff_gradFld t ij).continuous

/-- `B_t` as an `L²` field. -/
abbrev symFldL2 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (t : ℝ) : L2F ℝ Ω Ix :=
  smoothField hΩ hb (symFld t) fun ij => (contDiff_symFld t ij).continuous

/-- `curl B_t` as an `L²` field. -/
abbrev curlSymFldL2 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (t : ℝ) : L2F ℝ Ω Ix :=
  smoothField hΩ hb (curlM (symFld t)) (continuous_curlM fun ij => (contDiff_symFld t ij).of_le
    (by simp))

/-- `P_{L²(TSD)} E_t = B_t`: `E_t - B_t` is skew (`starProjection_smoothField_eq`). -/
theorem starProjection_gradFld (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (t : ℝ) :
    (tsd Ω).starProjection (gradFldL2 hΩ hb t) = symFldL2 hΩ hb t :=
  starProjection_smoothField_eq hΩ hb _ (fun ij => (contDiff_symFld t ij).of_le (by simp))
    (fun i j x _ => by rw [symFld_symm]) (fun x _ => by simp [symFld_diag])
    (fun i x _ => div_symFld t i x) (s := fun _ => 0) continuous_const (fun i j x _ => by
      rw [gradFld_eq, gradFld_eq, skewFld_skew, symFld_symm t j i]
      split_ifs with h
      · subst h; simp [symFld_diag]
      · ring)

theorem norm_sq_gradFld (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) (t : ℝ) :
    0 < ‖gradFldL2 hΩ hb t‖ ^ 2 := by
  rw [norm_sq_smoothField]
  simp only [sum_sq_gradFld]
  have : NeZero (volume.restrict Ω) := ⟨fun h => by
    have := hΩ.measure_pos volume hne
    rw [← Measure.restrict_apply_self, h] at this
    simp at this⟩
  have e : ∀ x : R3, 4 * Real.exp (-(t * x 0)) ^ 2 = Real.exp (Real.log 4 + 2 * -(t * x 0)) := by
    intro x
    rw [Real.exp_add, Real.exp_log (by norm_num), ← Real.exp_nat_mul]
    norm_num
  simp only [e]
  refine integral_exp_pos ?_
  have hc : Continuous fun x : R3 => Real.exp (Real.log 4 + 2 * -(t * x 0)) := by fun_prop
  exact (((hc.locallyIntegrable (μ := volume)).integrableOn_isCompact
    hb.isCompact_closure).mono_set subset_closure)

theorem norm_sq_curlSymFld (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (t : ℝ) :
    ‖curlSymFldL2 hΩ hb t‖ ^ 2 = t ^ 2 / 2 * ‖gradFldL2 hΩ hb t‖ ^ 2 := by
  rw [norm_sq_smoothField, norm_sq_smoothField, ← integral_const_mul]
  simp only [sum_sq_curlM_symFld]

/-- **The magnetic projection hypothesis of Prop 4.17 fails** on every nonempty bounded open `Ω`,
for every short complex with `d₁ ⊆ curl_min`: `P_{L²(TSD)}` does not map `D(d₁†)` into itself.
Otherwise `E ↦ d₁† P E` would be bounded on the graph of `d₁†` (closed graph theorem), but the
curl-free `E_t` have `P E_t = B_t`, `‖d₁† B_t‖ = (t/√2) ‖E_t‖`. [QuennevilleBelair2015], Prop 4.17 -/
theorem not_starProjection_mem_adjoint_domain (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) {W₀ : Type*} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀]
    [CompleteSpace W₀] (S : ShortHilbertComplex ℝ W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))
    (hd₁ : S.d₁ ≤ (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω) :
    ¬ ∀ B ∈ S.d₁†.domain, (tsd Ω).starProjection B ∈ S.d₁†.domain := by
  intro hyp
  obtain ⟨C, hC⟩ := LinearPMap.exists_norm_apply_le_of_mapsTo
    (LinearPMap.adjoint_isClosed S.dense₁) (tsd Ω).starProjection fun x => hyp _ x.2
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 2 * |C| + 1 := ⟨_, rfl⟩
  obtain ⟨hE, hE'⟩ := smoothField_mem_adjoint hΩ hb S hd₁ (Ψ := gradFld t)
    fun ij => (contDiff_gradFld t ij).of_le (by simp)
  obtain ⟨hB, hB'⟩ := smoothField_mem_adjoint hΩ hb S hd₁ (Ψ := symFld t)
    fun ij => (contDiff_symFld t ij).of_le (by simp)
  rw [smoothField_eq_zero hΩ hb _ fun ij x _ => curlM_gradFld t ij x] at hE'
  have h := hC ⟨gradFldL2 hΩ hb t, hE⟩
  rw [show (⟨(tsd Ω).starProjection (gradFldL2 hΩ hb t), hyp _ hE⟩ : S.d₁†.domain) = ⟨_, hB⟩
    from Subtype.ext (starProjection_gradFld hΩ hb t), hB', hE', Prod.norm_def, norm_zero,
    max_eq_left (norm_nonneg _)] at h
  have h1 := norm_sq_curlSymFld hΩ hb t
  have h2 := norm_sq_gradFld hΩ hb hne t
  have hsq : t ^ 2 / 2 * ‖gradFldL2 hΩ hb t‖ ^ 2 ≤ (|C| * ‖gradFldL2 hΩ hb t‖) ^ 2 := by
    rw [← h1]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))) 2
  have : t ^ 2 / 2 ≤ |C| ^ 2 := by
    rw [mul_pow] at hsq
    exact le_of_mul_le_mul_right hsq h2
  rw [ht] at this
  nlinarith [abs_nonneg C]

/-- **`P_{L²(TSD)} H(curl) ⊄ H(curl)`** on every nonempty bounded open `Ω ⊆ ℝ³`, with
`H(curl) = D(curl_max)` (no boundary condition). [QuennevilleBelair2015], Prop 4.17 -/
theorem not_starProjection_mem_curl_maximal (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) :
    ¬ ∀ B ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.maximal Ω).domain,
      (tsd Ω).starProjection B ∈
        ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.maximal Ω).domain := by
  have e := adjoint_gradCurl_d₁ (𝕜 := ℝ) hΩ
  have h := not_starProjection_mem_adjoint_domain hΩ hb hne (gradCurl ℝ hΩ) le_rfl
  rwa [e] at h

/-- **Both parts of the magnetic projection hypothesis fail**, for every short complex with
`d₁ ⊆ curl_min` and every closed `S₁`: `P_{L²(TSD)} D(d₁†) ⊄ D(d₁†)`, and
`P_K D(L) ⊄ D(L)` for `K = {0} × S₁ × L²(TSD)`. Independent of the electric failure
(`exists_projTSD_not_mem_domain`). [QuennevilleBelair2015], Prop 4.17 -/
theorem not_projection_magnetic (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    {W₀ : Type} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] [CompleteSpace W₀]
    (S : ShortHilbertComplex ℝ W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))
    (hd₁ : S.d₁ ≤ (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω) (S₁ : Submodule ℝ (L2F ℝ Ω Ix))
    [S₁.HasOrthogonalProjection] :
    (¬ ∀ B ∈ S.d₁†.domain, (tsd Ω).starProjection B ∈ S.d₁†.domain) ∧
      ¬ ∀ x ∈ S.wave.domain, (HilbertComplex.totalSub
        (ShortHilbertComplex.family3 (⊥ : Submodule ℝ W₀) S₁ (tsd Ω))).starProjection x ∈
          S.wave.domain := by
  refine ⟨not_starProjection_mem_adjoint_domain hΩ hb hne S hd₁, fun hPD => ?_⟩
  refine not_starProjection_mem_adjoint_domain hΩ hb hne S hd₁ fun B hB => ?_
  have hx := ShortHilbertComplex.inj₂_mem_wave_domain (S := S) hB
  have h := ((S.mem_wave_domain).1 (hPD _ hx)).2.2.2
  rwa [HilbertComplex.totalSub_starProjection_apply] at h

/-- **`P_{L²(TSD)}` is unbounded for the `H(curl)` graph norm**, explicitly: for every `C` there is
`t` with `E_t` smooth and curl-free in `H(curl)`, `P E_t = B_t ∈ H(curl)`, and
`‖curl B_t‖ > C ‖E_t‖ = C ‖E_t‖_{H(curl)}`. [QuennevilleBelair2015], Prop 4.17 -/
theorem projection_unbounded (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (C : ℝ) : ∃ t : ℝ, curlM (gradFld t) = 0 ∧
      gradFldL2 hΩ hb t ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.maximal Ω).domain ∧
      symFldL2 hΩ hb t ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.maximal Ω).domain ∧
      (tsd Ω).starProjection (gradFldL2 hΩ hb t) = symFldL2 hΩ hb t ∧
      C * ‖gradFldL2 hΩ hb t‖ < ‖curlSymFldL2 hΩ hb t‖ := by
  set t : ℝ := 2 * |C| + 2
  refine ⟨t, funext fun ij => funext fun x => curlM_gradFld t ij x,
    (smoothField_mem_curl_maximal hΩ hb fun ij => (contDiff_gradFld t ij).of_le (by simp)).1,
    (smoothField_mem_curl_maximal hΩ hb fun ij => (contDiff_symFld t ij).of_le (by simp)).1,
    starProjection_gradFld hΩ hb t, ?_⟩
  set E := gradFldL2 hΩ hb t
  set cB := curlSymFldL2 hΩ hb t
  have h1 : ‖cB‖ ^ 2 = t ^ 2 / 2 * ‖E‖ ^ 2 := norm_sq_curlSymFld hΩ hb t
  have h2 : 0 < ‖E‖ ^ 2 := norm_sq_gradFld hΩ hb hne t
  have hC : C ^ 2 < t ^ 2 / 2 := by
    have := abs_nonneg C
    have := sq_abs C
    nlinarith
  have key : (|C| * ‖E‖) ^ 2 < ‖cB‖ ^ 2 := by
    rw [h1, mul_pow, sq_abs]
    exact mul_lt_mul_of_pos_right hC h2
  calc C * ‖E‖ ≤ |C| * ‖E‖ := mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)
    _ < ‖cB‖ := lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) key

/-- **Bochner form**: on the Bochner space `L²(Ω; ℝ³ˣ³)` (Frobenius norm), with `L²(TSD)` and
`H(curl)` transported through `Feec.Domain.piL2Equiv`, `P_{L²(TSD)} H(curl) ⊄ H(curl)`.
[QuennevilleBelair2015], Prop 4.17 -/
theorem not_starProjection_mem_curl_maximal_bochner (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    ¬ ∀ F : Lp (EuclideanSpace ℝ Ix) 2 (volume.restrict Ω),
      piL2Equiv (volume.restrict Ω) ℝ Ix F ∈
          ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.maximal Ω).domain →
        piL2Equiv (volume.restrict Ω) ℝ Ix (((tsd Ω).map
          ((piL2Equiv (volume.restrict Ω) ℝ Ix).symm.toLinearEquiv :
            L2F ℝ Ω Ix →ₗ[ℝ] Lp (EuclideanSpace ℝ Ix) 2 (volume.restrict Ω))).starProjection F) ∈
          ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.maximal Ω).domain := by
  intro h
  refine not_starProjection_mem_curl_maximal hΩ hb hne fun B hB => ?_
  have := h ((piL2Equiv (volume.restrict Ω) ℝ Ix).symm B) (by simpa using hB)
  rwa [Submodule.starProjection_map_apply, LinearIsometryEquiv.symm_symm,
    LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply] at this

/-! ### The density conjectures of Prop 4.17, decided -/

/-- **The two inferred `L²(TSD)` densities of Prop 4.17, decided** on every nonempty bounded open
`Ω` star-shaped with respect to a ball: `cl (L²(TSD) ∩ H(curl)) = L²(TSD)` holds, while
`cl (L²(TSD) ∩ H̊(curl)) = L²(TSD₀) ≠ L²(TSD)` fails. [QuennevilleBelair2015], Prop 4.17 -/
theorem density_dichotomy (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    {x₀ : R3} {s : ℝ} (hs : 0 < s) (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) :
    (tsd Ω ⊓
      ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.maximal Ω).domain).topologicalClosure =
        tsd Ω ∧
      (tsd Ω ⊓ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain).topologicalClosure =
        tsd₀ Ω hΩ hb ∧
      (tsd Ω ⊓ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain).topologicalClosure ≠
        tsd Ω :=
  ⟨closure_tsd_inf_curl_maximal hΩ hb hs hstar, closure_eq_tsd₀ hΩ hb hs hstar,
    not_dense_tsd_inter hΩ hb hne⟩

/-- **The gap in the proof of Prop 4.17, stated in Lean.** On every nonempty bounded open `Ω`
star-shaped with respect to a ball: the two literal density conjectures (`H̊(curl) ∩ H(div, 0)`
and `H(curl) ∩ H(div, 0)` dense in `H(div, 0)`) hold, and so does the inferred `H(curl)` density
in `L²(TSD)`; the inferred `H̊(curl)` density does not, its closure being `L²(TSD₀)`. So the step
"so that `H̊(curl) ∩ L²(TSD)` is dense in `L²(TSD)`" is an invalid inference. [QuennevilleBelair2015], Prop 4.17 -/
theorem density_gap (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    {x₀ : R3} {s : ℝ} (hs : 0 < s) (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) :
    (∀ B ∈ (gradCurl ℝ hΩ).d₀†.ker, B ∈ closure ((((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal
        Ω).domain : Set (L2F ℝ Ω Ix)) ∩ (gradCurl ℝ hΩ).d₀†.ker)) ∧
      (∀ B ∈ (gradCurl ℝ hΩ).d₀†.ker, B ∈ closure ((((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).maximal
        Ω).domain : Set (L2F ℝ Ω Ix)) ∩ (gradCurl ℝ hΩ).d₀†.ker)) ∧
      (tsd Ω ⊓
        ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.maximal Ω).domain).topologicalClosure =
          tsd Ω ∧
      (tsd Ω ⊓ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain).topologicalClosure =
        tsd₀ Ω hΩ hb ∧
      (tsd Ω ⊓ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain).topologicalClosure ≠
        tsd Ω :=
  ⟨fun _ hB => dense_curl_inter_divFree hΩ hB, fun _ hB => dense_curl_maximal_inter_divFree hΩ hB,
    density_dichotomy hΩ hb hne hs hstar⟩

/-! ### The largest propagating constraint space `K*` is a strict, nonzero subspace of `K` -/

/-- `diag(1, -1, 0) ∉ S₁*`: `S₁* ⊆ L²(TSD₀)` and constants with nonzero mean are not in
`L²(TSD₀)`. -/
theorem constField_diagA_not_mem_invariantCore₁ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) {W₀ : Type} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀]
    [CompleteSpace W₀] (S : ShortHilbertComplex ℝ W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))
    (hd₁ : S.d₁.domain ≤ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain)
    (S₂ : Submodule ℝ (L2F ℝ Ω Ix)) [S₂.HasOrthogonalProjection] :
    constField hΩ hb diagA ∉ S.invariantCore₁ (tsd Ω) S₂ := fun hm =>
  constField_diagA_not_mem_tsd₀ hΩ hb hne (invariantCore₁_le_tsd₀ hΩ hb S hd₁ S₂ hm)

/-- `β ∉ S₂*` (any `S₂`, any complex with `d₁ ⊆ curl_min`): `d₁† β = curl β ∉ L²(TSD₀)`. -/
theorem betaL2_not_mem_invariantCore₂ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) {W₀ : Type} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀]
    [CompleteSpace W₀] (S : ShortHilbertComplex ℝ W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))
    (hd₁ : S.d₁ ≤ (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω) (S₂ : Submodule ℝ (L2F ℝ Ω Ix))
    [S₂.HasOrthogonalProjection] : betaL2 hΩ hb ∉ S.invariantCore₂ (tsd Ω) S₂ := by
  intro hm
  obtain ⟨hβ, hβv⟩ := smoothField_mem_adjoint hΩ hb S hd₁
    (fun ij => (contDiff_betaField ij).of_le (by simp))
  have := adjoint_mem_tsd₀_of_mem_invariantCore₂ hΩ hb S hd₁.1 S₂ ⟨_, hβ⟩ hm
  rw [hβv] at this
  exact curl_betaL2_not_mem_tsd₀ hΩ hb hne this

/-- Constant symmetric trace-free fields are stationary magnetic data: `A ∈ S₂*`. -/
theorem constField_mem_invariantCore₂ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (S₁ : Submodule ℝ (L2F ℝ Ω Ix)) {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ = A)
    (htrA : A.trace = 0) : constField hΩ hb A ∈ (gradCurl ℝ hΩ).invariantCore₂ S₁ (tsd Ω) := by
  obtain ⟨hmem, e⟩ := smoothField_mem_adjoint hΩ hb (gradCurl ℝ hΩ) le_rfl
    (Ψ := fun ij _ => A ij.1 ij.2) (fun ij => contDiff_const)
  refine ShortHilbertComplex.mem_invariantCore₂_of_eq_zero (S := gradCurl ℝ hΩ) ⟨_, hmem⟩
    (constField_mem_tsd hΩ hb hA htrA) ?_
  rw [e]
  exact smoothField_eq_zero hΩ hb _ fun ij x _ => by simp [curlM, partialDeriv]

/-- **Corrected Prop 4.17 on bounded domains** for the grad–curl complex
`H̊¹ → H̊(curl) → L²` and `K = {0} × L²(TSD) × L²(TSD)`, with `K*` the invariant core of `K`
under the wave group (`Feec.ShortHilbertComplex.coreSub`):
1. `K* = {0} × S₁* × S₂*` with `S₁* ⊆ L²(TSD₀)` and `S₂* ⊆ L²(TSD)`;
2. `{0} × S₁* × S₂*` is a reducing subcomplex (projection hypothesis, `d₁ S₁* ⊆ S₂*`,
   `d₁† S₂* ⊆ S₁*`), and the largest one: every closed `S₁', S₂' ⊆ L²(TSD)` whose product reduces
   `L` lies in `(S₁*, S₂*)`;
3. strictness: `diag(1, -1, 0) ∈ L²(TSD) \ S₁*` and `β ∈ L²(TSD) \ S₂*`; `diag(1, -1, 0) ∈ S₂*` is a
   nonzero **stationary** datum;
4. every `U₀ ∈ D(L) ∩ K*` has on every `[0, T]` a classical solution of `U' = L U`, unique among
   strong solutions, staying in `K* ⊆ K`.
The only elements of `K*` exhibited are stationary; whether `K*` contains non-stationary data on
a general bounded domain is open. [QuennevilleBelair2015], Prop 4.17 -/
theorem invariantCore_tsd (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    (gradCurl ℝ hΩ).coreSub (tsd Ω) (tsd Ω) = HilbertComplex.totalSub
        (ShortHilbertComplex.family3 (⊥ : Submodule ℝ (L2F ℝ Ω (Fin 3)))
          ((gradCurl ℝ hΩ).invariantCore₁ (tsd Ω) (tsd Ω))
          ((gradCurl ℝ hΩ).invariantCore₂ (tsd Ω) (tsd Ω))) ∧
      (gradCurl ℝ hΩ).invariantCore₁ (tsd Ω) (tsd Ω) ≤ tsd₀ Ω hΩ hb ∧
      (gradCurl ℝ hΩ).invariantCore₂ (tsd Ω) (tsd Ω) ≤ tsd Ω ∧
      (gradCurl ℝ hΩ).toHilbertComplex.ReducingSubcomplex
        (ShortHilbertComplex.family3 (⊥ : Submodule ℝ (L2F ℝ Ω (Fin 3)))
          ((gradCurl ℝ hΩ).invariantCore₁ (tsd Ω) (tsd Ω))
          ((gradCurl ℝ hΩ).invariantCore₂ (tsd Ω) (tsd Ω))) ∧
      (∀ (S₁' S₂' : Submodule ℝ (L2F ℝ Ω Ix)) [S₁'.HasOrthogonalProjection]
        [S₂'.HasOrthogonalProjection], S₁' ≤ tsd Ω → S₂' ≤ tsd Ω →
        (gradCurl ℝ hΩ).wave.IsReducing (HilbertComplex.totalSub
          (ShortHilbertComplex.family3 (⊥ : Submodule ℝ (L2F ℝ Ω (Fin 3))) S₁' S₂')) →
        S₁' ≤ (gradCurl ℝ hΩ).invariantCore₁ (tsd Ω) (tsd Ω) ∧
          S₂' ≤ (gradCurl ℝ hΩ).invariantCore₂ (tsd Ω) (tsd Ω)) ∧
      constField hΩ hb diagA ∈ tsd Ω ∧
      constField hΩ hb diagA ∉ (gradCurl ℝ hΩ).invariantCore₁ (tsd Ω) (tsd Ω) ∧
      constField hΩ hb diagA ∈ (gradCurl ℝ hΩ).invariantCore₂ (tsd Ω) (tsd Ω) ∧
      constField hΩ hb diagA ≠ 0 ∧
      betaL2 hΩ hb ∈ tsd Ω ∧ betaL2 hΩ hb ∉ (gradCurl ℝ hΩ).invariantCore₂ (tsd Ω) (tsd Ω) ∧
      ∀ U₀ ∈ (gradCurl ℝ hΩ).wave.domain, U₀ ∈ (gradCurl ℝ hΩ).coreSub (tsd Ω) (tsd Ω) →
        ∀ T : ℝ, ∃ U, U 0 = U₀ ∧ Evolution.IsClassicalSolution (gradCurl ℝ hΩ).wave (Icc 0 T) 0 U ∧
          (∀ t ∈ Icc 0 T, U t ∈ (gradCurl ℝ hΩ).coreSub (tsd Ω) (tsd Ω)) ∧
          ∀ V, V 0 = U₀ → Evolution.IsStrongSolution (gradCurl ℝ hΩ).wave (Icc 0 T) 0 V →
            EqOn V U (Icc 0 T) := by
  have hker : tsd Ω ≤ ((gradCurl ℝ hΩ).d₀†).ker := fun B hB => ((mem_tsd_iff_ker hΩ).1 hB).2.2
  refine ⟨ShortHilbertComplex.coreSub_eq,
    invariantCore₁_le_tsd₀ hΩ hb (gradCurl ℝ hΩ) le_rfl (tsd Ω),
    ShortHilbertComplex.invariantCore₂_le,
    ShortHilbertComplex.reducingSubcomplex_coreSub hker,
    fun S₁' S₂' _ _ h₁ h₂ hred => ShortHilbertComplex.le_invariantCore_of_isReducing h₁ h₂ hred,
    constField_mem_tsd hΩ hb diagA_transpose diagA_trace,
    constField_diagA_not_mem_invariantCore₁ hΩ hb hne (gradCurl ℝ hΩ) le_rfl (tsd Ω),
    constField_mem_invariantCore₂ hΩ hb (tsd Ω) diagA_transpose diagA_trace,
    constField_diagA_ne_zero hΩ hb hne, betaL2_mem_tsd hΩ hb,
    betaL2_not_mem_invariantCore₂ hΩ hb hne (gradCurl ℝ hΩ) le_rfl (tsd Ω),
    fun U₀ hU₀ hK T => ShortHilbertComplex.existsUnique_mem_coreSub hU₀ hK 0 T⟩

/-! ### The violation lives in the boundary layer -/

/-- For every strong solution of the Hodge wave equation of the grad–curl complex from TSD data
`(0, 0, B₀)` that is TSD a.e. on `depDomain Ω t` and on the layer `Ω \ depDomain Ω t`, the
electric field `E(t)` lies in `L²(TSD)`. -/
theorem mem_tsd_of_ae_layer (hΩ : IsOpen Ω) {T : ℝ} {U : ℝ → Win Ω}
    (hU : Evolution.IsStrongSolution (gradCurl ℝ hΩ).wave (Icc 0 T) 0 U) (h0 : winσ (U 0) = 0)
    (hE₀ : winE (U 0) ∈ tsd Ω) (hB₀ : winB (U 0) ∈ tsd Ω) {t : ℝ} (ht : t ∈ Icc 0 T)
    (hlayer : ∀ᵐ y ∂volume.restrict (Ω \ depDomain Ω t),
      SymTF (winE (U t)) y ∧ SymTF (winB (U t)) y) : winE (U t) ∈ tsd Ω := by
  have hdep := tsd_depDomain hΩ hU h0 hE₀ hB₀ ht
  have hall : ∀ᵐ y ∂volume.restrict Ω, SymTF (winE (U t)) y ∧ SymTF (winB (U t)) y := by
    have := (ae_restrict_union_iff _ _ _).2 ⟨hdep, hlayer⟩
    rwa [union_sdiff_cancel (depDomain_subset ht.1)] at this
  obtain ⟨-, hdE, -, -⟩ := tsd_cone hΩ hU h0 hE₀ hB₀ (x := 0) (r := 0)
    (fun z hz => absurd hz (not_lt.2 dist_nonneg)) ht
  exact mem_tsd_of_ae_symTF (hall.mono fun y hy => hy.1) (weakDiv_eq_zero_of_mem_ker hΩ hdE)

/-- **The boundary obstruction of the explicit datum `(0, 0, β)` lives in the boundary layer.**
On every nonempty bounded open `Ω ⊆ ℝ³`, `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ)` is TSD, `(0, 0, β) ∈ D(L)`, and
for every `T > 0` the Hodge wave equation of the grad–curl complex has a strong solution on
`[0, T]` (the wave group orbit), unique among strong solutions; it is TSD a.e. on
`depDomain Ω t` for every `t ∈ [0, T]`, but for some `t ∈ [0, T]` it is not a.e. symmetric and
trace-free on the boundary layer `Ω \ depDomain Ω t`. [QuennevilleBelair2015], Prop 4.17 -/
theorem beta_violation_boundary_layer (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) :
    betaL2 hΩ hb ∈ tsd Ω ∧
      ShortHilbertComplex.inj₂ (𝕜 := ℝ) _ _ _ (betaL2 hΩ hb) ∈ (gradCurl ℝ hΩ).wave.domain ∧
      ∀ T > 0, ∃ U : ℝ → Win Ω, U 0 = ShortHilbertComplex.inj₂ (𝕜 := ℝ) _ _ _ (betaL2 hΩ hb) ∧
        Evolution.IsStrongSolution (gradCurl ℝ hΩ).wave (Icc 0 T) 0 U ∧
        (∀ V : ℝ → Win Ω, V 0 = ShortHilbertComplex.inj₂ (𝕜 := ℝ) _ _ _ (betaL2 hΩ hb) →
          Evolution.IsStrongSolution (gradCurl ℝ hΩ).wave (Icc 0 T) 0 V → EqOn V U (Icc 0 T)) ∧
        (∀ t ∈ Icc 0 T, ∀ᵐ y ∂volume.restrict (depDomain Ω t),
          SymTF (winE (U t)) y ∧ SymTF (winB (U t)) y) ∧
        ∃ t ∈ Icc 0 T, ¬ ∀ᵐ y ∂volume.restrict (Ω \ depDomain Ω t),
          SymTF (winE (U t)) y ∧ SymTF (winB (U t)) y := by
  set U₀ := ShortHilbertComplex.inj₂ (𝕜 := ℝ) (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix) (L2F ℝ Ω Ix)
    (betaL2 hΩ hb)
  obtain ⟨hβ, -⟩ := betaL2_mem_adjoint hΩ hb (gradCurl ℝ hΩ) le_rfl
  have hD : U₀ ∈ (gradCurl ℝ hΩ).wave.domain :=
    ShortHilbertComplex.inj₂_mem_wave_domain (S := gradCurl ℝ hΩ) hβ
  have h0 : winσ U₀ = 0 := rfl
  have hE : winE U₀ ∈ tsd Ω := Submodule.zero_mem _
  have hB : winB U₀ ∈ tsd Ω := betaL2_mem_tsd hΩ hb
  refine ⟨betaL2_mem_tsd hΩ hb, hD, fun T hT => ?_⟩
  obtain ⟨hS, huniq, hdep⟩ := existsUnique_tsd_depDomain hΩ hD h0 hE hB T
  set U := fun t => (gradCurl ℝ hΩ).toHilbertComplex.waveGroup.S t U₀
  have hU0 : U 0 = U₀ := by simp [U]
  refine ⟨U, hU0, hS, fun V hV0 hV t ht => huniq V hV0 hV t ht, hdep, ?_⟩
  obtain ⟨t, ht, hnot⟩ := betaL2_not_propagates hΩ hb hne (gradCurl ℝ hΩ) le_rfl hT hS
    (by rw [hU0]; rfl) (by rw [hU0]; rfl)
  exact ⟨t, ht, fun hlayer => hnot (mem_tsd_of_ae_layer hΩ hS (by rw [hU0]; exact h0)
    (by rw [hU0]; exact hE) (by rw [hU0]; exact hB) ht hlayer)⟩

/-- **The boundary obstruction lives in the boundary layer** (existential-datum form): on every
nonempty bounded open `Ω` there is TSD data `(0, 0, B₀) ∈ D(L)` such that for every `T > 0` a strong
solution exists, every strong solution is TSD on `depDomain Ω t` for all `t ∈ [0, T]`, and fails to
be symmetric and trace-free on a non-null part of `Ω \ depDomain Ω t` for some `t ∈ [0, T]`.
[QuennevilleBelair2015], Prop 4.17 -/
theorem violation_boundary_layer (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    ∃ B₀ ∈ tsd Ω, ShortHilbertComplex.inj₂ (𝕜 := ℝ) _ _ _ B₀ ∈ (gradCurl ℝ hΩ).wave.domain ∧
      ∀ T > 0, (∃ U : ℝ → Win Ω, U 0 = ShortHilbertComplex.inj₂ (𝕜 := ℝ) _ _ _ B₀ ∧
          Evolution.IsStrongSolution (gradCurl ℝ hΩ).wave (Icc 0 T) 0 U) ∧
        ∀ U : ℝ → Win Ω, U 0 = ShortHilbertComplex.inj₂ (𝕜 := ℝ) _ _ _ B₀ →
          Evolution.IsStrongSolution (gradCurl ℝ hΩ).wave (Icc 0 T) 0 U →
            (∀ t ∈ Icc 0 T, ∀ᵐ y ∂volume.restrict (depDomain Ω t),
              SymTF (winE (U t)) y ∧ SymTF (winB (U t)) y) ∧
            ∃ t ∈ Icc 0 T, ¬ ∀ᵐ y ∂volume.restrict (Ω \ depDomain Ω t),
              SymTF (winE (U t)) y ∧ SymTF (winB (U t)) y := by
  obtain ⟨hβ, hD, hall⟩ := beta_violation_boundary_layer hΩ hb hne
  refine ⟨_, hβ, hD, fun T hT => ?_⟩
  obtain ⟨U, hU0, hU, huniq, -, -⟩ := hall T hT
  refine ⟨⟨U, hU0, hU⟩, fun V hV0 hV => ?_⟩
  have h0 : winσ (V 0) = 0 := by rw [hV0]; rfl
  have hE : winE (V 0) ∈ tsd Ω := by rw [hV0]; exact Submodule.zero_mem _
  have hB : winB (V 0) ∈ tsd Ω := by rw [hV0]; exact hβ
  refine ⟨fun t ht => tsd_depDomain hΩ hV h0 hE hB ht, ?_⟩
  obtain ⟨t, ht, hnot⟩ := betaL2_not_propagates hΩ hb hne (gradCurl ℝ hΩ) le_rfl hT hV h0
    (by rw [hV0]; rfl)
  exact ⟨t, ht, fun hlayer => hnot (mem_tsd_of_ae_layer hΩ hV h0 hE hB ht hlayer)⟩

end Feec.Counterexamples.BoundedDomainTSD

/-! ### Deprecated names -/

namespace Feec.Models.BoundedDomain

end Feec.Models.BoundedDomain

namespace Feec.EinsteinBianchi

end Feec.EinsteinBianchi
