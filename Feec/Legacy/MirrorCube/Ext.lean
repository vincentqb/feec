module

public import Feec.Legacy.Box.Ident
public import Feec.Legacy.Box.Mirror
public import Feec.Legacy.MirrorCube.Compress

/-!
# Mirror extension of fields on the box `Q = (0, ½)³`

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use. It
keeps only what those modules need and the results that have no home in the general layers
yet; everything else moved there (see `docs/migration/map.tsv`).

For the repair of thesis Prop 4.17 on the box (`Feec.Legacy.MirrorCube.Cube`) the tensorial mirror
parity classes of `Feec.Legacy.Box.Mirror` (`σ_a(R_i x) = s_i(a) σ_a(x)`, `E(R_i x) = D_i E(x) D_i`,
`B(R_i x) = -D_i B(x) D_i`) are identified with `L²(Q)`. This file builds, for a sign vector
`c ∈ {±1}³`, the extension of `L²(Q)` functions to `𝕋³` with parity `c_i` in `x_i`
(`extS`: real valued, `‖ext g‖² = 8 ‖g‖²`, `ext g|_Q = g`, unique among real functions of that
parity), and from it the mirror extensions `Jm ε : L²(Q; ℝ³ˣ³) → L2M` (entry `(a, b)` with
parity `ε s_i(a) s_i(b)`) and `Jv : L²(Q; ℝ³) → L2V` onto the real fields of
`(mirrorM ε).fix`, `mirrorV.fix`. With the projections `P = Re ∘ avg` onto these real parity
fields they form the data `Feec.Legacy.MirrorCube.Compr` of the abstract compression
(`comprM`, `comprV`), and `P` commutes with `grad`, `curl` and `P_TSD`.

## References

* [QuennevilleBelair2015], §4.10
* [Brezis2011], §9.2 (extension by reflection)
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace InnerProductSpace ENNReal ComplexConjugate
open MeasureTheory Set Filter Topology

namespace Feec.Legacy.MirrorCube

open Feec.Legacy.Torus Feec.Legacy.TorusWeak Feec.Legacy.Box Feec.Legacy.BoxIdent UnitAddTorus
open Feec.Legacy.BoundedDomain (R3 Ix IsTest)

attribute [local instance] Feec.Legacy.Torus.instMeasureSpaceUnitAddCircle_feec

/-- The local Haar measure on `ℝ/ℤ` is an additive Haar measure. -/
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The local Haar measure on `ℝ/ℤ` is a probability measure. -/
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## Parity of the reflection average -/

section Avg

theorem reflT_comm (i j : Fin 3) (x : T3) : reflT i (reflT j x) = reflT j (reflT i x) := by
  by_cases hij : i = j
  · subst hij; rfl
  funext l
  by_cases hi : l = i <;> by_cases hj : l = j
  · exact absurd (hi.symm.trans hj) hij
  · simp [reflT, hi, hij]
  · simp [reflT, hj, Ne.symm hij]
  · simp [reflT, hi, hj]

theorem halfC_reflT_self {c : ℝ} (hc : c * c = 1) (i : Fin 3) (g : C(T3, ℂ)) (x : T3) :
    halfC c i g (reflT i x) = c * halfC c i g x := by
  simp only [halfC_apply, reflT_reflT]
  have : (c : ℂ) * c = 1 := by rw [← Complex.ofReal_mul, hc, Complex.ofReal_one]
  linear_combination (-(1 / 2 : ℂ)) * g (reflT i x) * this

theorem halfC_reflT_other {s : ℂ} {i j : Fin 3} (c' : ℝ) {g : C(T3, ℂ)}
    (hg : ∀ y, g (reflT i y) = s * g y) (x : T3) :
    halfC c' j g (reflT i x) = s * halfC c' j g x := by
  simp only [halfC_apply]
  rw [reflT_comm j i, hg, hg]
  ring

/-- **The parity average has parity `c_i` in `x_i`**: `avg_c g (R_i x) = c_i avg_c g (x)`. -/
theorem avgC_reflT {c : Fin 3 → ℝ} (hc : ∀ i, c i * c i = 1) (g : C(T3, ℂ)) (i : Fin 3)
    (x : T3) : avgC c g (reflT i x) = c i * avgC c g x := by
  have h0 : ∀ y, halfC (c 0) 0 g (reflT 0 y) = c 0 * halfC (c 0) 0 g y :=
    halfC_reflT_self (hc 0) 0 g
  have h1 : ∀ y, halfC (c 1) 1 (halfC (c 0) 0 g) (reflT 1 y) =
      c 1 * halfC (c 1) 1 (halfC (c 0) 0 g) y := halfC_reflT_self (hc 1) 1 _
  have h2 : ∀ y, avgC c g (reflT 2 y) = c 2 * avgC c g y := halfC_reflT_self (hc 2) 2 _
  fin_cases i
  · exact halfC_reflT_other _ (halfC_reflT_other _ h0) x
  · exact halfC_reflT_other _ h1 x
  · exact h2 x

theorem avgC_sub (c : Fin 3 → ℝ) (g h : C(T3, ℂ)) :
    avgC c (g - h) = avgC c g - avgC c h := by
  ext x; simp only [avgC, halfC_apply, ContinuousMap.sub_apply]; ring

end Avg

/-! ## Scalar parity extension of test functions -/

section ExtTest

variable (c : Fin 3 → ℝ)

/-- A scalar test function on `Q` as an `L²(Q)` class. -/
def testL2 {Φ : R3 → ℝ} (hΦ : IsTest Qr Φ) : BoundedDomain.L2 Qr := hΦ.memLp.toLp Φ

/-- The parity extension `8 · avg_c (per Φ)` of a test function, as a continuous function. -/
def extC {Φ : R3 → ℝ} (hΦ : IsTest Qr Φ) : C(T3, ℂ) := (8 : ℝ) • avgC c (perC hΦ)

/-- The parity extension of a test function, in `L²(𝕋³)`. -/
def extTest {Φ : R3 → ℝ} (hΦ : IsTest Qr Φ) : L2T := (extC c hΦ).toLp 2 volume ℂ

/-- The parity condition on `L²(𝕋³)`: `f̂(R_i k) = c_i f̂(k)`. -/
def HasPar (f : L2T) : Prop :=
  ∀ i k, mFourierCoeff (f : T3 → ℂ) (Box.refl i k) = c i * mFourierCoeff (f : T3 → ℂ) k

/-- Real-valued functions on `𝕋³`: `f̂(-k) = conj f̂(k)`. -/
def IsRealT (f : L2T) : Prop :=
  ∀ k, mFourierCoeff (f : T3 → ℂ) (-k) = conj (mFourierCoeff (f : T3 → ℂ) k)

theorem continuous_mFourierCoeff (k : Z3) : Continuous fun f : L2T => mFourierCoeff (f : T3 → ℂ) k := by
  have e : (fun f : L2T => mFourierCoeff (f : T3 → ℂ) k) =
      fun f => (mFourierBasis.repr f : Z3 → ℂ) k := funext fun f => (mFourierBasis_repr f k).symm
  rw [e]
  exact (lp.evalCLM ℂ (fun _ : Z3 => ℂ) 2 k).continuous.comp mFourierBasis.repr.continuous

theorem isClosed_hasPar : IsClosed {f : L2T | HasPar c f} := by
  have e : {f : L2T | HasPar c f} = ⋂ i, ⋂ k, {f : L2T | mFourierCoeff (f : T3 → ℂ)
      (Box.refl i k) = c i * mFourierCoeff (f : T3 → ℂ) k} := by
    ext f; simp [HasPar]
  rw [e]
  exact isClosed_iInter fun i => isClosed_iInter fun k =>
    isClosed_eq (continuous_mFourierCoeff _) (continuous_const.mul (continuous_mFourierCoeff _))

theorem isClosed_isRealT : IsClosed {f : L2T | IsRealT f} := by
  have e : {f : L2T | IsRealT f} = ⋂ k, {f : L2T | mFourierCoeff (f : T3 → ℂ) (-k) =
      conj (mFourierCoeff (f : T3 → ℂ) k)} := by
    ext f; simp [IsRealT]
  rw [e]
  exact isClosed_iInter fun k => isClosed_eq (continuous_mFourierCoeff _)
    (Complex.continuous_conj.comp (continuous_mFourierCoeff _))

theorem mFourierCoeff_extTest {Φ : R3 → ℝ} (hΦ : IsTest Qr Φ) (k : Z3) :
    mFourierCoeff (extTest c hΦ : T3 → ℂ) k = mFourierCoeff (extC c hΦ) k :=
  mFourierCoeff_congr_ae
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := (volume : Measure T3)) (extC c hΦ)) k

variable {c}

theorem hasPar_extTest (hc : ∀ i, c i * c i = 1) {Φ : R3 → ℝ} (hΦ : IsTest Qr Φ) :
    HasPar c (extTest c hΦ) := fun i k => by
  rw [mFourierCoeff_extTest, mFourierCoeff_extTest, ← mFourierCoeff_comp_reflT]
  have e : (fun x => extC c hΦ (reflT i x)) = fun x => (c i : ℂ) * extC c hΦ x := by
    funext x
    simp only [extC, ContinuousMap.coe_smul, Pi.smul_apply, Complex.real_smul,
      avgC_reflT hc]
    ring
  rw [e]
  simp only [mFourierCoeff, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x; ring

theorem conj_extC {Φ : R3 → ℝ} (hΦ : IsTest Qr Φ) (x : T3) : conj (extC c hΦ x) = extC c hΦ x := by
  simp only [extC, ContinuousMap.coe_smul, Pi.smul_apply, Complex.real_smul, map_mul,
    Complex.conj_ofReal, conj_avgC _ (conj_perC hΦ)]

theorem isRealT_extTest {Φ : R3 → ℝ} (hΦ : IsTest Qr Φ) : IsRealT (extTest c hΦ) := fun k => by
  rw [mFourierCoeff_extTest, mFourierCoeff_extTest, mFourierCoeff_neg_of_real (conj_extC hΦ)]

/-- **The extension restricts back to the test function.** -/
theorem resQ_extTest {Φ : R3 → ℝ} (hΦ : IsTest Qr Φ) : resQ (extTest c hΦ) = testL2 hΦ := by
  refine Lp.ext ?_
  have h := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := (volume : Measure T3)) (extC c hΦ)
  filter_upwards [coeFn_resQ (extTest c hΦ), ae_Qr_of_ae_boxSet (ae_restrict_of_ae h),
    hΦ.memLp.coeFn_toLp, ae_restrict_mem measurableSet_Qr] with y h1 h2 h3 h4
  rw [h1, testL2, h3]
  rw [extTest, h2]
  simp only [extC, ContinuousMap.coe_smul, Pi.smul_apply, Complex.real_smul]
  rw [avgC_of_mem_boxSet _ (fun x hx => per_eq_zero_of_notMem hΦ hx)
      (proj_mem_boxSet fun i => h4 i (mem_univ i)), perC_apply, per_proj_of_mem h4]
  rw [show ((8 : ℝ) : ℂ) * ((1 / 8 : ℂ) * (Φ y : ℂ)) = ((Φ y : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re]

/-- The imaginary part of a real function restricts to `0`. -/
theorem resQ_I_smul_of_real {f : L2T} (hf : IsRealT f) : resQ ((-Complex.I) • f) = 0 :=
  resQ_I_smul_eq_zero hf

/-- **Norm of a real parity function**: `‖f‖² = 8 ‖f|_Q‖²`. -/
theorem norm_sq_of_hasPar (hc : ∀ i, c i * c i = 1) {f : L2T} (hp : HasPar c f)
    (hr : IsRealT f) : ‖f‖ ^ 2 = 8 * ‖resQ f‖ ^ 2 := by
  have hs : ∀ i, ‖((c i : ℝ) : ℂ)‖ = 1 := fun i => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    rcases mul_self_eq_one_iff.1 (hc i) with h | h <;> simp [h]
  rw [norm_sq_eq_eight hs hp, resQ_I_smul_of_real hr, norm_zero]
  ring

theorem norm_sq_extTest (hc : ∀ i, c i * c i = 1) {Φ : R3 → ℝ} (hΦ : IsTest Qr Φ) :
    ‖extTest c hΦ‖ ^ 2 = 8 * ‖testL2 hΦ‖ ^ 2 := by
  rw [norm_sq_of_hasPar hc (hasPar_extTest hc hΦ) (isRealT_extTest hΦ), resQ_extTest]

theorem extTest_sub {Φ Ψ : R3 → ℝ} (hΦ : IsTest Qr Φ) (hΨ : IsTest Qr Ψ) :
    extTest c (hΦ.sub hΨ) = extTest c hΦ - extTest c hΨ := by
  rw [extTest, extTest, extTest, ← _root_.map_sub]
  congr 1
  rw [extC, extC, extC, perC_sub hΦ hΨ, avgC_sub, smul_sub]

theorem testL2_sub {Φ Ψ : R3 → ℝ} (hΦ : IsTest Qr Φ) (hΨ : IsTest Qr Ψ) :
    testL2 (hΦ.sub hΨ) = testL2 hΦ - testL2 hΨ := by
  refine Lp.ext ?_
  filter_upwards [(hΦ.sub hΨ).memLp.coeFn_toLp, Lp.coeFn_sub (testL2 hΦ) (testL2 hΨ),
    hΦ.memLp.coeFn_toLp, hΨ.memLp.coeFn_toLp] with y h1 h2 h3 h4
  rw [testL2, h1, h2, Pi.sub_apply, testL2, testL2, h3, h4]

theorem dist_extTest (hc : ∀ i, c i * c i = 1) {Φ Ψ : R3 → ℝ} (hΦ : IsTest Qr Φ)
    (hΨ : IsTest Qr Ψ) :
    dist (extTest c hΦ) (extTest c hΨ) = Real.sqrt 8 * dist (testL2 hΦ) (testL2 hΨ) := by
  rw [dist_eq_norm, dist_eq_norm, ← extTest_sub, ← testL2_sub]
  have h := norm_sq_extTest hc (hΦ.sub hΨ)
  rw [← Real.sqrt_sq (norm_nonneg (extTest c _)), h, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (norm_nonneg _)]

/-- Scalar test functions are dense in `L²(Q)`. -/
theorem mem_closure_testL2 (g : BoundedDomain.L2 Qr) :
    g ∈ closure {g' | ∃ Φ : R3 → ℝ, ∃ hΦ : IsTest Qr Φ, testL2 hΦ = g'} := by
  set B : BoundedDomain.L2M Qr := WithLp.toLp 2 fun p => if p = (0, 0) then g else 0
  have hB := mem_closure_testFields B
  have hc : Continuous fun B : BoundedDomain.L2M Qr => B (0, 0) :=
    BoundedDomain.continuous_component (0, 0)
  have h := map_mem_closure hc hB (t := {g' | ∃ Φ : R3 → ℝ, ∃ hΦ : IsTest Qr Φ, testL2 hΦ = g'})
    (by
      rintro _ ⟨Φ, hΦ, rfl⟩
      exact ⟨Φ (0, 0), hΦ (0, 0), rfl⟩)
  simpa [B] using h

end ExtTest

/-! ## The extension of `L²(Q)` functions -/

section ExtS

variable {c : Fin 3 → ℝ}

theorem mFourierCoeff_add' (f g : L2T) (k : Z3) :
    mFourierCoeff ((f + g : L2T) : T3 → ℂ) k =
      mFourierCoeff (f : T3 → ℂ) k + mFourierCoeff (g : T3 → ℂ) k := by
  rw [← mFourierBasis_repr, ← mFourierBasis_repr, ← mFourierBasis_repr, _root_.map_add]; rfl

theorem mFourierCoeff_sub' (f g : L2T) (k : Z3) :
    mFourierCoeff ((f - g : L2T) : T3 → ℂ) k =
      mFourierCoeff (f : T3 → ℂ) k - mFourierCoeff (g : T3 → ℂ) k := by
  rw [← mFourierBasis_repr, ← mFourierBasis_repr, ← mFourierBasis_repr, _root_.map_sub]; rfl

theorem mFourierCoeff_smul' (r : ℝ) (f : L2T) (k : Z3) :
    mFourierCoeff ((r • f : L2T) : T3 → ℂ) k = r * mFourierCoeff (f : T3 → ℂ) k := by
  rw [← mFourierBasis_repr, ← mFourierBasis_repr, show (r • f : L2T) = (r : ℂ) • f from rfl,
    _root_.map_smul]; rfl

theorem HasPar.sub {f g : L2T} (hf : HasPar c f) (hg : HasPar c g) : HasPar c (f - g) :=
  fun i k => by rw [mFourierCoeff_sub', mFourierCoeff_sub', hf, hg]; ring

theorem HasPar.add {f g : L2T} (hf : HasPar c f) (hg : HasPar c g) : HasPar c (f + g) :=
  fun i k => by rw [mFourierCoeff_add', mFourierCoeff_add', hf, hg]; ring

theorem HasPar.smul {f : L2T} (hf : HasPar c f) (r : ℝ) : HasPar c (r • f) :=
  fun i k => by rw [mFourierCoeff_smul', mFourierCoeff_smul', hf]; ring

theorem IsRealT.sub {f g : L2T} (hf : IsRealT f) (hg : IsRealT g) : IsRealT (f - g) :=
  fun k => by rw [mFourierCoeff_sub', mFourierCoeff_sub', hf, hg, map_sub]

theorem IsRealT.add {f g : L2T} (hf : IsRealT f) (hg : IsRealT g) : IsRealT (f + g) :=
  fun k => by rw [mFourierCoeff_add', mFourierCoeff_add', hf, hg, map_add]

theorem IsRealT.smul {f : L2T} (hf : IsRealT f) (r : ℝ) : IsRealT (r • f) :=
  fun k => by rw [mFourierCoeff_smul', mFourierCoeff_smul', hf, map_mul, Complex.conj_ofReal]

variable (hc : ∀ i, c i * c i = 1)
include hc

/-- **A real parity function is determined by its restriction to `Q`.** -/
theorem eq_of_resQ_eq {f g : L2T} (hf : HasPar c f) (hg : HasPar c g) (hrf : IsRealT f)
    (hrg : IsRealT g) (h : resQ f = resQ g) : f = g := by
  have h0 := norm_sq_of_hasPar hc (hf.sub hg) (hrf.sub hrg)
  rw [_root_.map_sub, h, sub_self, norm_zero] at h0
  have : ‖f - g‖ = 0 := by nlinarith [norm_nonneg (f - g)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- **Every `L²(Q)` function has a real extension of parity `c`**, with `‖f‖² = 8 ‖g‖²`. -/
theorem exists_extS (g : BoundedDomain.L2 Qr) :
    ∃ f : L2T, HasPar c f ∧ IsRealT f ∧ resQ f = g ∧ ‖f‖ ^ 2 = 8 * ‖g‖ ^ 2 := by
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 (mem_closure_testL2 g)
  choose Φ hΦ hu' using hu
  set e : ℕ → L2T := fun n => extTest c (hΦ n)
  have he : CauchySeq e := cauchySeq_of_dist_le (Real.sqrt_nonneg 8) hlim.cauchySeq
    fun n m => by rw [dist_extTest hc, hu', hu']
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete he
  refine ⟨f, (isClosed_hasPar c).mem_of_tendsto hf
      (Eventually.of_forall fun n => hasPar_extTest hc (hΦ n)),
    isClosed_isRealT.mem_of_tendsto hf (Eventually.of_forall fun n => isRealT_extTest (hΦ n)),
    ?_, ?_⟩
  · refine tendsto_nhds_unique ((resQ.continuous.tendsto _).comp hf) (hlim.congr fun n => ?_)
    simp only [Function.comp_apply, e, resQ_extTest, hu']
  · refine tendsto_nhds_unique (((continuous_norm.pow 2).tendsto _).comp hf) ?_
    refine (((continuous_norm.pow 2).const_mul 8).tendsto _).comp hlim |>.congr fun n => ?_
    change 8 * ‖u n‖ ^ 2 = ‖e n‖ ^ 2
    rw [norm_sq_extTest hc, hu']

/-- The extension, as a function. -/
def extSf (g : BoundedDomain.L2 Qr) : L2T := (exists_extS hc g).choose

theorem hasPar_extSf (g : BoundedDomain.L2 Qr) : HasPar c (extSf hc g) :=
  (exists_extS hc g).choose_spec.1

theorem isRealT_extSf (g : BoundedDomain.L2 Qr) : IsRealT (extSf hc g) :=
  (exists_extS hc g).choose_spec.2.1

theorem resQ_extSf (g : BoundedDomain.L2 Qr) : resQ (extSf hc g) = g :=
  (exists_extS hc g).choose_spec.2.2.1

theorem norm_sq_extSf (g : BoundedDomain.L2 Qr) : ‖extSf hc g‖ ^ 2 = 8 * ‖g‖ ^ 2 :=
  (exists_extS hc g).choose_spec.2.2.2

theorem extSf_resQ {f : L2T} (hf : HasPar c f) (hr : IsRealT f) : extSf hc (resQ f) = f :=
  eq_of_resQ_eq hc (hasPar_extSf hc _) hf (isRealT_extSf hc _) hr (resQ_extSf hc _)

/-- **The parity extension** `L²(Q) → L²(𝕋³)` with parity `c_i` in `x_i`. -/
def extS : BoundedDomain.L2 Qr →L[ℝ] L2T :=
  LinearMap.mkContinuous
    { toFun := extSf hc
      map_add' := fun g h => eq_of_resQ_eq hc (hasPar_extSf hc _)
        ((hasPar_extSf hc g).add (hasPar_extSf hc h)) (isRealT_extSf hc _)
        ((isRealT_extSf hc g).add (isRealT_extSf hc h))
        (by rw [_root_.map_add, resQ_extSf, resQ_extSf, resQ_extSf])
      map_smul' := fun r g => eq_of_resQ_eq hc (hasPar_extSf hc _)
        ((hasPar_extSf hc g).smul r) (isRealT_extSf hc _) ((isRealT_extSf hc g).smul r)
        (by rw [RingHom.id_apply, _root_.map_smul, resQ_extSf, resQ_extSf]) }
    (Real.sqrt 8) fun g => by
      refine le_of_eq ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [← Real.sqrt_sq (norm_nonneg (extSf hc g)), norm_sq_extSf, Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (norm_nonneg _)]

theorem extS_apply (g : BoundedDomain.L2 Qr) : extS hc g = extSf hc g := rfl

theorem hasPar_extS (g : BoundedDomain.L2 Qr) : HasPar c (extS hc g) := hasPar_extSf hc g

theorem isRealT_extS (g : BoundedDomain.L2 Qr) : IsRealT (extS hc g) := isRealT_extSf hc g

theorem resQ_extS (g : BoundedDomain.L2 Qr) : resQ (extS hc g) = g := resQ_extSf hc g

theorem extS_resQ {f : L2T} (hf : HasPar c f) (hr : IsRealT f) : extS hc (resQ f) = f :=
  extSf_resQ hc hf hr

theorem norm_sq_extS (g : BoundedDomain.L2 Qr) : ‖extS hc g‖ ^ 2 = 8 * ‖g‖ ^ 2 :=
  norm_sq_extSf hc g

/-- **The extension multiplies inner products by `8`.** -/
theorem inner_extS (g h : BoundedDomain.L2 Qr) : ⟪extS hc g, extS hc h⟫_ℝ = 8 * ⟪g, h⟫_ℝ := by
  have key : ∀ u : BoundedDomain.L2 Qr, ‖extS hc u‖ ^ 2 = 8 * ‖u‖ ^ 2 := norm_sq_extS hc
  have e1 := key (g + h)
  rw [_root_.map_add, norm_add_sq_real, norm_add_sq_real, key, key] at e1
  linarith

end ExtS

/-! ## Mirror extension of matrix and vector fields -/

section Mirror

/-- The parity of the entry `(a, b)` of a mirror tensor (`ε = 1`) or pseudo-tensor (`ε = -1`)
in `x_i`: `ε s_i(a) s_i(b)`. -/
def cM (ε : ℝ) (p : Ix) : Fin 3 → ℝ := fun i => ε * sgn i p.1 * sgn i p.2

theorem cM_sq {ε : ℝ} (hε : ε * ε = 1) (p : Ix) (i : Fin 3) : cM ε p i * cM ε p i = 1 := by
  have h1 := sgn_mul_self i p.1; have h2 := sgn_mul_self i p.2
  simp only [cM]
  linear_combination (sgn i p.1 * sgn i p.1 * (sgn i p.2 * sgn i p.2)) * hε +
    (sgn i p.2 * sgn i p.2) * h1 + h2

/-- The parity of the component `a` of a mirror vector in `x_i`: `s_i(a)`. -/
def cV (a : Fin 3) : Fin 3 → ℝ := fun i => sgn i a

theorem cV_sq (a i : Fin 3) : cV a i * cV a i = 1 := sgn_mul_self i a

/-- The entrywise extension, before the Fourier transform. -/
def extMpi (ε : ℝ) (hε : ε * ε = 1) (B : BoundedDomain.L2M Qr) : MField :=
  WithLp.toLp 2 fun p => extS (cM_sq hε p) (B p)

theorem norm_sq_extMpi (ε : ℝ) (hε : ε * ε = 1) (B : BoundedDomain.L2M Qr) :
    ‖extMpi ε hε B‖ ^ 2 = 8 * ‖B‖ ^ 2 := by
  rw [extMpi, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact norm_sq_extS (cM_sq hε p) (B p)

/-- **The mirror extension of matrix fields** `L²(Q; ℝ³ˣ³) → L2M`: the entry `(a, b)` extended
with parity `ε s_i(a) s_i(b)` in `x_i`. -/
def Jm (ε : ℝ) (hε : ε * ε = 1) : BoundedDomain.L2M Qr →L[ℝ] L2M :=
  LinearMap.mkContinuous
    { toFun := fun B => matrixFourier (extMpi ε hε B)
      map_add' := fun B B' => by
        rw [← _root_.map_add]; congr 1
        ext p; simp [extMpi]
      map_smul' := fun r B => by
        rw [RingHom.id_apply, show r • matrixFourier (extMpi ε hε B) =
          matrixFourier ((r : ℂ) • extMpi ε hε B) by rw [_root_.map_smul]; rfl]
        congr 1
        ext p; simp [extMpi]; rfl }
    (Real.sqrt 8) fun B => by
      refine le_of_eq ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearIsometryEquiv.norm_map]
      rw [← Real.sqrt_sq (norm_nonneg (extMpi ε hε B)), norm_sq_extMpi,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _)]

theorem Jm_apply' (ε : ℝ) (hε : ε * ε = 1) (B : BoundedDomain.L2M Qr) :
    Jm ε hε B = matrixFourier (extMpi ε hε B) := rfl

theorem matrixFourier_symm_Jm (ε : ℝ) (hε : ε * ε = 1) (B : BoundedDomain.L2M Qr) (p : Ix) :
    ofCoeff (entry p (Jm ε hε B)) = extS (cM_sq hε p) (B p) := by
  rw [← matrixFourier_symm_apply, Jm_apply', LinearIsometryEquiv.symm_apply_apply]; rfl

theorem Jm_coeff (ε : ℝ) (hε : ε * ε = 1) (B : BoundedDomain.L2M Qr) (k : Z3) (p : Ix) :
    Jm ε hε B k p = mFourierCoeff (extS (cM_sq hε p) (B p) : T3 → ℂ) k := by
  rw [← matrixFourier_symm_Jm, mFourierCoeff_ofCoeff_entry]

theorem resB_Jm (ε : ℝ) (hε : ε * ε = 1) (B : BoundedDomain.L2M Qr) : resB (Jm ε hε B) = B := by
  ext1 p
  rw [resB_apply, matrixFourier_symm_Jm, resQ_extS]

theorem Jm_mem_fix (ε : ℝ) (hε : ε * ε = 1) (B : BoundedDomain.L2M Qr) :
    Jm ε hε B ∈ (mirrorM ε hε).fix := fun i => by
  ext k ⟨a, b⟩
  change matSgn ε i (Jm ε hε B (Box.refl i k)) (a, b) = Jm ε hε B k (a, b)
  rw [matSgn_apply, Jm_coeff, Jm_coeff, hasPar_extS (cM_sq hε (a, b)) _ i k, ← mul_assoc,
    ← Complex.ofReal_mul]
  have := cM_sq hε (a, b) i
  simp only [cM] at this ⊢
  rw [this, Complex.ofReal_one, one_mul]

theorem isRealM_Jm (ε : ℝ) (hε : ε * ε = 1) (B : BoundedDomain.L2M Qr) : IsRealM (Jm ε hε B) :=
  fun k p => by rw [Jm_coeff, Jm_coeff, isRealT_extS]

theorem norm_sq_Jm (ε : ℝ) (hε : ε * ε = 1) (B : BoundedDomain.L2M Qr) :
    ‖Jm ε hε B‖ ^ 2 = 8 * ‖B‖ ^ 2 := by
  rw [Jm_apply', LinearIsometryEquiv.norm_map, norm_sq_extMpi]

theorem inner_Jm (ε : ℝ) (hε : ε * ε = 1) (B B' : BoundedDomain.L2M Qr) :
    ⟪Jm ε hε B, Jm ε hε B'⟫_ℝ = 8 * ⟪B, B'⟫_ℝ := by
  have e1 := norm_sq_Jm ε hε (B + B')
  rw [_root_.map_add, norm_add_sq_real, norm_add_sq_real, norm_sq_Jm, norm_sq_Jm] at e1
  linarith

/-- Entry parity of a field of the mirror class. -/
theorem coeff_refl_of_mem_fix {ε : ℝ} (hε : ε * ε = 1) {A : L2M} (hA : A ∈ (mirrorM ε hε).fix)
    (i : Fin 3) (k : Z3) (p : Ix) : A (Box.refl i k) p = (cM ε p i : ℂ) * A k p := by
  have h := congrArg (fun B : L2M => B k p) (hA i)
  change matSgn ε i (A (Box.refl i k)) p = A k p at h
  obtain ⟨a, b⟩ := p
  rw [matSgn_apply] at h
  rw [← h, ← mul_assoc, ← Complex.ofReal_mul]
  have := cM_sq hε (a, b) i
  simp only [cM] at this ⊢
  rw [this, Complex.ofReal_one, one_mul]

/-- **A real field of the mirror class is the mirror extension of its restriction.** -/
theorem Jm_resB {ε : ℝ} (hε : ε * ε = 1) {A : L2M} (hA : A ∈ (mirrorM ε hε).fix)
    (hr : IsRealM A) : Jm ε hε (resB A) = A := by
  have hp : ∀ p, extS (cM_sq hε p) (resB A p) = ofCoeff (entry p A) := fun p => by
    rw [resB_apply]
    refine extS_resQ (cM_sq hε p) (fun i k => ?_) (fun k => ?_)
    · rw [mFourierCoeff_ofCoeff_entry, mFourierCoeff_ofCoeff_entry, coeff_refl_of_mem_fix hε hA]
    · rw [mFourierCoeff_ofCoeff_entry, mFourierCoeff_ofCoeff_entry, hr k p]
  rw [Jm_apply']
  have e : extMpi ε hε (resB A) = matrixFourier.symm A := by
    ext1 p
    rw [matrixFourier_symm_apply]
    exact hp p
  rw [e, LinearIsometryEquiv.apply_symm_apply]

/-- The entrywise vector extension, before the Fourier transform. -/
def extVpi (u : BoundedDomain.L2V Qr) : VField :=
  WithLp.toLp 2 fun a => extS (cV_sq a) (u a)

theorem norm_sq_extVpi (u : BoundedDomain.L2V Qr) : ‖extVpi u‖ ^ 2 = 8 * ‖u‖ ^ 2 := by
  rw [extVpi, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact norm_sq_extS (cV_sq a) (u a)

/-- **The mirror extension of vector fields** `L²(Q; ℝ³) → L2V`: the component `a` extended with
parity `s_i(a)` in `x_i` (`σ · n = 0` on the faces). -/
def Jv : BoundedDomain.L2V Qr →L[ℝ] L2V :=
  LinearMap.mkContinuous
    { toFun := fun u => vectorFourier (extVpi u)
      map_add' := fun u u' => by
        rw [← _root_.map_add]; congr 1
        ext a; simp [extVpi]
      map_smul' := fun r u => by
        rw [RingHom.id_apply, show r • vectorFourier (extVpi u) =
          vectorFourier ((r : ℂ) • extVpi u) by rw [_root_.map_smul]; rfl]
        congr 1
        ext a; simp [extVpi]; rfl }
    (Real.sqrt 8) fun u => by
      refine le_of_eq ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearIsometryEquiv.norm_map]
      rw [← Real.sqrt_sq (norm_nonneg (extVpi u)), norm_sq_extVpi,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _)]

theorem Jv_apply' (u : BoundedDomain.L2V Qr) : Jv u = vectorFourier (extVpi u) := rfl

theorem vectorFourier_symm_Jv (u : BoundedDomain.L2V Qr) (a : Fin 3) :
    vectorFourier.symm (Jv u) a = extS (cV_sq a) (u a) := by
  rw [Jv_apply', LinearIsometryEquiv.symm_apply_apply]; rfl

theorem Jv_coeff (u : BoundedDomain.L2V Qr) (k : Z3) (a : Fin 3) :
    Jv u k a = mFourierCoeff (extS (cV_sq a) (u a) : T3 → ℂ) k := by
  rw [← vectorFourier_symm_Jv, vectorFourier_symm_apply, mFourierCoeff_ofCoeff]; rfl

theorem resBV_Jv (u : BoundedDomain.L2V Qr) : resBV (Jv u) = u := by
  ext1 a
  rw [resBV_apply, vectorFourier_symm_Jv, resQ_extS]

theorem Jv_mem_fix (u : BoundedDomain.L2V Qr) : Jv u ∈ mirrorV.fix := fun i => by
  ext k a
  change vecSgn i (Jv u (Box.refl i k)) a = Jv u k a
  rw [vecSgn_apply, Jv_coeff, Jv_coeff, hasPar_extS (cV_sq a) _ i k, ← mul_assoc,
    ← Complex.ofReal_mul]
  have := cV_sq a i
  simp only [cV] at this ⊢
  rw [this, Complex.ofReal_one, one_mul]

theorem isRealV_Jv (u : BoundedDomain.L2V Qr) : IsRealV (Jv u) :=
  fun k a => by rw [Jv_coeff, Jv_coeff, isRealT_extS]

theorem norm_sq_Jv (u : BoundedDomain.L2V Qr) : ‖Jv u‖ ^ 2 = 8 * ‖u‖ ^ 2 := by
  rw [Jv_apply', LinearIsometryEquiv.norm_map, norm_sq_extVpi]

theorem inner_Jv (u u' : BoundedDomain.L2V Qr) : ⟪Jv u, Jv u'⟫_ℝ = 8 * ⟪u, u'⟫_ℝ := by
  have e1 := norm_sq_Jv (u + u')
  rw [_root_.map_add, norm_add_sq_real, norm_add_sq_real, norm_sq_Jv, norm_sq_Jv] at e1
  linarith

theorem coeffV_refl_of_mem_fix {σ : L2V} (hσ : σ ∈ mirrorV.fix) (i : Fin 3) (k : Z3)
    (a : Fin 3) : σ (Box.refl i k) a = (cV a i : ℂ) * σ k a := by
  have h := congrArg (fun ρ : L2V => ρ k a) (hσ i)
  change vecSgn i (σ (Box.refl i k)) a = σ k a at h
  rw [vecSgn_apply] at h
  rw [← h, ← mul_assoc, ← Complex.ofReal_mul]
  have := cV_sq a i
  simp only [cV] at this ⊢
  rw [this, Complex.ofReal_one, one_mul]

/-- **A real field of the vector mirror class is the mirror extension of its restriction.** -/
theorem Jv_resBV {σ : L2V} (hσ : σ ∈ mirrorV.fix) (hr : IsRealV σ) : Jv (resBV σ) = σ := by
  have hp : ∀ a, extS (cV_sq a) (resBV σ a) = vectorFourier.symm σ a := fun a => by
    rw [resBV_apply]
    refine extS_resQ (cV_sq a) (fun i k => ?_) (fun k => ?_)
    · rw [vectorFourier_symm_apply, mFourierCoeff_ofCoeff, mFourierCoeff_ofCoeff]
      exact coeffV_refl_of_mem_fix hσ i k a
    · rw [vectorFourier_symm_apply, mFourierCoeff_ofCoeff, mFourierCoeff_ofCoeff]
      exact hr k a
  rw [Jv_apply']
  have e : extVpi (resBV σ) = vectorFourier.symm σ := by
    ext1 a
    exact hp a
  rw [e, LinearIsometryEquiv.apply_symm_apply]

end Mirror

/-! ## The projections onto the real mirror fields -/

section Proj

/-- Operators commuting with a partial map: `U D(T) ⊆ D(T)`, `T U = U' T`. -/
def CommOp {W V : Type*} [AddCommGroup W] [Module ℝ W] [AddCommGroup V] [Module ℝ V]
    (T : W →ₗ.[ℝ] V) (U : W →ₗ[ℝ] W) (U' : V →ₗ[ℝ] V) : Prop :=
  ∀ z : T.domain, ∃ h : U z ∈ T.domain, T ⟨_, h⟩ = U' (T z)

section CommOp

variable {W V : Type*} [AddCommGroup W] [Module ℝ W] [AddCommGroup V] [Module ℝ V]
  {T : W →ₗ.[ℝ] V}

theorem CommOp.comp {U1 U2 : W →ₗ[ℝ] W} {U1' U2' : V →ₗ[ℝ] V} (h1 : CommOp T U1 U1')
    (h2 : CommOp T U2 U2') : CommOp T (U1 ∘ₗ U2) (U1' ∘ₗ U2') := fun z => by
  obtain ⟨a, ea⟩ := h2 z
  obtain ⟨b, eb⟩ := h1 ⟨_, a⟩
  refine ⟨b, ?_⟩
  exact eb.trans (congrArg U1' ea)

theorem CommOp.half {U : W →ₗ[ℝ] W} {U' : V →ₗ[ℝ] V} (h : CommOp T U U') :
    CommOp T ((1 / 2 : ℝ) • (LinearMap.id + U)) ((1 / 2 : ℝ) • (LinearMap.id + U')) :=
  fun z => by
    obtain ⟨a, ea⟩ := h z
    have hm : (1 / 2 : ℝ) • ((z : W) + U z) ∈ T.domain :=
      T.domain.smul_mem _ (T.domain.add_mem z.2 a)
    refine ⟨hm, ?_⟩
    have e : (⟨_, hm⟩ : T.domain) = (1 / 2 : ℝ) • (z + ⟨_, a⟩) := Subtype.ext rfl
    simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply]
    rw [lpmap_congr' T _ hm rfl, e, T.map_smul, T.map_add, ea]

end CommOp

/-- `Re A = (A + conj A)/2` on matrix fields. -/
def reM : L2M →L[ℝ] L2M := (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ L2M + cjM)

/-- `Re σ = (σ + conj σ)/2` on vector fields. -/
def reV : L2V →L[ℝ] L2V := (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ L2V + cjV)

theorem reM_apply (A : L2M) : reM A = (1 / 2 : ℝ) • (A + cjM A) := rfl

theorem reV_apply (σ : L2V) : reV σ = (1 / 2 : ℝ) • (σ + cjV σ) := rfl

theorem inner_reM (A B : L2M) : ⟪reM A, B⟫_ℝ = ⟪A, reM B⟫_ℝ := by
  rw [reM_apply, reM_apply, real_inner_smul_left, real_inner_smul_right, inner_add_left,
    inner_add_right, inner_cjM]

theorem inner_reV (σ ρ : L2V) : ⟪reV σ, ρ⟫_ℝ = ⟪σ, reV ρ⟫_ℝ := by
  rw [reV_apply, reV_apply, real_inner_smul_left, real_inner_smul_right, inner_add_left,
    inner_add_right, inner_cjV]

theorem isRealM_reM (A : L2M) : IsRealM (reM A) := by
  rw [isRealM_iff_cjM, reM_apply, _root_.map_smul, _root_.map_add, cjM_cjM, add_comm]

theorem isRealV_reV (σ : L2V) : IsRealV (reV σ) := by
  rw [isRealV_iff_cjV, reV_apply, _root_.map_smul, _root_.map_add, cjV_cjV, add_comm]

theorem reM_of_real {A : L2M} (h : IsRealM A) : reM A = A := by
  rw [reM_apply, (isRealM_iff_cjM A).1 h, ← two_smul ℝ A, smul_smul]; norm_num

theorem reV_of_real {σ : L2V} (h : IsRealV σ) : reV σ = σ := by
  rw [reV_apply, (isRealV_iff_cjV σ).1 h, ← two_smul ℝ σ, smul_smul]; norm_num

/-- Conjugation commutes with the mirror reflections of matrix fields. -/
theorem cjM_R (ε : ℝ) (hε : ε * ε = 1) (i : Fin 3) (A : L2M) :
    cjM ((mirrorM ε hε).R i A) = (mirrorM ε hε).R i (cjM A) := by
  ext k ⟨a, b⟩
  change conjM (matSgn ε i (A (Box.refl i (-k)))) (a, b) = matSgn ε i (cjM A (Box.refl i k)) (a, b)
  rw [conjM_apply, matSgn_apply, matSgn_apply, cjM_apply, conjM_apply, refl_neg', map_mul,
    Complex.conj_ofReal]

/-- Conjugation commutes with the mirror reflections of vector fields. -/
theorem cjV_R (i : Fin 3) (σ : L2V) : cjV (mirrorV.R i σ) = mirrorV.R i (cjV σ) := by
  ext k a
  change conjVec (vecSgn i (σ (Box.refl i (-k)))) a = vecSgn i (cjV σ (Box.refl i k)) a
  rw [conjVec_apply, vecSgn_apply, vecSgn_apply, cjV_apply, conjVec_apply, refl_neg', map_mul,
    Complex.conj_ofReal]

theorem cjM_avg (ε : ℝ) (hε : ε * ε = 1) (A : L2M) :
    cjM ((mirrorM ε hε).avg A) = (mirrorM ε hε).avg (cjM A) := by
  simp only [Refl3.avg_apply, Refl3.half_apply, _root_.map_smul, _root_.map_add, cjM_R]

theorem cjV_avg (σ : L2V) : cjV (mirrorV.avg σ) = mirrorV.avg (cjV σ) := by
  simp only [Refl3.avg_apply, Refl3.half_apply, _root_.map_smul, _root_.map_add, cjV_R]

theorem reM_avg (ε : ℝ) (hε : ε * ε = 1) (A : L2M) :
    reM ((mirrorM ε hε).avg A) = (mirrorM ε hε).avg (reM A) := by
  rw [reM_apply, reM_apply, _root_.map_smul, _root_.map_add, cjM_avg]

theorem reV_avg (σ : L2V) : reV (mirrorV.avg σ) = mirrorV.avg (reV σ) := by
  rw [reV_apply, reV_apply, _root_.map_smul, _root_.map_add, cjV_avg]

theorem reM_mem_fix (ε : ℝ) (hε : ε * ε = 1) {A : L2M} (hA : A ∈ (mirrorM ε hε).fix) :
    reM A ∈ (mirrorM ε hε).fix := by
  have : cjM A ∈ (mirrorM ε hε).fix := fun i => by rw [← cjM_R, hA i]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hA this)

theorem reV_mem_fix {σ : L2V} (hσ : σ ∈ mirrorV.fix) : reV σ ∈ mirrorV.fix := by
  have : cjV σ ∈ mirrorV.fix := fun i => by rw [← cjV_R, hσ i]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hσ this)

/-- **The projection onto the real fields of the mirror class**, `P = Re ∘ avg`. -/
def Pm (ε : ℝ) (hε : ε * ε = 1) : L2M →L[ℝ] L2M := reM ∘L (mirrorM ε hε).avg

/-- The projection onto the real fields of the vector mirror class. -/
def Pv : L2V →L[ℝ] L2V := reV ∘L mirrorV.avg

theorem Pm_apply (ε : ℝ) (hε : ε * ε = 1) (A : L2M) : Pm ε hε A = reM ((mirrorM ε hε).avg A) :=
  rfl

theorem Pv_apply (σ : L2V) : Pv σ = reV (mirrorV.avg σ) := rfl

theorem inner_Pm (ε : ℝ) (hε : ε * ε = 1) (A B : L2M) :
    ⟪Pm ε hε A, B⟫_ℝ = ⟪A, Pm ε hε B⟫_ℝ := by
  rw [Pm_apply, Pm_apply, inner_reM, (mirrorM ε hε).inner_avg, reM_avg]

theorem inner_Pv (σ ρ : L2V) : ⟪Pv σ, ρ⟫_ℝ = ⟪σ, Pv ρ⟫_ℝ := by
  rw [Pv_apply, Pv_apply, inner_reV, mirrorV.inner_avg, reV_avg]

theorem Pm_mem_fix (ε : ℝ) (hε : ε * ε = 1) (A : L2M) : Pm ε hε A ∈ (mirrorM ε hε).fix :=
  reM_mem_fix ε hε ((mirrorM ε hε).avg_mem A)

theorem Pv_mem_fix (σ : L2V) : Pv σ ∈ mirrorV.fix := reV_mem_fix (mirrorV.avg_mem σ)

/-- **The compression data of the mirror tensor class**: `J = Jm ε`, `R = res_Q`, `P = Pm ε`. -/
def comprM (ε : ℝ) (hε : ε * ε = 1) : Compr 8 (BoundedDomain.L2M Qr) L2M where
  J := Jm ε hε
  R := resB
  P := Pm ε hε
  inner_J := inner_Jm ε hε
  RJ := resB_Jm ε hε
  JRP z := Jm_resB hε (Pm_mem_fix ε hε z) (isRealM_reM _)
  PJ B := by
    rw [Pm_apply, (mirrorM ε hε).avg_of_mem (Jm_mem_fix ε hε B), reM_of_real (isRealM_Jm ε hε B)]
  P_sa := inner_Pm ε hε

/-- **The compression data of the mirror vector class**: `J = Jv`, `R = res_Q`, `P = Pv`. -/
def comprV : Compr 8 (BoundedDomain.L2V Qr) L2V where
  J := Jv
  R := resBV
  P := Pv
  inner_J := inner_Jv
  RJ := resBV_Jv
  JRP z := Jv_resBV (Pv_mem_fix z) (isRealV_reV _)
  PJ u := by rw [Pv_apply, mirrorV.avg_of_mem (Jv_mem_fix u), reV_of_real (isRealV_Jv u)]
  P_sa := inner_Pv

/-- `P` commutes with the periodic gradient. -/
theorem comprComm_grad : ComprComm periodicComplex.d0 comprV (comprM 1 one_mul_one) := by
  have hav : CommOp periodicComplex.d0 (mirrorV.avg : L2V →ₗ[ℝ] L2V)
      ((mirrorM 1 one_mul_one).avg : L2M →ₗ[ℝ] L2M) := fun z => intertwines_grad.avg z
  have hcj : CommOp periodicComplex.d0 (cjV : L2V →ₗ[ℝ] L2V) (cjM : L2M →ₗ[ℝ] L2M) :=
    fun z => cjV_mem_gradT_domain z.2
  exact hcj.half.comp hav

/-- `P` commutes with the periodic curl. -/
theorem comprComm_curl :
    ComprComm periodicComplex.d1 (comprM 1 one_mul_one) (comprM (-1) neg_one_mul_neg_one) := by
  have hav : CommOp periodicComplex.d1 ((mirrorM 1 one_mul_one).avg : L2M →ₗ[ℝ] L2M)
      ((mirrorM (-1) neg_one_mul_neg_one).avg : L2M →ₗ[ℝ] L2M) := fun z => intertwines_curl.avg z
  have hcj : CommOp periodicComplex.d1 (cjM : L2M →ₗ[ℝ] L2M) (cjM : L2M →ₗ[ℝ] L2M) :=
    fun z => cjM_mem_Hcurl z.2
  exact hcj.half.comp hav

/-- Conjugation preserves `L²(TSD)`. -/
theorem cjM_mem_L2TSD {A : L2M} (hA : A ∈ L2TSD) : cjM A ∈ L2TSD := fun k => by
  change conjM (A (-k)) ∈ tsd (freq k)
  have h := hA (-k)
  change A (-k) ∈ tsd (freq (-k)) at h
  rw [freq_neg, tsd_neg] at h
  exact conjM_mem_tsd h

theorem Pm_mem_L2TSD (ε : ℝ) (hε : ε * ε = 1) {A : L2M} (hA : A ∈ L2TSD) :
    Pm ε hε A ∈ L2TSD := by
  have hh : ∀ i, ∀ B ∈ L2TSD, (mirrorM ε hε).half i B ∈ L2TSD := fun i B hB =>
    Submodule.smul_mem _ _ (Submodule.add_mem _ hB (mirrorM_mem_L2TSD ε hε i hB))
  have hav : (mirrorM ε hε).avg A ∈ L2TSD := by
    rw [Refl3.avg_apply]; exact hh 2 _ (hh 1 _ (hh 0 _ hA))
  rw [Pm_apply, reM_apply]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hav (cjM_mem_L2TSD hav))

/-- **`P_TSD` commutes with `P`.** -/
theorem starProjection_Pm (ε : ℝ) (hε : ε * ε = 1) (A : L2M) :
    L2TSD.starProjection ((comprM ε hε).P A) = (comprM ε hε).P (L2TSD.starProjection A) :=
  starProjection_comm_of_selfAdj L2TSD (Pm ε hε) (inner_Pm ε hε)
    (fun _ h => Pm_mem_L2TSD ε hε h) A

end Proj

end Feec.Legacy.MirrorCube
