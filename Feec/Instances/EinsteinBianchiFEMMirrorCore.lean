module

public import Feec.Instances.EinsteinBianchiFEMMirror

/-!
# The core and the rate classes of the mirror scheme (6.5)

For the approximating FEEC discretization `mirrorFEMApprox` of the mirror scheme (6.5)
(`Feec.Instances.EinsteinBianchiFEMMirror`):

* **the core** `mirrorFEMCore`: the TSD data of `D(L²)`, with the orbit comparison
  (`Feec.HilbertComplex.ApproxFEEC.orbitCore`); its approximation hypothesis is the
  model convergence theorem `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM`, applied to the
  real part `ξ₀` and to the imaginary part `-i ξ₀` of the datum (`mirrorFEM_hconv`); its closure
  is the whole TSD constraint (`mirrorFEMCore_closure`);
* **the rate classes** `mirrorFEMRate` (TSD data of `D(L³)`, order `1`, from
  `mirror_waveFEM_rate_of_mem_domain`) and `mirrorFEMRateSobolev` (TSD data in `H^{2+s}`,
  order `s ≤ 1`, from `mirror_waveFEM_rate_sobolev_of_add_two`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.3 ((6.5))

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology MeasureTheory

@[expose] public noncomputable section

namespace Feec.Instances.EinsteinBianchi.FEM

open Feec.HilbertComplex Feec.Models.Cube.MirrorWeakSymmetry Feec.Models.Cube.RowWise
open Feec.Models.Cube.MirrorBGG (SpaceQ W2Q complexQ tsdQ)
open Feec.Models.Cube.Mirror (MQ VQ)
open Feec.Models.Cube.MirrorSym (RQ)
open Feec.Models.Cube.WeakSymmetry (W0 W1 W2 Wv)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-! ### The error of a TSD state -/

/-- The four-term error of a real forms state `a` against the real part of a state `y`, the
quantity of `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM` (with `σ = M = 0`). -/
def tsdErr (y : PiLp 2 SpaceQ) (a : REnergy) : ℝ :=
  √(‖a.σ‖ ^ 2 + ‖rowsW1L (slot1 y) - a.u‖ ^ 2 + ‖a.M‖ ^ 2 + ‖rowsW2L (slotB y) - a.ρ‖ ^ 2)

theorem tsdErr_nonneg (y : PiLp 2 SpaceQ) (a : REnergy) : 0 ≤ tsdErr y a := Real.sqrt_nonneg _

set_option maxHeartbeats 1000000 in
/-- **The error of a TSD state** `y` against `Rt a + i Rt b`: at most the error of the real part
plus the error of the imaginary part. -/
theorem norm_sub_mirrorReEmb_le {y : PiLp 2 SpaceQ} (hy : y ∈ totalSub tsdQ) (a b : REnergy) :
    ‖y - mirrorReEmb a - Complex.I • mirrorReEmb b‖ ≤ tsdErr y a + tsdErr (-Complex.I • y) b := by
  obtain ⟨h0, -, hM, -⟩ := Feec.Models.Cube.MirrorBGG.mem_tsdQ_iff.1 hy
  have e0 : slot0 y = 0 := h0
  have eM : slotM y = 0 := hM
  have h := norm_sq_sub_mirrorReEmb y a b
  rw [e0, eM, smul_zero, smul_zero, map_zero, map_zero, zero_sub, zero_sub, zero_sub, zero_sub,
    norm_neg, norm_neg, norm_neg, norm_neg] at h
  have hA : tsdErr y a ^ 2 = ‖a.σ‖ ^ 2 + ‖rowsW1L (slot1 y) - a.u‖ ^ 2 + ‖a.M‖ ^ 2 +
      ‖rowsW2L (slotB y) - a.ρ‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hB : tsdErr (-Complex.I • y) b ^ 2 = ‖b.σ‖ ^ 2 +
      ‖rowsW1L (-Complex.I • slot1 y) - b.u‖ ^ 2 + ‖b.M‖ ^ 2 +
      ‖rowsW2L (-Complex.I • slotB y) - b.ρ‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hsq : ‖y - mirrorReEmb a - Complex.I • mirrorReEmb b‖ ^ 2 ≤
      (tsdErr y a + tsdErr (-Complex.I • y) b) ^ 2 := by
    rw [h, add_sq, hA, hB]
    nlinarith [tsdErr_nonneg y a, tsdErr_nonneg (-Complex.I • y) b]
  exact le_of_pow_le_pow_left₀ two_ne_zero
    (add_nonneg (tsdErr_nonneg _ _) (tsdErr_nonneg _ _)) hsq

set_option maxHeartbeats 1000000 in
/-- **The error of the real part is at most the full error**: for a TSD state `y`,
`tsdErr y a ≤ ‖y - Rt a - i Rt b‖` (the converse of `norm_sub_mirrorReEmb_le`). -/
theorem tsdErr_le_norm_sub_mirrorReEmb {y : PiLp 2 SpaceQ} (hy : y ∈ totalSub tsdQ)
    (a b : REnergy) : tsdErr y a ≤ ‖y - mirrorReEmb a - Complex.I • mirrorReEmb b‖ := by
  obtain ⟨h0, -, hM, -⟩ := Feec.Models.Cube.MirrorBGG.mem_tsdQ_iff.1 hy
  have e0 : slot0 y = 0 := h0
  have eM : slotM y = 0 := hM
  have h := norm_sq_sub_mirrorReEmb y a b
  rw [e0, eM, smul_zero, smul_zero, map_zero, map_zero, zero_sub, zero_sub, zero_sub, zero_sub,
    norm_neg, norm_neg, norm_neg, norm_neg] at h
  have hA : tsdErr y a ^ 2 = ‖a.σ‖ ^ 2 + ‖rowsW1L (slot1 y) - a.u‖ ^ 2 + ‖a.M‖ ^ 2 +
      ‖rowsW2L (slotB y) - a.ρ‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hB : tsdErr (-Complex.I • y) b ^ 2 = ‖b.σ‖ ^ 2 +
      ‖rowsW1L (-Complex.I • slot1 y) - b.u‖ ^ 2 + ‖b.M‖ ^ 2 +
      ‖rowsW2L (-Complex.I • slotB y) - b.ρ‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hsq : tsdErr y a ^ 2 ≤ ‖y - mirrorReEmb a - Complex.I • mirrorReEmb b‖ ^ 2 := by
    rw [h]
    nlinarith [sq_nonneg (tsdErr (-Complex.I • y) b)]
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hsq

theorem tsdErr_le {y : PiLp 2 SpaceQ} {a : REnergy} {δ : ℝ} (h0 : ‖a.σ‖ ≤ δ)
    (h1 : ‖rowsW1L (slot1 y) - a.u‖ ≤ δ) (h2 : ‖a.M‖ ≤ δ) (h3 : ‖rowsW2L (slotB y) - a.ρ‖ ≤ δ) :
    tsdErr y a ≤ 2 * δ := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans h0
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have := pow_le_pow_left₀ (norm_nonneg _) h0 2
  have := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have := pow_le_pow_left₀ (norm_nonneg _) h3 2
  nlinarith

/-! ### TSD data -/

/-- The TSD datum of a TSD state of `D(L²)` of the real mirror complex. -/
def tsdDatumOf {x : PiLp 2 SpaceQ} (hx : x ∈ tsdQℝ ⊓ complexQℝ.wave.domainSq) : TSDDatum where
  U₀ := x
  mem := mem_complexQℝ_domain.1 (LinearPMap.mem_domainSq.1 hx.2).1
  mem₂ := by
    obtain ⟨h1, h2⟩ := LinearPMap.mem_domainSq.1 hx.2
    have e := complexQℝ_wave_apply ⟨x, h1⟩
    exact mem_complexQℝ_domain.1 (e ▸ h2)
  tsd := hx.1

theorem tsdDatumOf_U₀ {x : PiLp 2 SpaceQ} (hx : x ∈ tsdQℝ ⊓ complexQℝ.wave.domainSq) :
    (tsdDatumOf hx).U₀ = x := rfl

theorem neg_I_smul_mem {x : PiLp 2 SpaceQ} (hx : x ∈ tsdQℝ ⊓ complexQℝ.wave.domainSq) :
    -Complex.I • x ∈ tsdQℝ ⊓ complexQℝ.wave.domainSq := by
  obtain ⟨h1, h2⟩ := LinearPMap.mem_domainSq.1 hx.2
  have h1' := mem_complexQℝ_domain.1 h1
  have h2' : complexQ.wave ⟨x, h1'⟩ ∈ complexQ.wave.domain := by
    have e := complexQℝ_wave_apply ⟨x, h1⟩
    exact mem_complexQℝ_domain.1 (e ▸ h2)
  have hs : -Complex.I • x ∈ complexQ.wave.domain := complexQ.wave.domain.smul_mem _ h1'
  have e : complexQ.wave ⟨-Complex.I • x, hs⟩ = -Complex.I • complexQ.wave ⟨x, h1'⟩ :=
    complexQ.wave.map_smul (-Complex.I) ⟨x, h1'⟩
  refine ⟨(totalSub tsdQ).smul_mem (-Complex.I) hx.1, LinearPMap.mem_domainSq.2
    ⟨mem_complexQℝ_domain.2 hs, ?_⟩⟩
  rw [complexQℝ_wave_apply]
  refine mem_complexQℝ_domain.2 ?_
  change complexQ.wave ⟨-Complex.I • x, hs⟩ ∈ _
  rw [e]
  exact complexQ.wave.domain.smul_mem _ h2'

/-! ### Solutions of (6.5) as orbits of the approximating discretization -/

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : Feec.Models.Cube.FEM.ParitySmoothingEstimates 3 ∅
    Feec.FiniteElement.PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3,
    Feec.Models.Cube.FEM.ParitySmoothingEstimates 3 {a} Feec.FiniteElement.PolySeq.lagrangeP2 ρ C)

theorem mirrorSource_zero (N : ℕ) (t : ℝ) : mirrorSource hT hB N 0 t = 0 :=
  ext_inner_right ℝ fun v => by
    rw [inner_mirrorSource, Pi.zero_apply, inner_zero_left, inner_zero_left]

/-- A solution of (6.5) with the (vanishing) projected source as a solution without source. -/
def toSourceFree (N : ℕ) {T : ℝ}
    (s : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T (mirrorSource hT hB N 0)) :
    Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T 0 :=
  s.ofEqOn fun t _ => (mirrorSource_zero hT hB N t).symm

/-- The discrete initial value of a pair of solutions of (6.5) (real and imaginary parts). -/
def pairInit (N : ℕ) {T : ℝ} (hT0 : 0 ≤ T)
    (s s' : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T (mirrorSource hT hB N 0)) :
    (mirrorFEMApprox hT hB).X N :=
  WithLp.toLp 2 (DiscreteSolution.hiddenInit hT0 (toSourceFree hT hB N s),
    DiscreteSolution.hiddenInit hT0 (toSourceFree hT hB N s'))

/-- **The complex discrete solution from a pair of solutions of (6.5)**:
`ι' e^{tL'}(v, v') = Rt(state of s)(t) + i Rt(state of s')(t)`. -/
theorem mirrorFEMApprox_sol_pairInit (N : ℕ) {T : ℝ} (hT0 : 0 ≤ T)
    (s s' : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T (mirrorSource hT hB N 0)) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    (mirrorFEMApprox hT hB).sol N (pairInit hT hB N hT0 s s') t =
      mirrorReEmb (dState hT hB N (toSourceFree hT hB N s) t) +
        mulI (mirrorReEmb (dState hT hB N (toSourceFree hT hB N s') t)) :=
  (mirrorFEMApprox_sol hT hB N _ _ t).trans (congrArg₂ (· + ·)
    (mirrorFEMReal_sol_eq hT hB N hT0 _ ht) (congrArg mulI (mirrorFEMReal_sol_eq hT hB N hT0 _ ht)))

set_option maxHeartbeats 1000000 in
/-- **The error of a pair of solutions of (6.5)** against the TSD solution: at most the error of
the real part plus the error of the imaginary part, each being the quantity of
`mirror_waveFEM` for the data `ξ₀` and `-i ξ₀`. -/
theorem norm_sub_sol_pairInit_le (N : ℕ) {T : ℝ} (hT0 : 0 ≤ T)
    (s s' : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T (mirrorSource hT hB N 0)) {t : ℝ}
    (ht : t ∈ Icc 0 T) {y : PiLp 2 SpaceQ} (hy : y ∈ totalSub tsdQ) :
    ‖y - (mirrorFEMApprox hT hB).sol N (pairInit hT hB N hT0 s s') t‖ ≤
      tsdErr y (dState hT hB N (toSourceFree hT hB N s) t) +
        tsdErr (-Complex.I • y) (dState hT hB N (toSourceFree hT hB N s') t) := by
  rw [mirrorFEMApprox_sol_pairInit hT hB N hT0 s s' ht, mulI_apply, ← sub_sub]
  exact norm_sub_mirrorReEmb_le hy _ _

set_option maxHeartbeats 4000000 in
/-- **The model convergence of the mirror scheme (6.5) for complex TSD data of `D(L²)`**: for every
`T > 0` and `ε > 0`, for all large `N`, the real and imaginary parts of the datum run (6.5) from
their elliptic projections (6.4) (`Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM` for `ξ₀`
and `-i ξ₀`), and the complexified discrete solution is within `ε` of `e^{tL} ξ₀` on `[0, T]`. -/
theorem mirrorFEM_hconv : ∀ x ∈ tsdQℝ ⊓ complexQℝ.wave.domainSq, ∀ T : ℝ, 0 < T →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∃ v : (mirrorFEMApprox hT hB).X N,
      ∀ t ∈ Icc 0 T, ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N v t‖ ≤ ε := by
  intro x hx T hT0 ε hε
  have hδ : 0 < ε / 4 := by positivity
  obtain ⟨hTSD, h1⟩ := mirror_waveFEM hT hB (tsdDatumOf hx) hT0 (tsdDatumOf hx).U_zero
    ((tsdDatumOf hx).isStrongSolution T) hδ
  obtain ⟨-, h2⟩ := mirror_waveFEM hT hB (tsdDatumOf (neg_I_smul_mem hx)) hT0
    (tsdDatumOf (neg_I_smul_mem hx)).U_zero
    ((tsdDatumOf (neg_I_smul_mem hx)).isStrongSolution T) hδ
  filter_upwards [h1, h2] with N hN hN'
  obtain ⟨sh, -, hsh⟩ := hN
  obtain ⟨sh', -, hsh'⟩ := hN'
  refine ⟨pairInit hT hB N hT0.le sh sh', fun t ht => ?_⟩
  have hyU : complexQℝ.waveGroup.S t x = (tsdDatumOf hx).U t := complexQℝ_waveGroup ht.1 x
  have hyU' : (tsdDatumOf (neg_I_smul_mem hx)).U t = -Complex.I • (tsdDatumOf hx).U t :=
    (complexQ.waveGroup.S t).map_smul (-Complex.I) x
  rw [hyU]
  refine (norm_sub_sol_pairInit_le hT hB N hT0.le sh sh' ht (hTSD t ht)).trans ?_
  obtain ⟨a0, a1, a2, a3, -⟩ := hsh t ht
  obtain ⟨b0, b1, b2, b3, -⟩ := hsh' t ht
  rw [hyU'] at b1 b3
  have e1 : tsdErr ((tsdDatumOf hx).U t) (dState hT hB N (toSourceFree hT hB N sh) t) ≤
      2 * (ε / 4) := tsdErr_le a0 a1 a2 a3
  have e2 : tsdErr (-Complex.I • (tsdDatumOf hx).U t)
      (dState hT hB N (toSourceFree hT hB N sh') t) ≤ 2 * (ε / 4) := tsdErr_le b0 b1 b2 b3
  linarith

/-! ### The core -/

/-- **The core of the mirror scheme**: TSD data of `D(L²)`, with the orbit comparison
`e^{tL'} π' ξ₀` (zero consistency defect); the approximation hypothesis is the model convergence
`mirrorFEM_hconv`. -/
def mirrorFEMCore : (mirrorFEMApprox hT hB).Core :=
  ApproxFEEC.orbitCore (mirrorFEMApprox_isOrthogonal hT hB) (tsdQℝ ⊓ complexQℝ.wave.domainSq)
    (mirrorFEM_hconv hT hB)

theorem mirrorFEMCore_data :
    (mirrorFEMCore hT hB).Data = tsdQℝ ⊓ complexQℝ.wave.domainSq := rfl

/-- The TSD data of `D(L²)` are dense in the TSD constraint (`D(L²) ∩ K` is dense in the reducing
`K`). -/
theorem topologicalClosure_tsdQℝ_inf_domainSq :
    (tsdQℝ ⊓ complexQℝ.wave.domainSq).topologicalClosure = tsdQℝ := by
  refine le_antisymm ((tsdQℝ ⊓ complexQℝ.wave.domainSq).topologicalClosure_minimal inf_le_left
    isClosed_totalSub) fun k hk => ?_
  have h := complexQℝ.isSkewAdjoint_wave.subset_closure_domainSq_inf isReducing_tsdQℝ hk
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, inf_comm]
  exact h

/-- **The closure of the core is the TSD constraint.** -/
theorem mirrorFEMCore_closure :
    (mirrorFEMCore hT hB).Data.topologicalClosure = tsdQℝ :=
  topologicalClosure_tsdQℝ_inf_domainSq

set_option maxHeartbeats 4000000 in
/-- **The discrete solutions of `mirrorFEMApprox` are the scheme (6.5)**: from every discrete
initial value `(a, b)`, `ι' e^{tL'}(a, b) = Rt(σₕ, uₕ, Mₕ, ρₕ)(t) + i Rt(σₕ', uₕ', Mₕ', ρₕ')(t)` for
the solutions `s`, `s'` of (6.5) without source with initial states `a`, `b`. -/
theorem mirrorFEMApprox_sol_eq_scheme (N : ℕ) {T : ℝ} (hT0 : 0 < T) (a b : mirrorHidden hT hB N) :
    ∃ s s' : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T 0,
      DiscreteSolution.hiddenInit hT0.le s = a ∧ DiscreteSolution.hiddenInit hT0.le s' = b ∧
      ∀ t ∈ Icc 0 T, (mirrorFEMApprox hT hB).sol N (WithLp.toLp 2 (a, b)) t =
        mirrorReEmb (dState hT hB N s t) + mulI (mirrorReEmb (dState hT hB N s' t)) := by
  obtain ⟨s, hs, -⟩ := exists_discreteSolution_group (mirrorWave_dt0_injective hT hB N)
    (mirrorWave_S0_surjective hT hB N) hT0 a
  obtain ⟨s', hs', -⟩ := exists_discreteSolution_group (mirrorWave_dt0_injective hT hB N)
    (mirrorWave_S0_surjective hT hB N) hT0 b
  subst hs hs'
  exact ⟨s, s', rfl, rfl, fun t ht => (mirrorFEMApprox_sol hT hB N _ _ t).trans
    (congrArg₂ (· + ·) (mirrorFEMReal_sol_eq hT hB N hT0.le s ht)
      (congrArg mulI (mirrorFEMReal_sol_eq hT hB N hT0.le s' ht)))⟩

/-! ### Rates -/

open Feec.Models.Cube.FEM (meshSize meshSize_pos)

theorem LU₀_negI {x : PiLp 2 SpaceQ} (hx : x ∈ tsdQℝ ⊓ complexQℝ.wave.domainSq) :
    (tsdDatumOf (neg_I_smul_mem hx)).LU₀ = -Complex.I • (tsdDatumOf hx).LU₀ :=
  complexQ.wave.map_smul (-Complex.I) ⟨x, (tsdDatumOf hx).mem⟩

theorem LLU₀_negI {x : PiLp 2 SpaceQ} (hx : x ∈ tsdQℝ ⊓ complexQℝ.wave.domainSq) :
    (tsdDatumOf (neg_I_smul_mem hx)).LLU₀ = -Complex.I • (tsdDatumOf hx).LLU₀ := by
  change complexQ.wave ⟨(tsdDatumOf (neg_I_smul_mem hx)).LU₀, _⟩ = _
  have e : (⟨(tsdDatumOf (neg_I_smul_mem hx)).LU₀, (tsdDatumOf (neg_I_smul_mem hx)).mem₂⟩ :
      complexQ.wave.domain) = -Complex.I • ⟨(tsdDatumOf hx).LU₀, (tsdDatumOf hx).mem₂⟩ :=
    Subtype.ext (LU₀_negI hx)
  rw [e]
  exact complexQ.wave.map_smul _ _

/-- The norm `‖ξ₀‖ + ‖Lξ₀‖ + ‖L²ξ₀‖ + ‖L³ξ₀‖` of the `D(L³)` rate class. -/
def l3Norm (D : TSDDatum) (h3 : D.LLU₀ ∈ complexQ.wave.domain) : ℝ :=
  ‖D.U₀‖ + ‖D.LU₀‖ + ‖D.LLU₀‖ + ‖complexQ.wave ⟨D.LLU₀, h3⟩‖

theorem l3Norm_nonneg (D : TSDDatum) (h3 : D.LLU₀ ∈ complexQ.wave.domain) : 0 ≤ l3Norm D h3 := by
  unfold l3Norm; positivity

theorem mem_LLU₀_negI {x : PiLp 2 SpaceQ} (hx : x ∈ tsdQℝ ⊓ complexQℝ.wave.domainSq)
    (h3 : (tsdDatumOf hx).LLU₀ ∈ complexQ.wave.domain) :
    (tsdDatumOf (neg_I_smul_mem hx)).LLU₀ ∈ complexQ.wave.domain := by
  rw [LLU₀_negI hx]; exact complexQ.wave.domain.smul_mem _ h3

theorem l3Norm_negI {x : PiLp 2 SpaceQ} (hx : x ∈ tsdQℝ ⊓ complexQℝ.wave.domainSq)
    (h3 : (tsdDatumOf hx).LLU₀ ∈ complexQ.wave.domain) :
    l3Norm (tsdDatumOf (neg_I_smul_mem hx)) (mem_LLU₀_negI hx h3) = l3Norm (tsdDatumOf hx) h3 := by
  have e : complexQ.wave ⟨(tsdDatumOf (neg_I_smul_mem hx)).LLU₀, mem_LLU₀_negI hx h3⟩ =
      -Complex.I • complexQ.wave ⟨(tsdDatumOf hx).LLU₀, h3⟩ := by
    have e' : (⟨(tsdDatumOf (neg_I_smul_mem hx)).LLU₀, mem_LLU₀_negI hx h3⟩ :
        complexQ.wave.domain) = -Complex.I • ⟨(tsdDatumOf hx).LLU₀, h3⟩ :=
      Subtype.ext (LLU₀_negI hx)
    rw [e']; exact complexQ.wave.map_smul _ _
  have hn : ∀ z : PiLp 2 SpaceQ, ‖-Complex.I • z‖ = ‖z‖ := fun z => by
    rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
  have a : (tsdDatumOf (neg_I_smul_mem hx)).U₀ = -Complex.I • (tsdDatumOf hx).U₀ := rfl
  unfold l3Norm
  rw [e, a, LU₀_negI hx, LLU₀_negI hx, hn, hn, hn, hn]

/-- The TSD data of `D(L³)`. -/
def mirrorL3Data : Set (PiLp 2 SpaceQ) :=
  {x | ∃ hx : x ∈ tsdQℝ ⊓ complexQℝ.wave.domainSq, (tsdDatumOf hx).LLU₀ ∈ complexQ.wave.domain}

open Classical in
/-- The class norm of `mirrorL3Data`: `‖ξ₀‖ + ‖Lξ₀‖ + ‖L²ξ₀‖ + ‖L³ξ₀‖`. -/
def mirrorL3Norm (x : PiLp 2 SpaceQ) : ℝ :=
  if h : x ∈ mirrorL3Data then l3Norm (tsdDatumOf h.choose) h.choose_spec else 0

theorem mirrorL3Norm_of_mem {x : PiLp 2 SpaceQ} (hx : x ∈ tsdQℝ ⊓ complexQℝ.wave.domainSq)
    (h3 : (tsdDatumOf hx).LLU₀ ∈ complexQ.wave.domain) :
    mirrorL3Norm x = l3Norm (tsdDatumOf hx) h3 := by
  have hm : x ∈ mirrorL3Data := ⟨hx, h3⟩
  rw [mirrorL3Norm, dite_eq_left_of_eq_true (eq_true hm)]

/-- The constant of `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_of_mem_domain`. -/
def mirrorRateK : ℝ := (mirror_waveFEM_rate_of_mem_domain hT hB).choose

theorem mirrorRateK_nonneg : 0 ≤ mirrorRateK hT hB :=
  (mirror_waveFEM_rate_of_mem_domain hT hB).choose_spec.1

set_option maxHeartbeats 4000000 in
/-- The model rate (`mirror_waveFEM_rate_of_mem_domain`) for one TSD datum of `D(L³)`. -/
theorem mirrorFEM_rate_datum (N : ℕ) {x : PiLp 2 SpaceQ} (hx : x ∈ tsdQℝ ⊓ complexQℝ.wave.domainSq)
    (h3 : (tsdDatumOf hx).LLU₀ ∈ complexQ.wave.domain) {T : ℝ} (hT0 : 0 < T) :
    ∃ sh : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T (mirrorSource hT hB N 0),
      ∀ t ∈ Icc 0 T, tsdErr ((tsdDatumOf hx).U t) (dState hT hB N (toSourceFree hT hB N sh) t) ≤
        mirrorRateK hT hB * l3Norm (tsdDatumOf hx) h3 * (1 + t) * meshSize N := by
  obtain ⟨sh, -, hsh⟩ := (mirror_waveFEM_rate_of_mem_domain hT hB).choose_spec.2 N
    (tsdDatumOf hx) h3 hT0
    (tsdDatumOf hx).U_zero ((tsdDatumOf hx).isStrongSolution T)
  exact ⟨sh, hsh⟩
set_option maxHeartbeats 4000000 in
/-- **The model rate of the mirror scheme for TSD data of `D(L³)`**
(`mirror_waveFEM_rate_of_mem_domain` for `ξ₀` and `-i ξ₀`): for every `N`, some discrete initial
value gives `‖e^{tL} ξ₀ - ι' e^{tL'} v‖ ≤ 2 K (1 + T) h_N ‖ξ₀‖_{L³}` on `[0, T]`. -/
theorem mirrorFEM_hrate {T : ℝ} (hT0 : 0 < T) :
    ∀ x ∈ mirrorL3Data, ∀ N, ∃ v : (mirrorFEMApprox hT hB).X N, ∀ t ∈ Icc 0 T,
      ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N v t‖ ≤
        2 * mirrorRateK hT hB * (1 + T) * meshSize N ^ (1 : ℝ) * mirrorL3Norm x := by
  rintro x ⟨hx, h3⟩ N
  obtain ⟨sh, hsh⟩ := mirrorFEM_rate_datum hT hB N hx h3 hT0
  obtain ⟨sh', hsh'⟩ := mirrorFEM_rate_datum hT hB N (neg_I_smul_mem hx) (mem_LLU₀_negI hx h3) hT0
  refine ⟨pairInit hT hB N hT0.le sh sh', fun t ht => ?_⟩
  have hyU : complexQℝ.waveGroup.S t x = (tsdDatumOf hx).U t := complexQℝ_waveGroup ht.1 x
  have hyU' : (tsdDatumOf (neg_I_smul_mem hx)).U t = -Complex.I • (tsdDatumOf hx).U t :=
    (complexQ.waveGroup.S t).map_smul (-Complex.I) x
  have hb := norm_sub_sol_pairInit_le hT hB N hT0.le sh sh' ht ((tsdDatumOf hx).U_tsd t)
  have e1 := hsh t ht
  have e2 := hsh' t ht
  rw [hyU', l3Norm_negI hx h3] at e2
  rw [hyU, mirrorL3Norm_of_mem hx h3, Real.rpow_one]
  have hc := l3Norm_nonneg (tsdDatumOf hx) h3
  have hm := (meshSize_pos N).le
  have hK := mirrorRateK_nonneg hT hB
  have h1t : (1 + t) ≤ (1 + T) := by linarith [ht.2]
  have h4 : mirrorRateK hT hB * l3Norm (tsdDatumOf hx) h3 * (1 + t) * meshSize N ≤
      mirrorRateK hT hB * l3Norm (tsdDatumOf hx) h3 * (1 + T) * meshSize N :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1t (mul_nonneg hK hc)) hm
  have h5 : mirrorRateK hT hB * l3Norm (tsdDatumOf hx) h3 * (1 + T) * meshSize N * 2 =
      2 * mirrorRateK hT hB * (1 + T) * meshSize N * l3Norm (tsdDatumOf hx) h3 := by ring
  linarith
/-- **The rate class of order `1`**: TSD data of `D(L³)` with the norm
`‖ξ₀‖ + ‖Lξ₀‖ + ‖L²ξ₀‖ + ‖L³ξ₀‖`, `C = 6 K (1 + T)` and `C' = 0` (orbit comparison). -/
def mirrorFEMRate (T : ℝ) (hT0 : 0 < T) : (mirrorFEMApprox hT hB).RateClass T :=
  ApproxFEEC.orbitRate (mirrorFEMApprox_isOrthogonal hT hB) mirrorL3Data mirrorL3Norm meshSize 1
    (2 * mirrorRateK hT hB * (1 + T)) (mirrorFEM_hrate hT hB hT0)

theorem mirrorFEMRate_data (T : ℝ) (hT0 : 0 < T) :
    (mirrorFEMRate hT hB T hT0).Data = mirrorL3Data := rfl

theorem mirrorFEMRate_α (T : ℝ) (hT0 : 0 < T) : (mirrorFEMRate hT hB T hT0).α = 1 := rfl

theorem mirrorFEMRate_C (T : ℝ) (hT0 : 0 < T) :
    (mirrorFEMRate hT hB T hT0).C = 3 * (2 * mirrorRateK hT hB * (1 + T)) := rfl

theorem mirrorFEMRate_C' (T : ℝ) (hT0 : 0 < T) : (mirrorFEMRate hT hB T hT0).C' = 0 := rfl

theorem mirrorFEMRate_meshSize (T : ℝ) (hT0 : 0 < T) :
    (mirrorFEMRate hT hB T hT0).meshSize = meshSize := rfl

theorem mirrorFEMRate_classNorm (T : ℝ) (hT0 : 0 < T) :
    (mirrorFEMRate hT hB T hT0).classNorm = mirrorL3Norm := rfl

/-! ### Sobolev rates -/

theorem fibreEnergy_smul (c : ℂ) (X : PiLp 2 Feec.Models.Torus.BGG.Space) (m : Fin 3 → ℤ) :
    fibreEnergy (c • X) m = ‖c‖ ^ 2 * fibreEnergy X m := by
  unfold fibreEnergy
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := Measure.ae_count_iff.1 (Lp.coeFn_smul c (X i)) m
  change ‖((c • X i : Feec.Models.Torus.BGG.Space i) : (Fin 3 → ℤ) → _) m‖ ^ 2 = _
  rw [h, Pi.smul_apply, norm_smul, mul_pow]

theorem fibreEnergy_extState_negI (x : PiLp 2 SpaceQ) (m : Fin 3 → ℤ) :
    fibreEnergy (extState (-Complex.I • x)) m = fibreEnergy (extState x) m := by
  rw [extState, map_smul, fibreEnergy_smul, norm_neg, Complex.norm_I, one_pow, one_mul]

theorem memSobState_negI {s : ℝ} {x : PiLp 2 SpaceQ} (h : MemSobState s x) :
    MemSobState s (-Complex.I • x) := by
  unfold MemSobState
  simp only [fibreEnergy_extState_negI]
  exact h

theorem sobState_negI (s : ℝ) (x : PiLp 2 SpaceQ) : sobState s (-Complex.I • x) = sobState s x := by
  unfold sobState
  simp only [fibreEnergy_extState_negI]

/-- The constant of `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM_rate_sobolev_of_add_two`. -/
def mirrorSobK : ℝ := (mirror_waveFEM_rate_sobolev_of_add_two hT hB).choose

theorem mirrorSobK_nonneg : 0 ≤ mirrorSobK hT hB :=
  (mirror_waveFEM_rate_sobolev_of_add_two hT hB).choose_spec.1

set_option maxHeartbeats 4000000 in
/-- The model Sobolev rate (`mirror_waveFEM_rate_sobolev_of_add_two`) for one TSD datum. -/
theorem mirrorFEM_sobolev_datum (N : ℕ) {x : PiLp 2 SpaceQ}
    (hx : x ∈ tsdQℝ ⊓ complexQℝ.wave.domainSq) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (h : MemSobState (2 + s) x) {T : ℝ} (hT0 : 0 < T) :
    ∃ sh : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T (mirrorSource hT hB N 0),
      ∀ t ∈ Icc 0 T, tsdErr ((tsdDatumOf hx).U t) (dState hT hB N (toSourceFree hT hB N sh) t) ≤
        mirrorSobK hT hB * √(sobState (2 + s) x) * (1 + t) * meshSize N ^ s := by
  obtain ⟨sh, -, hsh⟩ := (mirror_waveFEM_rate_sobolev_of_add_two hT hB).choose_spec.2 N
    (tsdDatumOf hx) hs0 hs1 h hT0 (tsdDatumOf hx).U_zero ((tsdDatumOf hx).isStrongSolution T)
  exact ⟨sh, hsh⟩

/-- The TSD data of `D(L²)` whose mirror extension lies in `H^{2+s}`. -/
def mirrorSobData (s : ℝ) : Set (PiLp 2 SpaceQ) :=
  {x | x ∈ tsdQℝ ⊓ complexQℝ.wave.domainSq ∧ MemSobState (2 + s) x}

set_option maxHeartbeats 4000000 in
/-- **The model Sobolev rate of the mirror scheme** (`mirror_waveFEM_rate_sobolev_of_add_two` for
`ξ₀` and `-i ξ₀`): `‖e^{tL} ξ₀ - ι' e^{tL'} v‖ ≤ 2 K (1 + T) h_Nˢ ‖ξ₀‖_{2+s}` on `[0, T]`. -/
theorem mirrorFEM_hrate_sobolev {T s : ℝ} (hT0 : 0 < T) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∀ x ∈ mirrorSobData s, ∀ N, ∃ v : (mirrorFEMApprox hT hB).X N, ∀ t ∈ Icc 0 T,
      ‖complexQℝ.waveGroup.S t x - (mirrorFEMApprox hT hB).sol N v t‖ ≤
        2 * mirrorSobK hT hB * (1 + T) * meshSize N ^ s * √(sobState (2 + s) x) := by
  rintro x ⟨hx, h⟩ N
  obtain ⟨sh, hsh⟩ := mirrorFEM_sobolev_datum hT hB N hx hs0 hs1 h hT0
  obtain ⟨sh', hsh'⟩ := mirrorFEM_sobolev_datum hT hB N (neg_I_smul_mem hx) hs0 hs1
    (memSobState_negI h) hT0
  refine ⟨pairInit hT hB N hT0.le sh sh', fun t ht => ?_⟩
  have hyU : complexQℝ.waveGroup.S t x = (tsdDatumOf hx).U t := complexQℝ_waveGroup ht.1 x
  have hyU' : (tsdDatumOf (neg_I_smul_mem hx)).U t = -Complex.I • (tsdDatumOf hx).U t :=
    (complexQ.waveGroup.S t).map_smul (-Complex.I) x
  have hb := norm_sub_sol_pairInit_le hT hB N hT0.le sh sh' ht ((tsdDatumOf hx).U_tsd t)
  have e1 := hsh t ht
  have e2 := hsh' t ht
  rw [hyU', sobState_negI] at e2
  rw [hyU]
  have hc := Real.sqrt_nonneg (sobState (2 + s) x)
  have hm : 0 ≤ meshSize N ^ s := Real.rpow_nonneg (meshSize_pos N).le s
  have hK := mirrorSobK_nonneg hT hB
  have h1t : (1 + t) ≤ (1 + T) := by linarith [ht.2]
  have h4 : mirrorSobK hT hB * √(sobState (2 + s) x) * (1 + t) * meshSize N ^ s ≤
      mirrorSobK hT hB * √(sobState (2 + s) x) * (1 + T) * meshSize N ^ s :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1t (mul_nonneg hK hc)) hm
  have h5 : mirrorSobK hT hB * √(sobState (2 + s) x) * (1 + T) * meshSize N ^ s * 2 =
      2 * mirrorSobK hT hB * (1 + T) * meshSize N ^ s * √(sobState (2 + s) x) := by ring
  linarith

/-- **The rate class of order `s ∈ [0, 1]`**: TSD data with mirror extension in `H^{2+s}`, norm
`‖ξ₀‖_{2+s}`, `C = 6 K (1 + T)` and `C' = 0`. -/
def mirrorFEMRateSobolev (T s : ℝ) (hT0 : 0 < T) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (mirrorFEMApprox hT hB).RateClass T :=
  ApproxFEEC.orbitRate (mirrorFEMApprox_isOrthogonal hT hB) (mirrorSobData s)
    (fun x => √(sobState (2 + s) x)) meshSize s (2 * mirrorSobK hT hB * (1 + T))
    (mirrorFEM_hrate_sobolev hT hB hT0 hs0 hs1)

theorem mirrorFEMRateSobolev_data (T s : ℝ) (hT0 : 0 < T) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (mirrorFEMRateSobolev hT hB T s hT0 hs0 hs1).Data = mirrorSobData s := rfl

theorem mirrorFEMRateSobolev_α (T s : ℝ) (hT0 : 0 < T) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (mirrorFEMRateSobolev hT hB T s hT0 hs0 hs1).α = s := rfl

theorem mirrorFEMRateSobolev_C' (T s : ℝ) (hT0 : 0 < T) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (mirrorFEMRateSobolev hT hB T s hT0 hs0 hs1).C' = 0 := rfl

end Feec.Instances.EinsteinBianchi.FEM
