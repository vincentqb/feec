module

public import Feec.Models.Box.RowWise
public import Feec.Models.Cube.Mirror
public import Feec.Models.Cube.EigenDense
public import Feec.HilbertComplex.CompressCompact

/-!
# Boxes with tensorial mirror boundary conditions: TSD data propagate

The mirror conditions of `Feec.Models.Cube.Mirror` (`σ · n = 0`, `E_{nτ} = 0` on the faces)
carry over from cubes to every box `B = ∏ (aᵢ, aᵢ + ℓᵢ)` with possibly unequal sides `ℓᵢ > 0`.
The diagonal map `T x = d * (x - a)`, `dᵢ = 1/(2ℓᵢ)`, maps `B` onto `Q = (0, ½)³` and turns
`grad`, `curl` into `grad_d`, `curl_d` (`∂ᵢ ↦ dᵢ ∂ᵢ`, `Feec.Domain.ConstCoeffOp.minimal_pullDiag`).
On the Fourier side this is the anisotropic torus complex `Box.complexD` (frequencies
`ξ_d(n) = d * 2πn`, `Feec.Models.Box.symD`). Every ingredient of the cube argument holds at every
frequency, so nothing else changes:

* the mirror reflections `n ↦ flip_k n`, `v ↦ D_k v`, `E ↦ D_k E D_k`, `B ↦ -D_k B D_k` are fibre
  symmetries of `symD d` (`Box.Mirror.symmetriesD`), because `ξ_d(flip_k n) = D_k ξ_d(n)`
  (`dfreq_flipAt`); their fixed fields are those of the cube (`fixed_actionD`), the range of the
  mirror extensions `Feec.Models.Cube.Mirror.J`;
* the TSD fibres `tsdK i ξ` are a fibre reducing family at every `ξ`
  (`Feec.Fourier.GradCurl.isFibreReducing`), so the anisotropic constraint
  `{0} × L²(TSD_{ξ_d}) × L²(TSD_{ξ_d})` reduces `complexD d` (`reducingSubcomplexD`), and it is
  permuted by the reflections (`fib_mem_tsdKD`).

The mirror complex on `Q` with the weights `d` is the compression `Box.Mirror.complexQD d`; it
is the cube mirror complex `Feec.Models.Cube.Mirror.complexQ` reweighted by the column scalings
`E ↦ E D`, `B ↦ det D · B D⁻¹`, as for the row-wise conditions
(`Feec.Models.Box.complexBox_eq_transport`). The **mirror complex on the box**
`Box.Mirror.complexBoxM a ℓ` is its pull-back along `T`.

## Main results

* **`Box.Mirror.reducingSubcomplexBox`**: TSD reduces the mirror complex on every box;
  `propagatesBox`, `existsUnique_memBox`, **`invariantCore_eqBox`** (`K* = K`, thesis Prop 4.17
  with mirror conditions).
* **`Box.Mirror.eigenDense_complexBoxM`**: a complete set of eigenvectors (the analogue of
  `Feec.Models.Cube.Mirror.eigenDense_complexCube`); also `eigenDense_complexD`,
  `eigenDense_complexQD`.
* **`Box.Mirror.exists_nonstationaryBox`**: the datum `(0, 2 cos(π (x₃ - a₃)/ℓ₃) diag(1, -1, 0), 0)`
  (the pull-back of the cube datum) is TSD, in `D(L)`, and not stationary: the constraint has
  dynamical content.

## Scope

As for cubes (`Feec.Models.Cube.Mirror`), the mirror conditions are not the thesis' row-wise
conditions: with those (`Feec.Models.Box.EigenDense`, `Feec.Counterexamples.BoxStationary`)
only stationary TSD data propagate on boxes. On general bounded `Ω` (balls, Lipschitz domains)
the question for the thesis' complex is **still open**
(`Feec.Models.BoundedDomain.not_coreSub_le_stationary_iff`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (Prop 4.17, (4.14), (4.15))
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.2 (extension by reflection)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set LinearPMap MeasureTheory

@[expose] public noncomputable section

namespace Feec.Models.Box.Mirror

open Feec.Fourier Feec.Fourier.GradCurl Feec.ShortHilbertComplex Feec.Models.Cube.MirrorExt
open Feec.HilbertComplex (ScaledEmbedding totalSub ReducingSubcomplex)
open Feec.Models.Cube.MirrorTorus (sgn sgn_mul_self leviCivita3_sgn)
open Feec.Fourier.Torus (flipAt flipAt_apply)
open Feec.Models.Cube.Mirror (cV cE cB cV_sq cE_sq cB_sq fib
  symmetries action J SpaceQ VQ MQ inner_J eight_pos range_J complexQ k0 M0 M0_apply cosCoeff
  cosCoeff_eq_zero cosE coe_cosE cosE_mem_fixed cosState cosState_zero cosState_one cosState_two
  cosStateQ cosStateQ_zero cosStateQ_one cosStateQ_two totalJ_cosStateQ cosEQ J_cosEQ)
open Feec.Models.Torus.GradCurl (Space)
open Feec.Models.BoundedDomain (R3)
open Feec.Models.Cube.Geometry (Q)

variable {d : R3}

/-! ### The mirror symmetries of the anisotropic torus complex -/

theorem dfreq_flipAt (d : R3) (k : Fin 3) (n : Fin 3 → ℤ) (a : Fin 3) :
    ((dfreq d (flipAt k n) a : ℝ) : ℂ) = sgn k a * (dfreq d n a : ℂ) := by
  simp only [dfreq_apply, flipAt_apply, sgn]
  split_ifs <;> push_cast <;> ring

theorem grad_flipD (d : R3) (k : Fin 3) (n : Fin 3 → ℤ) (v : Vec) :
    grad (dfreq d (flipAt k n)) (sgnCLM (Fin 3) (fun a => cV a k) v) =
      sgnCLM (Fin 3 × Fin 3) (fun p => cE p k) (grad (dfreq d n) v) := by
  ext ⟨a, b⟩
  rw [grad_apply, sgnCLM_apply, sgnCLM_apply, grad_apply, dfreq_flipAt]
  simp only [cV, cE]
  ring

theorem curl_flipD (d : R3) (k : Fin 3) (n : Fin 3 → ℤ) (M : Mat) :
    curl (dfreq d (flipAt k n)) (sgnCLM (Fin 3 × Fin 3) (fun p => cE p k) M) =
      sgnCLM (Fin 3 × Fin 3) (fun p => cB p k) (curl (dfreq d n) M) := by
  ext ⟨a, b⟩
  rw [sgnCLM_apply, curl_apply, curl_apply]
  simp only [sgnCLM_apply, dfreq_flipAt, Finset.mul_sum, cE, cB]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
  linear_combination (Complex.I * sgn k a * (dfreq d n c : ℂ) * M (a, e)) *
    leviCivita3_sgn k b c e

/-- The anisotropic TSD fibres are permuted by the reflections. -/
theorem matR_mem_tsdD (d : R3) (k : Fin 3) (n : Fin 3 → ℤ) {s : Fin 3 × Fin 3 → ℂ}
    (hs : ∀ p, s p = s (p.2, p.1)) (hd : ∀ a, s (a, a) = s (0, 0))
    (hsgn : ∀ p, s p = s (0, 0) * (sgn k p.1 * sgn k p.2)) {M : Mat}
    (hM : M ∈ tsd (dfreq d (flipAt k n))) :
    sgnCLM (Fin 3 × Fin 3) s M ∈ tsd (dfreq d n) := by
  obtain ⟨h1, h2, h3⟩ := mem_tsd.1 hM
  refine mem_tsd.2 ⟨?_, ?_, ?_⟩
  · ext a b
    have := congrFun (congrFun h1 a) b
    simp only [Matrix.transpose_apply, toMatrix_apply] at this ⊢
    rw [sgnCLM_apply, sgnCLM_apply, this, hs (b, a)]
  · have e : (toMatrix (sgnCLM (Fin 3 × Fin 3) s M)).trace = s (0, 0) * (toMatrix M).trace := by
      simp only [Matrix.trace, Matrix.diag, toMatrix_apply, sgnCLM_apply, hd, Finset.mul_sum]
    rw [e, h2, mul_zero]
  · ext a
    have := congrFun h3 a
    simp only [Matrix.mulVec, dotProduct, toMatrix_apply, cfreq, Pi.zero_apply] at this ⊢
    simp only [dfreq_flipAt] at this
    rw [show (∑ b, sgnCLM (Fin 3 × Fin 3) s M (a, b) * (dfreq d n b : ℂ)) =
        s (0, 0) * sgn k a * ∑ b, M (a, b) * (sgn k b * (dfreq d n b : ℂ)) by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [sgnCLM_apply, hsgn]; ring, this, mul_zero]

variable (d) in
/-- **The tensorial reflections of the anisotropic torus grad–curl complex.** -/
def symmetriesD : (symD d).Symmetries (Fin 3) where
  R := flipRefl
  ρ := fib
  invol := symmetries.invol
  inner_ρ := symmetries.inner_ρ
  symm k i j n v := by
    change gradCurl.m i j (dfreq d (flipAt k n)) (fib k i v) =
      fib k j (gradCurl.m i j (dfreq d n) v)
    fin_cases i <;> fin_cases j
    all_goals first
      | (change (0 : _ →L[ℂ] _) _ = fib k _ ((0 : _ →L[ℂ] _) v); simp)
      | exact grad_flipD d k n v
      | exact curl_flipD d k n v
  comm_σ := symmetries.comm_σ
  comm_ρ := symmetries.comm_ρ

variable (d) in
/-- The mirror action of `(ℤ/2)³` on the anisotropic torus complex. -/
abbrev actionD : (complexD d).Action (Multiplicative (Fin 3 → ZMod 2)) := (symmetriesD d).toAction

/-- **The fixed fields do not depend on the frequencies**: they are the mirror parity fields. -/
theorem fixed_actionD (i : Fin 3) : (actionD d).fixed i = action.fixed i := by
  ext x
  exact (symmetriesD d).mem_fixed_toAction.trans Cube.Mirror.mem_fixed_iff.symm

theorem range_JD (i : Fin 3) :
    LinearMap.range (J i : SpaceQ i →ₗ[ℂ] Space i) = (actionD d).fixed i :=
  (range_J i).trans (fixed_actionD i).symm

variable (d) in
/-- The ranges of the mirror extensions reduce the anisotropic torus complex. -/
theorem reducingSubcomplex_rangeD :
    (complexD d).ReducingSubcomplex fun i => LinearMap.range (J i : SpaceQ i →ₗ[ℂ] Space i) := by
  convert (actionD d).reducingSubcomplex_fixed using 1
  exact funext range_JD

/-! ### The anisotropic TSD constraint -/

variable (d) in
/-- **The anisotropic constraint** `{0} × L²(TSD_{ξ_d}) × L²(TSD_{ξ_d})`: fibrewise symmetric,
trace-free, and `M ξ_d(n) = 0`. -/
abbrev constraintD (i : Fin 3) : Submodule ℂ (Space i) :=
  Operator.fibreSub Measure.count fun n => tsdK i (dfreq d n)

variable (d) in
theorem fibreReducingD :
    FibreReducing (symD d) fun i n => tsdK i (dfreq d n) :=
  isFibreReducing.toFibreReducing _ (dfreq d) _ fun _ => AEStronglyMeasurable.of_discrete

instance (i : Fin 3) : (constraintD d i).HasOrthogonalProjection :=
  (fibreReducingD d).hasOrthogonalProjection i

variable (d) in
/-- **The anisotropic TSD constraint reduces the anisotropic torus complex.** -/
theorem reducingSubcomplexD : (complexD d).ReducingSubcomplex (constraintD d) :=
  (fibreReducingD d).toReducingSubcomplex

theorem fib_mem_tsdKD (k i : Fin 3) (n : Fin 3 → ℤ) {v : W3 Vec Mat Mat i}
    (hv : v ∈ tsdK i (dfreq d (flipAt k n))) : fib k i v ∈ tsdK i (dfreq d n) := by
  fin_cases i
  · have h0 : (v : Vec) = 0 := (Submodule.mem_bot ℂ).1 hv
    change sgnCLM (Fin 3) (fun a => cV a k) v ∈ (⊥ : Submodule ℂ Vec)
    have h1 : sgnCLM (Fin 3) (fun a => cV a k) (v : Vec) = 0 := by
      rw [h0]; exact (sgnCLM (Fin 3) fun a => cV a k).map_zero
    rw [h1]
    exact Submodule.zero_mem _
  · exact matR_mem_tsdD d k n (s := fun p => cE p k) (fun p => by simp only [cE]; ring)
      (fun a => by simp only [cE, sgn_mul_self])
      (fun p => by simp only [cE, sgn_mul_self]; ring) hv
  · exact matR_mem_tsdD d k n (s := fun p => cB p k) (fun p => by simp only [cB]; ring)
      (fun a => by simp only [cB, sgn_mul_self])
      (fun p => by simp only [cB, sgn_mul_self]; ring) hv

theorem act_mem_constraintD (g : Multiplicative (Fin 3 → ZMod 2)) (i : Fin 3) {x : Space i}
    (hx : x ∈ constraintD d i) : (actionD d).act g i x ∈ constraintD d i :=
  (symmetriesD d).act_mem_fibreSub (K := fun i n => tsdK i (dfreq d n))
    (fun k i n _ hv => fib_mem_tsdKD k i n hv) g i hx

/-! ### The mirror complex on `Q` with weights `d` -/

variable (d) in
/-- **The weighted mirror complex on `Q`**: `grad_d`, `curl_d` with `σ · n = 0`, `E_{nτ} = 0`,
the compression of the anisotropic torus complex along the mirror extensions. -/
abbrev complexQD : HilbertComplex ℂ ComplexShape.fin3 SpaceQ :=
  (complexD d).compress J eight_pos inner_J (reducingSubcomplex_rangeD d)

variable (d) in
def embeddingQD : ScaledEmbedding (complexQD d) (complexD d) :=
  ScaledEmbedding.ofCompress eight_pos inner_J (reducingSubcomplex_rangeD d)

variable (d) in
/-- The constraint on `Q`: the pull-back of `constraintD d` along the mirror extensions. -/
abbrev tsdQD (i : Fin 3) : Submodule ℂ (SpaceQ i) :=
  (constraintD d i).comap (J i : SpaceQ i →ₗ[ℂ] Space i)

instance (i : Fin 3) : (tsdQD d i).HasOrthogonalProjection :=
  (embeddingQD d).comap_hasOrthogonalProjection i _

theorem exists_J_eq_starProjectionD (i : Fin 3) (x : SpaceQ i) :
    ∃ y, J i y = (constraintD d i).starProjection (J i x) := by
  have hx : J i x ∈ (actionD d).fixed i := range_JD i ▸ LinearMap.mem_range_self _ x
  have h := (actionD d).starProjection_mem_fixed (fun g y hy => act_mem_constraintD g i hy) hx
  rw [← range_JD] at h
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy⟩

variable (d) in
/-- **TSD reduces the weighted mirror complex on `Q`.** -/
theorem reducingSubcomplexQD : (complexQD d).ReducingSubcomplex (tsdQD d) :=
  (embeddingQD d).reducingSubcomplex_comap (reducingSubcomplexD d) exists_J_eq_starProjectionD


/-! ### A non-stationary TSD datum -/

theorem M0_mem_tsdD {n : Fin 3 → ℤ} (hn : n = k0 ∨ n = -k0) : M0 ∈ tsd (dfreq d n) := by
  have h0 : n 0 = 0 ∧ n 1 = 0 := by
    rcases hn with rfl | rfl <;> simp [k0]
  refine mem_tsd.2 ⟨?_, ?_, ?_⟩
  · ext a b
    simp only [Matrix.transpose_apply, toMatrix_apply, M0_apply]
    split_ifs <;> simp_all
  · simp [Matrix.trace, toMatrix_apply, M0_apply, Fin.sum_univ_three]
  · ext a
    simp only [Matrix.mulVec, dotProduct, toMatrix_apply, M0_apply, cfreq, Fin.sum_univ_three,
      Pi.zero_apply]
    fin_cases a <;> simp [dfreq_apply, h0.1, h0.2]

theorem cosE_mem_constraintD : cosE ∈ constraintD d 1 := by
  refine Operator.mem_fibreSub.2 (Measure.ae_count_iff.2 fun n => ?_)
  change (cosE : (Fin 3 → ℤ) → Mat) n ∈ tsd (dfreq d n)
  rw [coe_cosE]
  unfold cosCoeff
  split_ifs with h
  · exact M0_mem_tsdD h
  · exact Submodule.zero_mem _

/-- `curl_{ξ_d(k₀)} M₀ ≠ 0`: its `(0, 1)` entry is `2π i d₂`. -/
theorem curl_M0_neD (hd : ∀ i, 0 < d i) : curl (dfreq d k0) M0 ≠ 0 := by
  intro h
  have := congrArg (fun M : Mat => M (0, 1)) h
  simp only [curl_apply, Fin.sum_univ_three, leviCivita3_apply, M0_apply, dfreq_apply, k0] at this
  norm_num [Real.pi_ne_zero, Complex.I_ne_zero, (hd 2).ne'] at this

theorem cosE_mem_domainD : cosE ∈ ((complexD d).d 1 2).domain :=
  mem_mulDomain_of_finite _ {k0, -k0} fun _ hn => (coe_cosE _).trans (cosCoeff_eq_zero hn)

theorem cosE_mem_adjoint_domainD : cosE ∈ (((complexD d).d 0 1)†).domain := by
  rw [show ((complexD d).d 0 1)† = Operator.mulOp Measure.count fun n =>
      ContinuousLinearMap.adjoint (gradCurl.m 0 1 (dfreq d n)) from (symD d).adjoint_d 0 1]
  exact mem_mulDomain_of_finite _ {k0, -k0} fun _ hn => (coe_cosE _).trans (cosCoeff_eq_zero hn)

theorem cosState_mem_domainD : cosState ∈ (complexD d).wave.domain :=
  HilbertComplex.mem_wave_domain_fin3 _
    (by rw [cosState_zero]; exact Submodule.zero_mem _)
    (by rw [cosState_one]; exact cosE_mem_domainD)
    (by rw [cosState_one]; exact cosE_mem_adjoint_domainD)
    (by rw [cosState_two]; exact Submodule.zero_mem _)

theorem curl_cosE_applyD :
    (((complexD d).d 1 2 ⟨cosE, cosE_mem_domainD⟩ :
      Lp Mat 2 (Measure.count : Measure (Fin 3 → ℤ))) : (Fin 3 → ℤ) → Mat) k0 =
      curl (dfreq d k0) M0 := by
  refine (Operator.coeFn_mulOp_count (fun n => gradCurl.m 1 2 (dfreq d n))
    ⟨cosE, cosE_mem_domainD⟩ k0).trans ?_
  change curl (dfreq d k0) ((cosE : (Fin 3 → ℤ) → Mat) k0) = _
  rw [coe_cosE]
  simp [cosCoeff]

theorem cosState_mem_constraintD (i : Fin 3) : cosState i ∈ constraintD d i := by
  fin_cases i
  · change cosState 0 ∈ _; rw [cosState_zero]; exact Submodule.zero_mem _
  · change cosState 1 ∈ _; rw [cosState_one]; exact cosE_mem_constraintD
  · change cosState 2 ∈ _; rw [cosState_two]; exact Submodule.zero_mem _

/-! ### Every box -/

section Box

open Domain (L2F)

variable {a ℓ : R3} (hℓ : ∀ i, 0 < ℓ i)

/-- The spaces `L²(B; ℂ³)`, `L²(B; ℂ³ˣ³)`, `L²(B; ℂ³ˣ³)` on the box `B = ∏ (aᵢ, aᵢ + ℓᵢ)`. -/
abbrev SpaceBox (a ℓ : R3) (i : Fin 3) : Type :=
  W3 (L2F ℂ (openBox a ℓ) (Fin 3)) (L2F ℂ (openBox a ℓ) (Fin 3 × Fin 3))
    (L2F ℂ (openBox a ℓ) (Fin 3 × Fin 3)) i

/-- The pull-backs `u ↦ u ∘ T` from `Q` to the box, slot by slot (over `ℂ`). -/
def pullBC : ∀ i, SpaceQ i ≃L[ℂ] SpaceBox a ℓ i
  | 0 => Domain.pullDiagF (dB_ne_zero hℓ) (bB a ℓ) Models.Cube.Geometry.measurableSet_Q
      (preimage_Q hℓ) (Fin 3)
  | 1 => Domain.pullDiagF (dB_ne_zero hℓ) (bB a ℓ) Models.Cube.Geometry.measurableSet_Q
      (preimage_Q hℓ) (Fin 3 × Fin 3)
  | 2 => Domain.pullDiagF (dB_ne_zero hℓ) (bB a ℓ) Models.Cube.Geometry.measurableSet_Q
      (preimage_Q hℓ) (Fin 3 × Fin 3)

theorem inner_pullBC (i : Fin 3) (x y : SpaceQ i) :
    ⟪pullBC (a := a) hℓ i x, pullBC hℓ i y⟫_ℂ =
      (((Domain.jacD (dB ℓ))⁻¹ : ℝ) : ℂ) * ⟪x, y⟫_ℂ := by
  fin_cases i
  · exact Domain.inner_pullDiagF _ _ _ _ x y
  · exact Domain.inner_pullDiagF _ _ _ _ x y
  · exact Domain.inner_pullDiagF _ _ _ _ x y

theorem jacD_inv_pos (hℓ : ∀ i, 0 < ℓ i) : 0 < (Domain.jacD (dB ℓ))⁻¹ :=
  inv_pos.2 (Domain.jacD_pos (dB_ne_zero hℓ))

/-- The chain-rule factors are already in `complexQD`: weights `1`. -/
def kappaB : Fin 3 → Fin 3 → ℂ := fun _ _ => ((1 : ℝ) : ℂ)

theorem kappaB_ne_zero (i j : Fin 3) : kappaB i j ≠ 0 := by simp [kappaB]

/-- **The mirror complex on the box** `∏ (aᵢ, aᵢ + ℓᵢ)`: `grad`, `curl` with `σ · n = 0`,
`E_{nτ} = 0` on the faces, the pull-back of the weighted mirror complex on `Q` along
`T x = d * (x - a)`. -/
abbrev complexBoxM (a ℓ : R3) (hℓ : ∀ i, 0 < ℓ i) :
    HilbertComplex ℂ ComplexShape.fin3 (SpaceBox a ℓ) :=
  (complexQD (dB ℓ)).transport (pullBC hℓ) kappaB kappaB_ne_zero

/-- The pull-back to `Q` embeds the box complex in the weighted complex on `Q`. -/
def embeddingBox : ScaledEmbedding (complexBoxM a ℓ hℓ) (complexQD (dB ℓ)) :=
  ScaledEmbedding.ofTransportSymm (pullBC hℓ) kappaB kappaB_ne_zero
    (fun _ => (Domain.jacD (dB ℓ))⁻¹) (fun _ => jacD_inv_pos hℓ) (inner_pullBC hℓ)

/-- **The TSD constraint on the box**: the fields whose transplant to `Q` lies in `tsdQD`. -/
abbrev tsdBox (a ℓ : R3) (hℓ : ∀ i, 0 < ℓ i) (i : Fin 3) : Submodule ℂ (SpaceBox a ℓ i) :=
  (tsdQD (dB ℓ) i).comap ((pullBC (a := a) hℓ i).symm : SpaceBox a ℓ i →ₗ[ℂ] SpaceQ i)

instance (i : Fin 3) : (tsdBox a ℓ hℓ i).HasOrthogonalProjection :=
  (embeddingBox (a := a) hℓ).comap_hasOrthogonalProjection i _

/-- **TSD reduces the mirror complex on every box.**
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem reducingSubcomplexBox : (complexBoxM a ℓ hℓ).ReducingSubcomplex (tsdBox a ℓ hℓ) :=
  (embeddingBox (a := a) hℓ).reducingSubcomplex_comap (reducingSubcomplexQD (dB ℓ)) fun i x =>
    ⟨pullBC hℓ i ((tsdQD (dB ℓ) i).starProjection ((pullBC hℓ i).symm x)),
      (pullBC hℓ i).symm_apply_apply _⟩

/-- **Prop 4.17 on every box with mirror boundary conditions**: TSD data and forcing give TSD
solutions.
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem propagatesBox {s t : ℝ} {F U : ℝ → PiLp 2 (SpaceBox a ℓ)}
    (hU : Evolution.IsStrongSolution (complexBoxM a ℓ hℓ).wave (Icc s t) F U)
    (h0 : U s ∈ totalSub (tsdBox a ℓ hℓ)) (hF : ∀ τ ∈ Icc s t, F τ ∈ totalSub (tsdBox a ℓ hℓ)) :
    ∀ τ ∈ Icc s t, U τ ∈ totalSub (tsdBox a ℓ hℓ) :=
  (reducingSubcomplexBox hℓ).propagates hU h0 hF

/-- Prop 4.17 on every box with mirror boundary conditions, with existence and uniqueness.
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem existsUnique_memBox {U₀ : PiLp 2 (SpaceBox a ℓ)}
    (hU₀ : U₀ ∈ (complexBoxM a ℓ hℓ).wave.domain) (hU₀S : U₀ ∈ totalSub (tsdBox a ℓ hℓ))
    {F : ℝ → PiLp 2 (SpaceBox a ℓ)} {s t : ℝ}
    (hF : Evolution.ForcingClass.admissible (complexBoxM a ℓ hℓ).wave s t F)
    (hFS : ∀ τ ∈ Icc s t, F τ ∈ totalSub (tsdBox a ℓ hℓ)) :
    ∃ U, U s = U₀ ∧ Evolution.IsClassicalSolution (complexBoxM a ℓ hℓ).wave (Icc s t) F U ∧
      (∀ τ ∈ Icc s t, U τ ∈ totalSub (tsdBox a ℓ hℓ)) ∧
      ∀ V, V s = U₀ → Evolution.IsStrongSolution (complexBoxM a ℓ hℓ).wave (Icc s t) F V →
        EqOn V U (Icc s t) :=
  (reducingSubcomplexBox hℓ).existsUnique_mem hU₀ hU₀S hF hFS

/-- **`K* = K` on every box with mirror boundary conditions.**
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem invariantCore_eqBox :
    (complexBoxM a ℓ hℓ).waveGroup.invariantCore (totalSub (tsdBox a ℓ hℓ)) =
      totalSub (tsdBox a ℓ hℓ) :=
  (reducingSubcomplexBox hℓ).invariantCore_eq

/-! #### A complete set of eigenvectors -/

variable (d) in
/-- **The anisotropic torus complex has an eigenbasis** (the Fourier modes). -/
theorem eigenDense_complexD : (complexD d).waveGroup.EigenDense :=
  (symD d).eigenDense_waveGroup Fourier.Torus.finite_bandN Fourier.Torus.bandN_mono
    Fourier.Torus.exists_mem_bandN

variable (d) in
/-- **The weighted mirror complex on `Q` has a dense set of eigenvectors.** -/
theorem eigenDense_complexQD : (complexQD d).waveGroup.EigenDense :=
  HilbertComplex.eigenDense_compress eight_pos inner_J (reducingSubcomplex_rangeD d)
    (eigenDense_complexD d)

/-- **The mirror complex on every box has a dense set of eigenvectors** (the analogue of
`Feec.Models.Cube.Mirror.eigenDense_complexCube`). -/
theorem eigenDense_complexBoxM : (complexBoxM a ℓ hℓ).waveGroup.EigenDense :=
  HilbertComplex.eigenDense_transport_const (complexQD (dB ℓ)) (jacD_inv_pos hℓ)
    (inner_pullBC hℓ) one_ne_zero (eigenDense_complexQD (dB ℓ))


/-! #### A non-stationary TSD datum -/

/-- The datum `(0, E₀ ∘ T, 0)` on the box, `E₀ = (2 cos(2π x₃) diag(1, -1, 0))|_Q`, i.e.
`2 cos(π (x₃ - a₃)/ℓ₃) diag(1, -1, 0)`. -/
def cosStateBox (a ℓ : R3) (hℓ : ∀ i, 0 < ℓ i) : PiLp 2 (SpaceBox a ℓ) :=
  HilbertComplex.totalMap (pullBC hℓ) cosStateQ

theorem totalMap_symm_cosStateBox :
    HilbertComplex.totalMap (fun i => (pullBC (a := a) hℓ i).symm) (cosStateBox a ℓ hℓ) =
      cosStateQ :=
  PiLp.ext fun i => (pullBC hℓ i).symm_apply_apply _

/-- **A non-stationary TSD datum on every box with mirror conditions**: the constraint has
dynamical content.
See [QuennevilleBelair2015], §4.10 (Prop 4.17, corrected). -/
theorem exists_nonstationaryBox :
    ∃ y ∈ (complexBoxM a ℓ hℓ).wave.domain, y ∈ totalSub (tsdBox a ℓ hℓ) ∧
      y ∉ (complexBoxM a ℓ hℓ).waveGroup.stationary := by
  have hdomQ : cosStateQ ∈ (complexQD (dB ℓ)).wave.domain :=
    (HilbertComplex.mem_wave_domain_compress_iff eight_pos inner_J
      (reducingSubcomplex_rangeD (dB ℓ))).2 (totalJ_cosStateQ ▸ cosState_mem_domainD)
  have hd : cosStateBox a ℓ hℓ ∈ (complexBoxM a ℓ hℓ).wave.domain :=
    (HilbertComplex.mem_wave_domain_transport_iff kappaB_ne_zero (jacD_inv_pos hℓ)
      (inner_pullBC hℓ)).2 (totalMap_symm_cosStateBox hℓ ▸ hdomQ)
  have hne : (complexQD (dB ℓ)).d 1 2 ⟨cosEQ, by rw [← cosStateQ_one]; exact hdomQ.1 1 2⟩ ≠ 0 := by
    intro h
    have h1 := HilbertComplex.J_compress_d eight_pos inner_J (reducingSubcomplex_rangeD (dB ℓ))
      (i := 1) (j := 2) ⟨cosEQ, by rw [← cosStateQ_one]; exact hdomQ.1 1 2⟩
    rw [h, _root_.map_zero] at h1
    have h2 : (complexD (dB ℓ)).d 1 2 ⟨cosE, cosE_mem_domainD⟩ = 0 :=
      (apply_congr' _ _ _ J_cosEQ.symm).trans h1.symm
    apply curl_M0_neD (dB_pos hℓ)
    rw [← curl_cosE_applyD, h2]
    exact Measure.ae_count_iff.1 (Lp.coeFn_zero _ 2 Measure.count) k0
  refine ⟨cosStateBox a ℓ hℓ, hd, fun i => ?_, HilbertComplex.not_mem_stationary_of_wave_ne_zero
    ⟨_, hd⟩ fun h => ?_⟩
  · change (pullBC hℓ i).symm (pullBC hℓ i (cosStateQ i)) ∈ tsdQD (dB ℓ) i
    rw [ContinuousLinearEquiv.symm_apply_apply]
    change J i (cosStateQ i) ∈ constraintD (dB ℓ) i
    rw [← HilbertComplex.totalJ_apply, totalJ_cosStateQ]
    exact cosState_mem_constraintD i
  · have h2 := congrArg (fun y : PiLp 2 (SpaceBox a ℓ) => y 2) h
    rw [HilbertComplex.wave_apply_fin3_two] at h2
    change kappaB 1 2 • pullBC hℓ 2 ((complexQD (dB ℓ)).d 1 2 ⟨(pullBC hℓ 1).symm
      (pullBC hℓ 1 (cosStateQ 1)), _⟩) = 0 at h2
    rw [smul_eq_zero, or_iff_right (kappaB_ne_zero 1 2), (pullBC hℓ 2).map_eq_zero_iff] at h2
    exact hne ((apply_congr' _ _ _ (by
      rw [ContinuousLinearEquiv.symm_apply_apply, cosStateQ_one])).trans h2)

end Box

end Feec.Models.Box.Mirror
