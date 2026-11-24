module

public import Feec.Models.Cube.MirrorTrace
public import Feec.Models.Cube.MirrorBGG

/-!
# The mirror constraint from the TSD conditions

The constraint of the mirror complex on `Q = (0, ½)³` is defined on the Fourier side: `E` lies in
`Mirror.tsdQ 1` iff the coefficients of its mirror extension are TSD at every frequency, which
encodes the wall conditions besides the TSD conditions in `Q` (`Mirror.mem_tsdQ_one`). This file
proves the converse on the operator domains: **the wall conditions follow from the domain
conditions**. A field `E ∈ D(curl)` (with `E_{nτ} = 0`) that is symmetric, trace-free and weakly
divergence-free in `Q` (against test fields compactly supported in `Q`) lies in the electric
constraint, and likewise `B ∈ D(curl†)` (with `B_{ττ} = 0`) in the magnetic constraint.

## Method

For a symmetric trace-free `M` with `C = curl M` (row-wise), row `l` of the divergence is a skew
part of the curl: `Σ_c ∫_Q M_{lc} ∂_c ψ = ∫_Q (C_{l+1,l+2} - C_{l+2,l+1}) ψ` for the trace test
functions `ψ` of the Green's formulas of `MirrorTrace` (`Mirror.sum_integral_fderiv_eq`). Against
`ψ ∈ C_c^∞(Q)` the left side vanishes, so `C_{l+1,l+2} = C_{l+2,l+1}`
(`Mirror.curl_apply_eq_of_tsd`); hence the left side vanishes for every trace test function,
which is the weak equation `div (ext M) = 0` on `𝕋³` (`MirrorTrace.isWeakFO_extL2_iff_trace`),
i.e. `M̂(k) ξ_k = 0` at every frequency.

## Main results

* `Mirror.mem_tsdQ_one_of_tsd`, `Mirror.mem_tsdQ_two_of_tsd`: the converses of
  `Mirror.mem_tsdQ_one`, `Mirror.mem_tsdQ_two` on `D(curl)` and `D(curl†)`, and
  `Mirror.mem_adjoint_d₀_of_mem_tsdQ`: electric constraint states lie in `ker grad†`.
* `MirrorBGG.mem_tsdQ_one_of_tsd`, `MirrorBGG.mem_tsdQ_two_of_tsd`: the same on the domains of
  the second BGG operator `(S₁, curl)` and of its adjoint, and
  `MirrorBGG.mem_adjoint_d₀_of_mem_tsdQ`: electric constraint states lie in `ker (grad grad)†`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (Prop 4.17), Ch. 6
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.2 (extension by reflection)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ComplexConjugate LinearPMap
open Set MeasureTheory UnitAddTorus

@[expose] public noncomputable section

namespace Feec.Models.Cube.Mirror

open Geometry MirrorExt MirrorTrace Feec.Fourier Feec.Fourier.GradCurl
open Feec.Models.BoundedDomain (R3)
open Feec.Models.Cube.MirrorTorus (sgn sgn_mul_self)

/-- `∫_Q u g = ⟪ḡ, u⟫` for continuous `g`. -/
theorem setIntegral_mul_eq_inner (u : Domain.L2 ℂ (Q (Fin 3))) {g : R3 → ℂ} (hg : Continuous g) :
    ∫ y in Q (Fin 3), (u : R3 → ℂ) y * g y =
      ⟪toL2Q (n := 2) (Complex.continuous_conj.comp hg), u⟫_ℂ := by
  rw [L2.inner_def]
  refine integral_congr_ae ((coe_toL2Q (Complex.continuous_conj.comp hg)).mono fun y hy => ?_)
  simp only [RCLike.inner_apply, hy, Function.comp_apply, Complex.conj_conj, mul_comm]

variable {cm cc : Fin 3 × Fin 3 → Fin 3 → ℂ} {cv : Fin 3 → Fin 3 → ℂ}

/-- **Row `l` of the divergence of a symmetric trace-free field is a skew part of its curl**:
for `C = curl M` in the weak form `CurlTrace cc`,
`Σ_c ∫_Q M_{lc} ∂_c ψ = ∫_Q C_{l+1,l+2} ψ - ∫_Q C_{l+2,l+1} ψ`. -/
theorem sum_integral_fderiv_eq {M C : MQ} (hsym : ∀ i j, M (i, j) = M (j, i))
    (htr : ∑ i, M (i, i) = 0) (hC : CurlTrace cc M C) (l : Fin 3) {ψ : R3 → ℂ}
    (h₁ : IsTraceTest (cc (l + 1, l + 2)) ψ) (h₂ : IsTraceTest (cc (l + 2, l + 1)) ψ) :
    ∑ c, ∫ y in Q (Fin 3), (M (l, c) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single c 1) =
      (∫ y in Q (Fin 3), (C (l + 1, l + 2) : R3 → ℂ) y * ψ y) -
        ∫ y in Q (Fin 3), (C (l + 2, l + 1) : R3 → ℂ) y * ψ y := by
  have i₁ : l + 1 + 1 = l + 2 := by fin_cases l <;> rfl
  have i₂ : l + 1 + 2 = l := by fin_cases l <;> rfl
  have i₃ : l + 2 + 1 = l := by fin_cases l <;> rfl
  have i₄ : l + 2 + 2 = l + 1 := by fin_cases l <;> rfl
  have e₁ := hC (l + 1) (l + 2) ψ h₁
  have e₂ := hC (l + 2) (l + 1) ψ h₂
  rw [i₃, i₄, hsym (l + 1) l] at e₁
  rw [i₁, i₂, hsym (l + 2) l] at e₂
  have hsum : ∀ {A : Type} [AddCommMonoid A] (f : Fin 3 → A),
      ∑ c, f c = f l + f (l + 1) + f (l + 2) := fun f => by
    rw [← Equiv.sum_comp (Equiv.addLeft l), Fin.sum_univ_three]
    simp only [Equiv.coe_addLeft, add_zero]
  have htr' : (∫ y in Q (Fin 3), (M (l, l) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single l 1)) +
      (∫ y in Q (Fin 3), (M (l + 1, l + 1) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single l 1)) +
      ∫ y in Q (Fin 3), (M (l + 2, l + 2) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single l 1) = 0 := by
    simp only [setIntegral_mul_eq_inner _ (h₁.continuous_fderiv l)]
    rw [← inner_add_right, ← inner_add_right]
    rw [← hsum fun i => M (i, i), htr, inner_zero_right]
  rw [hsum]
  linear_combination htr' - e₁ + e₂

/-- Compactly supported smooth functions in `Q` are trace test functions of every parity. -/
theorem isTraceTest_of_isTest {d : Type*} [Fintype d] (c : d → ℂ) {ψ : (d → ℝ) → ℂ}
    (hψ : Domain.IsTest (Q d) ψ) : IsTraceTest c ψ :=
  ⟨hψ.contDiff.of_le (by exact_mod_cast le_top), fun j _ y _ hy => hψ.eq_zero_of_notMem
    fun hQ => by have h := mem_Q.1 hQ j; rcases hy with hy | hy <;> simp [hy] at h⟩

/-- **The skew part of the curl of a TSD field vanishes**: for `M` symmetric, trace-free and
weakly divergence-free in `Q`, and `C = curl M` in the weak form `CurlTrace cc`,
`C_{l+1,l+2} = C_{l+2,l+1}`. -/
theorem curl_apply_eq_of_tsd {M C : MQ} (hsym : ∀ i j, M (i, j) = M (j, i))
    (htr : ∑ i, M (i, i) = 0)
    (hdiv : ∀ φ : Fin 3 → R3 → ℂ, ∀ hφ : Domain.IsTestField (Q (Fin 3)) φ,
      ⟪M, Domain.testField ((Domain.gradOp 3 3 : Domain.ConstCoeffOp _ ℂ _ _).isTestField_apply
        hφ)⟫_ℂ = 0)
    (hC : CurlTrace cc M C) (l : Fin 3) : C (l + 1, l + 2) = C (l + 2, l + 1) := by
  rw [← sub_eq_zero]
  refine Domain.L2.eq_zero_of_forall_integral isOpen_Q _ fun g hg => ?_
  set ψ : R3 → ℂ := fun y => (g y : ℂ)
  have hψ : Domain.IsTest (Q (Fin 3)) ψ := hg.ofReal
  have hconj : ∀ y v, conj (fderiv ℝ ψ y v) = fderiv ℝ ψ y v := fun y v => by
    have h : Complex.conjCLE ∘ ψ = ψ := funext fun y => Complex.conj_ofReal _
    conv_rhs => rw [← h]
    rw [Complex.conjCLE.comp_fderiv]; rfl
  have hA := sum_integral_fderiv_eq hsym htr hC l (isTraceTest_of_isTest _ hψ)
    (isTraceTest_of_isTest _ hψ)
  have hd := hdiv (Pi.single l ψ) (Domain.IsTestField.single l hψ)
  rw [Domain.inner_testField, Fintype.sum_prod_type, Finset.sum_eq_single l] at hd
  rotate_left
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [Domain.gradOp_apply, Pi.single_eq_of_ne ha]
  · simp
  simp only [Domain.gradOp_apply, Pi.single_eq_same] at hd
  calc _ = conj (∫ y in Q (Fin 3), ((C (l + 1, l + 2) - C (l + 2, l + 1) :
        Domain.L2 ℂ (Q (Fin 3))) : R3 → ℂ) y * ψ y) := by
        rw [← integral_conj]; congr 1; funext y; simp [ψ]
    _ = 0 := by
      rw [setIntegral_mul_eq_inner _ hψ.continuous, inner_sub_right,
        ← setIntegral_mul_eq_inner _ hψ.continuous, ← setIntegral_mul_eq_inner _ hψ.continuous,
        ← hA, map_sum, ← hd]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← integral_conj]
      congr 1; funext y
      rw [map_mul, hconj]

variable (hcm : ∀ p k, cm p k * cm p k = 1) (hcv : ∀ a k, cv a k * cv a k = 1)

include hcv in
/-- **Divergence-free rows on `Q` are divergence-free on `𝕋³`**: if
`Σ_c ∫_Q M_{lc} ∂_c ψ = 0` for every trace test function `ψ` of the parity `cv l` (the weak form
of `div_l M = 0` with `M_{l,τ} n_τ = 0` on the faces), then `Σ_c M̂_{lc}(k) ξ_c = 0`,
`ξ = 2πk`. -/
theorem sum_extF_mul_freq_eq_zero
    (hpar : ∀ a b, Function.update (cm (a, b)) b (-cm (a, b) b) = cv a) {M : MQ} (l : Fin 3)
    (h : ∀ ψ : R3 → ℂ, IsTraceTest (cv l) ψ →
      ∑ c, ∫ y in Q (Fin 3), (M (l, c) : R3 → ℂ) y * fderiv ℝ ψ y (Pi.single c 1) = 0)
    (k : Fin 3 → ℤ) :
    ∑ c, (extF hcm M : (Fin 3 → ℤ) → Mat) k (l, c) * (2 * Real.pi * k c) = 0 := by
  have hw := (isWeakFO_extL2_iff_trace (n := 2) (fun c p => if c = p then (1 : ℂ) else 0)
    (fun p => hcm (l, p)) (hcv l) (fun c p hα => ?_) (fun p => M (l, p)) 0).2 fun ψ hψ => ?_
  · have e := (TorusWeak.isWeakFO_iff _ _ _).1 hw k
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at e
    rw [_root_.map_zero, ← coeffCLM_apply, _root_.map_zero] at e
    have hI : ∑ c, 2 * Real.pi * Complex.I * k c *
        mFourierCoeff (extL2 (hcm (l, c)) (M (l, c)) : UnitAddTorus (Fin 3) → ℂ) k =
          Complex.I * ∑ c, (extF hcm M : (Fin 3 → ℤ) → Mat) k (l, c) * (2 * Real.pi * k c) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [extF_coeff]; ring
    rw [hI] at e
    exact (mul_eq_zero.1 e.symm).resolve_left Complex.I_ne_zero
  · simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hα
    subst hα
    exact hpar l c
  · simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [h ψ hψ, setIntegral_mul_eq_inner _ hψ.contDiff.continuous, inner_zero_right, neg_zero]

include hcm in
/-- **The extension of a TSD field with divergence-free rows on `𝕋³` is TSD fibrewise**, for
parities `cm` symmetric in the indices and constant on the diagonal. -/
theorem extF_mem_tsd (hsymc : ∀ a b, cm (a, b) = cm (b, a)) (hdiag : ∀ a, cm (a, a) = cm (0, 0))
    {M : MQ} (hsym : ∀ i j, M (i, j) = M (j, i)) (htr : ∑ i, M (i, i) = 0) (k : Fin 3 → ℤ)
    (hdiv : ∀ l, ∑ c, (extF hcm M : (Fin 3 → ℤ) → Mat) k (l, c) * (2 * Real.pi * k c) = 0) :
    (extF hcm M : (Fin 3 → ℤ) → Mat) k ∈ tsd (Fourier.Torus.freq k) := by
  refine mem_tsd.2 ⟨?_, ?_, ?_⟩
  · ext i j
    rw [Matrix.transpose_apply, toMatrix_apply, toMatrix_apply, extF_coeff, extF_coeff, hsym j i,
      extL2_congr (hsymc j i) (hcm (j, i)) (hcm (i, j))]
  · have hc0 : ∀ j, cm (0, 0) j * cm (0, 0) j = 1 := hcm (0, 0)
    simp only [Matrix.trace, Matrix.diag, toMatrix_apply, extF_coeff]
    rw [show (0 : ℂ) = coeffCLM k (extL2 hc0 (∑ i, M (i, i))) by
      rw [htr, _root_.map_zero, _root_.map_zero], map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeffCLM_apply, extL2_congr (hdiag i) (hcm (i, i)) hc0]
  · funext l
    rw [Pi.zero_apply, ← hdiv l]
    simp only [Matrix.mulVec, dotProduct, toMatrix_apply, cfreq, Fourier.Torus.freq_apply]
    push_cast
    rfl

include hcm hcv in
/-- **TSD fields in the domain of a mirror curl have TSD extensions**: `M` symmetric, trace-free
and weakly divergence-free in `Q`, with `C = curl M` in the weak form `CurlTrace cc`, has
fibrewise TSD extension by the parities `cm`. -/
theorem extF_mem_tsd_of_tsd (hpar : ∀ a b, Function.update (cm (a, b)) b (-cm (a, b) b) = cv a)
    (hsymc : ∀ a b, cm (a, b) = cm (b, a)) (hdiag : ∀ a, cm (a, a) = cm (0, 0))
    (hcc₁ : ∀ l, cc (l + 1, l + 2) = cv l) (hcc₂ : ∀ l, cc (l + 2, l + 1) = cv l) {M C : MQ}
    (hC : CurlTrace cc M C) (hsym : ∀ i j, M (i, j) = M (j, i)) (htr : ∑ i, M (i, i) = 0)
    (hdiv : ∀ φ : Fin 3 → R3 → ℂ, ∀ hφ : Domain.IsTestField (Q (Fin 3)) φ,
      ⟪M, Domain.testField ((Domain.gradOp 3 3 : Domain.ConstCoeffOp _ ℂ _ _).isTestField_apply
        hφ)⟫_ℂ = 0)
    (k : Fin 3 → ℤ) : (extF hcm M : (Fin 3 → ℤ) → Mat) k ∈ tsd (Fourier.Torus.freq k) :=
  extF_mem_tsd hcm hsymc hdiag hsym htr k fun l =>
    sum_extF_mul_freq_eq_zero hcm hcv hpar l (fun ψ hψ => by
      rw [sum_integral_fderiv_eq hsym htr hC l (by rwa [hcc₁]) (by rwa [hcc₂]),
        curl_apply_eq_of_tsd hsym htr hdiv hC l, sub_self]) k

/-- **The electric mirror constraint from the TSD conditions**: `E ∈ D(curl)` (mirror condition
`E_{nτ} = 0`) symmetric, trace-free and weakly divergence-free in `Q` lies in `tsdQ 1`; the
condition `E_{τn} = 0` of the constraint follows. Converse of `mem_tsdQ_one`. -/
theorem mem_tsdQ_one_of_tsd {E : MQ} (hE : E ∈ (complexQ.d 1 2).domain)
    (hsym : ∀ i j, E (i, j) = E (j, i)) (htr : ∑ i, E (i, i) = 0)
    (hdiv : ∀ φ : Fin 3 → R3 → ℂ, ∀ hφ : Domain.IsTestField (Q (Fin 3)) φ,
      ⟪E, Domain.testField ((Domain.gradOp 3 3 : Domain.ConstCoeffOp _ ℂ _ _).isTestField_apply
        hφ)⟫_ℂ = 0) :
    E ∈ tsdQ 1 :=
  Operator.mem_fibreSub.2 <| Measure.ae_count_iff.2 fun k =>
    extF_mem_tsd_of_tsd cE_sq cV_sq (fun a b => (cV_eq_update a b).symm)
      (fun a b => funext fun k => by simp only [cE]; ring)
      (fun a => funext fun k => by simp only [cE, sgn_mul_self])
      (fun l => funext fun k => by fin_cases l <;> fin_cases k <;> simp [cB, cV, sgn])
      (fun l => funext fun k => by fin_cases l <;> fin_cases k <;> simp [cB, cV, sgn])
      ((complexQ_d₁_iff E _).1 ⟨hE, rfl⟩) hsym htr hdiv k

/-- **The magnetic mirror constraint from the TSD conditions**: `B ∈ D(curl†)` (mirror condition
`B_{ττ} = 0`) symmetric, trace-free and weakly divergence-free in `Q` lies in `tsdQ 2`; the
condition `B_{nn} = 0` of the constraint follows. Converse of `mem_tsdQ_two`. -/
theorem mem_tsdQ_two_of_tsd {B : MQ} (hB : B ∈ ((complexQ.d 1 2)†).domain)
    (hsym : ∀ i j, B (i, j) = B (j, i)) (htr : ∑ i, B (i, i) = 0)
    (hdiv : ∀ φ : Fin 3 → R3 → ℂ, ∀ hφ : Domain.IsTestField (Q (Fin 3)) φ,
      ⟪B, Domain.testField ((Domain.gradOp 3 3 : Domain.ConstCoeffOp _ ℂ _ _).isTestField_apply
        hφ)⟫_ℂ = 0) :
    B ∈ tsdQ 2 :=
  Operator.mem_fibreSub.2 <| Measure.ae_count_iff.2 fun k =>
    extF_mem_tsd_of_tsd cB_sq cPV_sq
      (fun a b => funext fun k => by
        fin_cases a <;> fin_cases b <;> fin_cases k <;> simp [cB, cPV, sgn, Function.update])
      (fun a b => funext fun k => by simp only [cB]; ring)
      (fun a => funext fun k => by simp only [cB, sgn_mul_self])
      (fun l => funext fun k => by fin_cases l <;> fin_cases k <;> simp [cE, cPV, sgn])
      (fun l => funext fun k => by fin_cases l <;> fin_cases k <;> simp [cE, cPV, sgn])
      ((complexQ_adjoint_d₁_iff B _).1 ⟨hB, rfl⟩) hsym htr hdiv k

/-- **Electric constraint states are in `ker grad†`**: `E ∈ tsdQ 1` lies in the domain of
`d₀† = -div` with `d₀† E = 0` (TSD fields on the torus are divergence-free). -/
theorem mem_adjoint_d₀_of_mem_tsdQ {E : MQ} (hE : E ∈ tsdQ 1) :
    ∃ h : E ∈ ((complexQ.d 0 1)†).domain, (complexQ.d 0 1)† ⟨E, h⟩ = 0 := by
  obtain ⟨y, hy, hy0⟩ := LinearPMap.mem_ker_iff.1 (constraint_le_ker_adjoint hE)
  have h : E ∈ ((complexQ.d 0 1)†).domain := mem_complexQ_adjoint_domain_iff.2 (hy ▸ y.2)
  refine ⟨h, embeddingQ.J_injective 0 ?_⟩
  change J 0 _ = J 0 0
  rw [J_complexQ_adjoint (i := 0) (j := 1) ⟨(E : SpaceQ 1), h⟩, _root_.map_zero, ← hy0]
  exact LinearPMap.apply_congr' _ _ _ hy

end Feec.Models.Cube.Mirror

namespace Feec.Models.Cube.MirrorBGG

open Geometry MirrorExt Feec.Fourier Feec.Fourier.GradCurl Feec.Fourier.BGG
open Feec.Models.BoundedDomain (R3)
open Feec.Models.Cube.Mirror (MQ eight_pos)

/-- `D((S₁, curl)†) ∩ ({0} × L²) ⊆ {0} × D(curl†)`: if `(0, B)` lies in the domain of the adjoint of
the second BGG operator, `B` lies in the domain of the adjoint of the mirror curl. -/
theorem mem_adjoint_curl_domain {B : MQ}
    (hB : (WithLp.toLp 2 (0, B) : W2Q) ∈ ((complexQ.d 1 2)†).domain) :
    B ∈ ((Mirror.complexQ.d 1 2)†).domain := by
  have h := (HilbertComplex.mem_adjoint_compress_iff eight_pos inner_J
    reducingSubcomplex_range).1 hB
  change J₂ _ ∈ ((Fourier.Torus.symbolComplex bggFamily).toHilbertComplex.d 1 2)†.domain at h
  rw [(Fourier.Torus.symbolComplex bggFamily).adjoint_d 1 2] at h
  refine Mirror.mem_complexQ_adjoint_domain_iff.2 ?_
  rw [Mirror.adjoint_torus_curl]
  refine (show MemLp _ 2 Measure.count from h).ae_eq (ae_of_all _ fun n => ?_)
  change ContinuousLinearMap.adjoint (bgg (Fourier.Torus.freq n))
    ((J₂ (WithLp.toLp 2 (0, B)) : (Fin 3 → ℤ) → VM) n) = curl (Fourier.Torus.freq n)
      ((extF (c := Mirror.cB) Mirror.cB_sq B : (Fin 3 → ℤ) → Mat) n)
  rw [J₂, pairLp_coeff, WithLp.ofLp_toLp, _root_.map_zero,
    Measure.ae_count_iff.1 (Lp.coeFn_zero _ 2 Measure.count) n]
  exact adjoint_bgg_inr _ _

/-- **The electric BGG constraint from the TSD conditions**: `E` in the domain of the second BGG
operator `(S₁, curl)`, symmetric, trace-free and weakly divergence-free in `Q`, lies in
`tsdQ 1`. Converse of `tsd_of_mem_tsdQ` in the electric slot. -/
theorem mem_tsdQ_one_of_tsd {E : MQ} (hE : E ∈ (complexQ.d 1 2).domain)
    (hsym : ∀ i j, E (i, j) = E (j, i)) (htr : ∑ i, E (i, i) = 0)
    (hdiv : ∀ φ : Fin 3 → R3 → ℂ, ∀ hφ : Domain.IsTestField (Q (Fin 3)) φ,
      ⟪E, Domain.testField ((Domain.gradOp 3 3 : Domain.ConstCoeffOp _ ℂ _ _).isTestField_apply
        hφ)⟫_ℂ = 0) :
    E ∈ tsdQ 1 :=
  Mirror.mem_tsdQ_one_of_tsd (complexQ_d₁_eq ⟨E, hE⟩).fst hsym htr hdiv

/-- **The magnetic BGG constraint from the TSD conditions**: `B` with `(0, B)` in the domain of
the adjoint of `(S₁, curl)`, symmetric, trace-free and weakly divergence-free in `Q`, lies in the
magnetic constraint (`(0, B) ∈ tsdQ 2` by `mem_tsdQ_two`). -/
theorem mem_tsdQ_two_of_tsd {B : MQ}
    (hB : (WithLp.toLp 2 (0, B) : W2Q) ∈ ((complexQ.d 1 2)†).domain)
    (hsym : ∀ i j, B (i, j) = B (j, i)) (htr : ∑ i, B (i, i) = 0)
    (hdiv : ∀ φ : Fin 3 → R3 → ℂ, ∀ hφ : Domain.IsTestField (Q (Fin 3)) φ,
      ⟪B, Domain.testField ((Domain.gradOp 3 3 : Domain.ConstCoeffOp _ ℂ _ _).isTestField_apply
        hφ)⟫_ℂ = 0) :
    B ∈ Mirror.tsdQ 2 :=
  Mirror.mem_tsdQ_two_of_tsd (mem_adjoint_curl_domain hB) hsym htr hdiv

/-- **Electric constraint states are in `ker (grad grad)†`**: `E ∈ tsdQ 1` lies in the domain of
`d₀† = div div` with `d₀† E = 0`. -/
theorem mem_adjoint_d₀_of_mem_tsdQ {E : MQ} (hE : E ∈ tsdQ 1) :
    ∃ h : E ∈ ((complexQ.d 0 1)†).domain, (complexQ.d 0 1)† ⟨E, h⟩ = 0 := by
  obtain ⟨y, hy, hy0⟩ := LinearPMap.mem_ker_iff.1 (Models.Torus.BGG.constraint_le_ker_adjoint hE)
  have h : E ∈ ((complexQ.d 0 1)†).domain :=
    (HilbertComplex.mem_adjoint_compress_iff eight_pos inner_J reducingSubcomplex_range).2
      (hy ▸ y.2)
  refine ⟨h, embeddingQ.J_injective 0 ?_⟩
  change J 0 _ = J 0 0
  rw [HilbertComplex.J_adjoint_compress_d eight_pos inner_J reducingSubcomplex_range
    (i := 0) (j := 1) ⟨(E : SpaceQ 1), h⟩, _root_.map_zero, ← hy0]
  exact LinearPMap.apply_congr' _ _ _ hy

end Feec.Models.Cube.MirrorBGG
