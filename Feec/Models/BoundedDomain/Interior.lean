module

public import Feec.Models.BoundedDomain.Density
public import Feec.Domain.FiniteSpeed

/-!
# Interior TSD propagation for the grad–curl complex (finite speed of propagation)

On a bounded open `Ω ⊆ ℝ³`, TSD propagation (the conclusion of thesis Prop 4.17) fails for the
Hodge wave equation of the grad–curl complex `H̊¹ → H̊(curl) → L²`
(`Feec.Counterexamples.BoundedDomainTSD.tsd_not_propagates`): the electric boundary condition
creates a TSD violation at `∂Ω`. This file proves that the violation cannot enter the **domain
of dependence**: for TSD data the solution stays symmetric and trace-free at time `t` at every
point whose Euclidean distance to `ℝ³ \ Ω` exceeds `t`.

## The mathematics

1. *Interior equations* (`WeakEB`): `Ė = -curl B`, `Ḃ = curl E` tested against `C_c^∞(Ω; ℝ³ˣ³)`,
   `div E = div B = 0` at `t = 0`; divergence-freeness is conserved (`WeakEB.divE`,
   `WeakEB.divB`). Strong solutions of the Hodge wave equation of the grad–curl complex with TSD
   data satisfy them (`weakEB_of_isStrongSolution`): `σ ≡ 0`, `div E ≡ 0` from
   `Feec.ShortHilbertComplex.divFree_propagates`, and the wave components `wave_apply_*`.
2. *The violation system* (`viol`): `W = (a(E), τ(E), a(B), τ(B))`, `a(X)_k = X_{k+1,k+2} -
   X_{k+2,k+1}` (twice the axial vector of `skw X`), `τ(X) = tr X`, is a weak solution of the
   symmetric hyperbolic system `∂ₜ W = Σ ∂_{β j i} Wᵢ` with the coefficients `violDir`
   (`WeakEB.isWeakSolution_viol`, from the distributional Lemma 3.5 identities
   `sum_integral_curlM_cTr`, `sum_integral_curlM_cAx`), of unit speed for the Euclidean norm
   (`isSymmHyperbolic_violDir`: `|2 ξ · F(W)| ≤ |ξ| |W|²`, `abs_two_flux_le`).
3. *Finite speed* (`Feec.Domain.FiniteSpeed.IsWeakSolution.ae_eq_zero_of_preimage_ball`, through
   `WithLp.toLp 2 : ℝ³ → EuclideanSpace ℝ (Fin 3)`, since `R3` carries the sup norm): the
   violation vanishes on the cone `{|y - x| < r - t}` of every Euclidean ball `{|z - x| < r} ⊆ Ω`
   (`WeakEB.ae_viol_eq_zero`), hence on the domain of dependence `depDomain Ω t`
   (`WeakEB.ae_viol_eq_zero_depDomain`).

## Main results

* `WeakEB.mem_tsd_univ`: on `Ω = ℝ³` the weak equations propagate `L²(TSD)`.
* `tsd_depDomain`: strong solutions of the Hodge wave equation of the grad–curl complex with TSD
  data are symmetric and trace-free a.e. on `depDomain Ω t`; `tsd_depDomain_distrib`,
  `tsd_depDomain_local` (restriction to `depDomain Ω t` lies in `L²(TSD)`).
* The explicit datum `(0, 0, β)` violates TSD in the boundary layer
  (`Feec.Counterexamples.BoundedDomainTSD.beta_violation_boundary_layer`).

## References

* [QuennevilleBelair2015], §3.4 (Lemma 3.5, Prop 3.6), §4.10 (Props 4.17, 4.18, (4.14))
* [Evans2010], §7.3.2 (domain of dependence)
* [ACBY1997] (the Einstein–Bianchi system)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ContDiff Matrix LinearPMap
open MeasureTheory Set Filter Topology Feec.Domain

namespace Feec.Models.BoundedDomain

/-! ## Pointwise algebra of the violation system -/

/-- The energy density `|W|² = |a_E|² + τ_E² + |a_B|² + τ_B²`. -/
def dens (aE aB : Fin 3 → ℝ) (τE τB : ℝ) : ℝ :=
  ∑ k, aE k ^ 2 + τE ^ 2 + ∑ k, aB k ^ 2 + τB ^ 2

/-- The energy flux `F = a_E × a_B - τ_B a_E + τ_E a_B` (component `c`). -/
def vflux (aE aB : Fin 3 → ℝ) (τE τB : ℝ) (c : Fin 3) : ℝ :=
  aE (c + 1) * aB (c + 2) - aE (c + 2) * aB (c + 1) - τB * aE c + τE * aB c

theorem dens_nonneg (aE aB : Fin 3 → ℝ) (τE τB : ℝ) : 0 ≤ dens aE aB τE τB := by
  unfold dens; positivity

/-- Cauchy–Schwarz in `ℝ⁴`. -/
theorem sq_dot4_le (u0 u1 u2 u3 v0 v1 v2 v3 : ℝ) :
    (u0 * v0 + u1 * v1 + u2 * v2 + u3 * v3) ^ 2 ≤
      (u0 ^ 2 + u1 ^ 2 + u2 ^ 2 + u3 ^ 2) * (v0 ^ 2 + v1 ^ 2 + v2 ^ 2 + v3 ^ 2) := by
  have e : (u0 ^ 2 + u1 ^ 2 + u2 ^ 2 + u3 ^ 2) * (v0 ^ 2 + v1 ^ 2 + v2 ^ 2 + v3 ^ 2) -
      (u0 * v0 + u1 * v1 + u2 * v2 + u3 * v3) ^ 2 = (u0 * v1 - u1 * v0) ^ 2 +
      (u0 * v2 - u2 * v0) ^ 2 + (u0 * v3 - u3 * v0) ^ 2 + (u1 * v2 - u2 * v1) ^ 2 +
      (u1 * v3 - u3 * v1) ^ 2 + (u2 * v3 - u3 * v2) ^ 2 := by ring
  have : 0 ≤ (u0 * v1 - u1 * v0) ^ 2 + (u0 * v2 - u2 * v0) ^ 2 + (u0 * v3 - u3 * v0) ^ 2 +
      (u1 * v2 - u2 * v1) ^ 2 + (u1 * v3 - u3 * v1) ^ 2 + (u2 * v3 - u3 * v2) ^ 2 := by
    positivity
  linarith

/-- From `P² ≤ U (s V)`, `s ≤ c²`: `|2P| ≤ c (U + V)`. -/
theorem abs_two_le_of_sq_le {P U V s c : ℝ} (h : P ^ 2 ≤ U * (s * V)) (hs : s ≤ c ^ 2)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hc : 0 ≤ c) : |2 * P| ≤ c * (U + V) := by
  have h1 : P ^ 2 ≤ c ^ 2 * (U * V) := by
    calc P ^ 2 ≤ U * (s * V) := h
      _ ≤ U * (c ^ 2 * V) := by gcongr
      _ = c ^ 2 * (U * V) := by ring
  have h4 : 4 * (U * V) ≤ (U + V) ^ 2 := by nlinarith [sq_nonneg (U - V)]
  have h2 : (2 * P) ^ 2 ≤ (c * (U + V)) ^ 2 := by
    have : c ^ 2 * (4 * (U * V)) ≤ c ^ 2 * (U + V) ^ 2 := by gcongr
    nlinarith
  exact abs_le_of_sq_le_sq' h2 (by positivity) |> fun h => abs_le.2 ⟨h.1, h.2⟩

/-- **Unit propagation speed** of the violation system: `|2 ξ · F(W)| ≤ c |W|²` whenever
`|ξ| ≤ c`. -/
theorem abs_two_flux_le (ξ aE aB : Fin 3 → ℝ) (τE τB c : ℝ) (hc : 0 ≤ c)
    (hξ : ∑ k, ξ k ^ 2 ≤ c ^ 2) :
    |2 * ∑ k, ξ k * vflux aE aB τE τB k| ≤ c * dens aE aB τE τB := by
  have hcs := sq_dot4_le (aE 0) (aE 1) (aE 2) τE (aB 1 * ξ 2 - aB 2 * ξ 1 - τB * ξ 0)
    (aB 2 * ξ 0 - aB 0 * ξ 2 - τB * ξ 1) (aB 0 * ξ 1 - aB 1 * ξ 0 - τB * ξ 2)
    (ξ 0 * aB 0 + ξ 1 * aB 1 + ξ 2 * aB 2)
  have e1 : ∑ k, ξ k * vflux aE aB τE τB k = aE 0 * (aB 1 * ξ 2 - aB 2 * ξ 1 - τB * ξ 0) +
      aE 1 * (aB 2 * ξ 0 - aB 0 * ξ 2 - τB * ξ 1) + aE 2 * (aB 0 * ξ 1 - aB 1 * ξ 0 - τB * ξ 2) +
      τE * (ξ 0 * aB 0 + ξ 1 * aB 1 + ξ 2 * aB 2) := by
    simp only [vflux, Fin.sum_univ_three]
    simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
      show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
      show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
    ring
  have e2 : (aB 1 * ξ 2 - aB 2 * ξ 1 - τB * ξ 0) ^ 2 + (aB 2 * ξ 0 - aB 0 * ξ 2 - τB * ξ 1) ^ 2 +
      (aB 0 * ξ 1 - aB 1 * ξ 0 - τB * ξ 2) ^ 2 + (ξ 0 * aB 0 + ξ 1 * aB 1 + ξ 2 * aB 2) ^ 2 =
      (∑ k, ξ k ^ 2) * (aB 0 ^ 2 + aB 1 ^ 2 + aB 2 ^ 2 + τB ^ 2) := by
    simp only [Fin.sum_univ_three]; ring
  have e3 : dens aE aB τE τB = (aE 0 ^ 2 + aE 1 ^ 2 + aE 2 ^ 2 + τE ^ 2) +
      (aB 0 ^ 2 + aB 1 ^ 2 + aB 2 ^ 2 + τB ^ 2) := by
    simp only [dens, Fin.sum_univ_three]; ring
  rw [e1, e3]
  rw [e2] at hcs
  exact abs_two_le_of_sq_le hcs hξ (by positivity) (by positivity) hc

/-! ## The violation system -/

/-- The components of the violation `W = (a(E), τ(E), a(B), τ(B))`. -/
abbrev VIdx := (Fin 3 ⊕ Unit) ⊕ (Fin 3 ⊕ Unit)

/-- `e_k × e_m`. -/
def crossDir (k m : Fin 3) : R3 :=
  if m = k + 1 then Pi.single (k + 2) 1 else if m = k + 2 then -Pi.single (k + 1) 1 else 0

/-- The coefficients `β j i` of the violation system `∂ₜ Wⱼ = Σᵢ ∂_{β j i} Wᵢ`:
`∂ₜ a_E = -∇τ_B - curl a_B`, `∂ₜ τ_E = div a_B`, `∂ₜ a_B = ∇τ_E + curl a_E`, `∂ₜ τ_B = -div a_E`. -/
def violDir : VIdx → VIdx → R3
  | .inl (.inl k), .inr (.inl m) => crossDir k m
  | .inr (.inl m), .inl (.inl k) => crossDir k m
  | .inl (.inl k), .inr (.inr _) => -Pi.single k 1
  | .inr (.inr _), .inl (.inl k) => -Pi.single k 1
  | .inl (.inr _), .inr (.inl m) => Pi.single m 1
  | .inr (.inl m), .inl (.inr _) => Pi.single m 1
  | _, _ => 0

theorem violDir_symm (j i : VIdx) : violDir j i = violDir i j := by
  rcases j with (k | _) | (k | _) <;> rcases i with (m | _) | (m | _) <;> rfl

/-- The Euclidean structure on `ℝ³`: `toLp : R3 ≃ EuclideanSpace ℝ (Fin 3)`. -/
abbrev euc : R3 ≃L[ℝ] EuclideanSpace ℝ (Fin 3) := (EuclideanSpace.equiv (Fin 3) ℝ).symm

theorem euc_apply (x : R3) : euc x = WithLp.toLp 2 x := rfl

theorem measurePreserving_euc : MeasurePreserving euc volume volume :=
  PiLp.volume_preserving_toLp (Fin 3)

theorem measurePreserving_euc_symm : MeasurePreserving euc.symm volume volume :=
  PiLp.volume_preserving_ofLp (Fin 3)

/-- `‖x‖_{EuclideanSpace}² = Σ xᵢ²`. -/
theorem sum_sq_le_opNorm_sq (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :
    ∑ c, L (euc (Pi.single c 1)) ^ 2 ≤ ‖L‖ ^ 2 := by
  set ξ : Fin 3 → ℝ := fun c => L (euc (Pi.single c 1))
  set v : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ξ
  have hLv : L v = ∑ c, ξ c ^ 2 := by
    have e : v = ∑ c, ξ c • euc (Pi.single c 1) := by
      refine PiLp.ext fun i => ?_
      simp [v, Finset.sum_apply, Pi.single_apply]
    rw [e, map_sum]
    simp only [map_smul, smul_eq_mul, sq]
    rfl
  have hv : ‖v‖ = Real.sqrt (∑ c, ξ c ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp [v]
  have h1 : ∑ c, ξ c ^ 2 ≤ ‖L‖ * Real.sqrt (∑ c, ξ c ^ 2) := by
    calc ∑ c, ξ c ^ 2 = L v := hLv.symm
      _ ≤ ‖L‖ * ‖v‖ := (le_abs_self _).trans (L.le_opNorm v)
      _ = _ := by rw [hv]
  have hs : 0 ≤ ∑ c, ξ c ^ 2 := by positivity
  have hsq := Real.sq_sqrt hs
  have h2 : Real.sqrt (∑ c, ξ c ^ 2) ≤ ‖L‖ := by
    rcases (Real.sqrt_nonneg (∑ c, ξ c ^ 2)).lt_or_eq with h | h
    · nlinarith
    · rw [← h]; exact norm_nonneg _
  calc ∑ c, ξ c ^ 2 = Real.sqrt (∑ c, ξ c ^ 2) ^ 2 := hsq.symm
    _ ≤ ‖L‖ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2

/-- **The violation system is symmetric hyperbolic of unit speed** for the Euclidean norm. -/
theorem isSymmHyperbolic_violDir :
    FiniteSpeed.IsSymmHyperbolic (fun j i => euc (violDir j i)) 1 := by
  refine ⟨fun j i => by rw [violDir_symm], zero_le_one, fun L w => ?_⟩
  set ξ : Fin 3 → ℝ := fun c => L (euc (Pi.single c 1))
  set aE : Fin 3 → ℝ := fun k => w (.inl (.inl k))
  set aB : Fin 3 → ℝ := fun k => w (.inr (.inl k))
  have hL : ∀ v : R3, L (euc v) = ∑ c, v c * ξ c := fun v => by
    have e : v = ∑ c, v c • (Pi.single c 1 : R3) := by
      funext i; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [e]
    simp [map_sum, map_smul, ξ]
  have key : ∑ j, ∑ i, w j * w i * L (euc (violDir j i)) =
      2 * ∑ c, ξ c * vflux aE aB (w (.inl (.inr ()))) (w (.inr (.inr ()))) c := by
    simp only [Fintype.sum_sum_type, Fin.sum_univ_three, Finset.univ_unique, Finset.sum_singleton,
      violDir, hL, crossDir]
    simp [vflux, ξ, aE, aB]
    ring
  have hdens : ∑ j, w j ^ 2 = dens aE aB (w (.inl (.inr ()))) (w (.inr (.inr ()))) := by
    simp [dens, Fintype.sum_sum_type, aE, aB]
    ring
  rw [key, one_mul, hdens]
  have hξ : ∑ c, ξ c ^ 2 ≤ ‖L‖ ^ 2 := sum_sq_le_opNorm_sq L
  exact abs_two_flux_le ξ aE aB _ _ ‖L‖ (norm_nonneg _) hξ

/-! ## The violation fields and their weak curl identities -/

section Static

variable {Ω : Set R3}

/-- Twice the axial vector of the skew part, `a(X)_k = X_{k+1,k+2} - X_{k+2,k+1}`. -/
def axV (X : L2F ℝ Ω Ix) (k : Fin 3) : L2 ℝ Ω := X (k + 1, k + 2) - X (k + 2, k + 1)

/-- The trace `τ(X) = Σᵢ X_{ii}`. -/
def trV (X : L2F ℝ Ω Ix) : L2 ℝ Ω := ∑ i, X (i, i)

/-- `X` is symmetric and trace-free iff `a(X) = 0` and `τ(X) = 0`. -/
theorem symm_trace_iff (X : L2F ℝ Ω Ix) :
    ((∀ i j, X (i, j) = X (j, i)) ∧ ∑ i, X (i, i) = 0) ↔ (∀ k, axV X k = 0) ∧ trV X = 0 := by
  refine ⟨fun ⟨h1, h2⟩ => ⟨fun k => by simp [axV, h1 (k + 1)], h2⟩, fun ⟨h1, h2⟩ => ⟨?_, h2⟩⟩
  have e0 : X (1, 2) = X (2, 1) := sub_eq_zero.1 (h1 0)
  have e1 : X (2, 0) = X (0, 2) := sub_eq_zero.1 (h1 1)
  have e2 : X (0, 1) = X (1, 0) := sub_eq_zero.1 (h1 2)
  intro i j
  fin_cases i <;> fin_cases j <;> simp [e0, e1, e2]

theorem axV_trV_eq_zero_of_mem_tsd {X : L2F ℝ Ω Ix} (hX : X ∈ tsd Ω) :
    (∀ k, axV X k = 0) ∧ trV X = 0 :=
  (symm_trace_iff X).1 ⟨hX.1, hX.2.1⟩

/-- Coefficient test fields `Φ_{ij} = c_{ij} ψ`. -/
def cT (c : Ix → ℝ) (ψ : R3 → ℝ) : Ix → R3 → ℝ := fun ij x => c ij * ψ x

/-- Coefficients of `ψ I` (pairing with the trace). -/
def cTr : Ix → ℝ := fun ij => if ij.1 = ij.2 then 1 else 0

/-- Coefficients of `ψ ε_{k··}` (pairing with `a_k`). -/
def cAx (k : Fin 3) : Ix → ℝ := fun ij =>
  (if ij = (k + 1, k + 2) then 1 else 0) - (if ij = (k + 2, k + 1) then 1 else 0)

theorem isTestField_cT (c : Ix → ℝ) {ψ : R3 → ℝ} (hψ : IsTest Ω ψ) : IsTestField Ω (cT c ψ) :=
  fun ij => hψ.const_mul (c ij)

theorem isTestField_curlM {Φ : Ix → R3 → ℝ} (hΦ : IsTestField Ω Φ) :
    IsTestField Ω (curlM Φ) := fun _ =>
  ((hΦ _).fderiv_apply _).sub ((hΦ _).fderiv_apply _)

theorem isTestField_gradM {φ : Fin 3 → R3 → ℝ} (hφ : IsTestField Ω φ) :
    IsTestField Ω (gradM φ) := fun _ => (hφ _).fderiv_apply _

theorem curlM_cT (c : Ix → ℝ) {ψ : R3 → ℝ} (hψ : Differentiable ℝ ψ) (ab : Ix) (x : R3) :
    curlM (cT c ψ) ab x = c (ab.1, ab.2 + 2) * pd (ab.2 + 1) ψ x -
      c (ab.1, ab.2 + 1) * pd (ab.2 + 2) ψ x := by
  unfold curlM cT
  rw [pd_const_mul hψ, pd_const_mul hψ]

/-- `∫ Y (c f - d g) = c ∫ Y f - d ∫ Y g`. -/
theorem integral_mul_sub_mul (Y : L2 ℝ Ω) {f g : R3 → ℝ} (hf : MemLp f 2 (volume.restrict Ω))
    (hg : MemLp g 2 (volume.restrict Ω)) (c d : ℝ) :
    ∫ x, Y x * (c * f x - d * g x) ∂volume.restrict Ω =
      c * ∫ x, Y x * f x ∂volume.restrict Ω - d * ∫ x, Y x * g x ∂volume.restrict Ω := by
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_sub ((integrable_mul Y hf).const_mul c) ((integrable_mul Y hg).const_mul d)]
  congr 1; ext x; ring

theorem sum_integral_cT (X : L2F ℝ Ω Ix) (c : Ix → ℝ) (ψ : R3 → ℝ) :
    ∑ ij, ∫ x, X ij x * cT c ψ ij x ∂volume.restrict Ω =
      ∑ ij, c ij * ∫ x, X ij x * ψ x ∂volume.restrict Ω := by
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [← integral_const_mul]
  congr 1; ext x; simp only [cT]; ring

/-- `∫ τ(X) ψ = ⟨X, ψ I⟩`. -/
theorem integral_trV (X : L2F ℝ Ω Ix) {ψ : R3 → ℝ} (hψ : MemLp ψ 2 (volume.restrict Ω)) :
    ∫ x, trV X x * ψ x ∂volume.restrict Ω =
      ∑ ij, ∫ x, X ij x * cT cTr ψ ij x ∂volume.restrict Ω := by
  rw [sum_integral_cT, integral_mul_eq_inner _ hψ, trV, sum_inner]
  simp only [← integral_mul_eq_inner _ hψ, cTr, Fintype.sum_prod_type, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- `∫ a(X)_k ψ = ⟨X, ψ ε_{k··}⟩`. -/
theorem integral_axV (X : L2F ℝ Ω Ix) (k : Fin 3) {ψ : R3 → ℝ}
    (hψ : MemLp ψ 2 (volume.restrict Ω)) :
    ∫ x, axV X k x * ψ x ∂volume.restrict Ω =
      ∑ ij, ∫ x, X ij x * cT (cAx k) ψ ij x ∂volume.restrict Ω := by
  rw [sum_integral_cT, integral_mul_eq_inner _ hψ, axV, inner_sub_left,
    ← integral_mul_eq_inner _ hψ, ← integral_mul_eq_inner _ hψ]
  fin_cases k <;> simp [cAx, Fintype.sum_prod_type, Fin.sum_univ_three] <;> ring

theorem integral_axV_mul (Y : L2F ℝ Ω Ix) (k : Fin 3) {f : R3 → ℝ}
    (hf : MemLp f 2 (volume.restrict Ω)) :
    ∫ x, axV Y k x * f x ∂volume.restrict Ω = ∫ x, Y (k + 1, k + 2) x * f x ∂volume.restrict Ω -
      ∫ x, Y (k + 2, k + 1) x * f x ∂volume.restrict Ω := by
  rw [integral_mul_eq_inner _ hf, axV, inner_sub_left, ← integral_mul_eq_inner _ hf,
    ← integral_mul_eq_inner _ hf]

theorem integral_trV_mul (Y : L2F ℝ Ω Ix) {f : R3 → ℝ} (hf : MemLp f 2 (volume.restrict Ω)) :
    ∫ x, trV Y x * f x ∂volume.restrict Ω = ∑ i, ∫ x, Y (i, i) x * f x ∂volume.restrict Ω := by
  rw [integral_mul_eq_inner _ hf, trV, sum_inner]
  simp only [← integral_mul_eq_inner _ hf]

/-- `⟨Y, curl (ψ I)⟩ = ⟨a(Y), ∇ψ⟩` (no condition on `Y`). -/
theorem sum_integral_curlM_cTr (Y : L2F ℝ Ω Ix) {ψ : R3 → ℝ} (hψ : IsTest Ω ψ) :
    ∑ ab, ∫ x, Y ab x * curlM (cT cTr ψ) ab x ∂volume.restrict Ω =
      ∑ c, ∫ x, axV Y c x * pd c ψ x ∂volume.restrict Ω := by
  have hm : ∀ m, MemLp (pd m ψ) 2 (volume.restrict Ω) := fun m =>
    (hψ.fderiv_apply (Pi.single m 1)).memLp
  simp_rw [curlM_cT cTr hψ.differentiable]
  simp only [integral_mul_sub_mul _ (hm _) (hm _), integral_axV_mul _ _ (hm _)]
  simp [Fintype.sum_prod_type, Fin.sum_univ_three, cTr]
  ring

/-- For weakly divergence-free `Y`: `⟨Y, curl (ψ ε_{k··})⟩ = -⟨τ(Y), ∂_k ψ⟩ +
⟨a(Y)_{k+1}, ∂_{k+2} ψ⟩ - ⟨a(Y)_{k+2}, ∂_{k+1} ψ⟩` (the distributional form of
`a(curl Y) = ∇ τ(Y) + curl a(Y)`, Lemma 3.5). -/
theorem sum_integral_curlM_cAx (Y : L2F ℝ Ω Ix)
    (hdiv : ∀ φ : Fin 3 → R3 → ℝ, IsTestField Ω φ →
      ∑ ij : Ix, ∫ x, Y ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Ω = 0)
    (k : Fin 3) {ψ : R3 → ℝ} (hψ : IsTest Ω ψ) :
    ∑ ab, ∫ x, Y ab x * curlM (cT (cAx k) ψ) ab x ∂volume.restrict Ω =
      -∫ x, trV Y x * pd k ψ x ∂volume.restrict Ω +
        ∫ x, axV Y (k + 1) x * pd (k + 2) ψ x ∂volume.restrict Ω -
        ∫ x, axV Y (k + 2) x * pd (k + 1) ψ x ∂volume.restrict Ω := by
  have hm : ∀ m, MemLp (pd m ψ) 2 (volume.restrict Ω) := fun m =>
    (hψ.fderiv_apply (Pi.single m 1)).memLp
  have hφ : IsTestField Ω (fun i => if i = k then ψ else 0) := fun i => by
    show IsTest Ω (if i = k then ψ else 0)
    split_ifs
    exacts [hψ, IsTest.zero]
  have hd := hdiv _ hφ
  simp only [pd_ite_zero, mul_ite, mul_zero] at hd
  simp_rw [curlM_cT (cAx k) hψ.differentiable]
  simp only [integral_mul_sub_mul _ (hm _) (hm _), integral_axV_mul _ _ (hm _),
    integral_trV_mul _ (hm _)]
  fin_cases k <;> simp [Fintype.sum_prod_type, Fin.sum_univ_three, cAx] at hd ⊢ <;> linarith

end Static

/-! ## The interior equations -/

section Weak

variable {Ω : Set R3}

/-- The weak (interior, distributional) content of the reduced system (4.15) on `[0, T]`:
`E, B` continuous, weakly divergence-free **at `t = 0`**, and `Ė = -curl B`, `Ḃ = curl E` tested
against `C_c^∞(Ω; ℝ³ˣ³)`. No boundary condition enters. -/
structure WeakEB (Ω : Set R3) (T : ℝ) (E B : ℝ → L2F ℝ Ω Ix) : Prop where
  contE : ContinuousOn E (Icc 0 T)
  contB : ContinuousOn B (Icc 0 T)
  divE0 : ∀ φ : Fin 3 → R3 → ℝ, IsTestField Ω φ →
    ∑ ij : Ix, ∫ x, E 0 ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Ω = 0
  divB0 : ∀ φ : Fin 3 → R3 → ℝ, IsTestField Ω φ →
    ∑ ij : Ix, ∫ x, B 0 ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Ω = 0
  derivE : ∀ t ∈ Icc 0 T, ∀ Φ : Ix → R3 → ℝ, IsTestField Ω Φ →
    HasDerivWithinAt (fun s => ∑ ij, ∫ x, E s ij x * Φ ij x ∂volume.restrict Ω)
      (-∑ ij, ∫ x, B t ij x * curlM Φ ij x ∂volume.restrict Ω) (Icc 0 T) t
  derivB : ∀ t ∈ Icc 0 T, ∀ Φ : Ix → R3 → ℝ, IsTestField Ω Φ →
    HasDerivWithinAt (fun s => ∑ ij, ∫ x, B s ij x * Φ ij x ∂volume.restrict Ω)
      (∑ ij, ∫ x, E t ij x * curlM Φ ij x ∂volume.restrict Ω) (Icc 0 T) t

/-- A function on `[0, T]` with zero derivative is constant. -/
theorem eq_zero_sub_of_hasDerivWithinAt_zero {f : ℝ → ℝ} {T : ℝ}
    (hd : ∀ s ∈ Icc 0 T, HasDerivWithinAt f 0 (Icc 0 T) s) : ∀ t ∈ Icc 0 T, f t = f 0 :=
  constant_of_has_deriv_right_zero (fun s hs => (hd s hs).continuousWithinAt) fun s hs =>
    (hd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs)

/-- `div E` is conserved: testing `Ė = -curl B` against `∇φ` and `curl ∇φ = 0`. -/
theorem WeakEB.divE {T : ℝ} {E B : ℝ → L2F ℝ Ω Ix} (h : WeakEB Ω T E B) :
    ∀ t ∈ Icc 0 T, ∀ φ : Fin 3 → R3 → ℝ, IsTestField Ω φ →
      ∑ ij : Ix, ∫ x, E t ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Ω = 0 := by
  intro t ht φ hφ
  have hc := eq_zero_sub_of_hasDerivWithinAt_zero (T := T)
    (f := fun s => ∑ ij, ∫ x, E s ij x * gradM φ ij x ∂volume.restrict Ω) (fun s hs => by
      refine (h.derivE s hs _ (isTestField_gradM hφ)).congr_deriv ?_
      rw [neg_eq_zero]
      refine Finset.sum_eq_zero fun ij _ => ?_
      simp [curlM_gradM fun i => (hφ i).contDiff.of_le (by simp)]) t ht
  simp only [gradM] at hc
  rw [hc]
  exact h.divE0 φ hφ

/-- `div B` is conserved: `∂ₜ ⟨B, ∇φ⟩ = ⟨E, curl ∇φ⟩ = 0`. -/
theorem WeakEB.divB {T : ℝ} {E B : ℝ → L2F ℝ Ω Ix} (h : WeakEB Ω T E B) :
    ∀ t ∈ Icc 0 T, ∀ φ : Fin 3 → R3 → ℝ, IsTestField Ω φ →
      ∑ ij : Ix, ∫ x, B t ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Ω = 0 := by
  intro t ht φ hφ
  have hc := eq_zero_sub_of_hasDerivWithinAt_zero (T := T)
    (f := fun s => ∑ ij, ∫ x, B s ij x * gradM φ ij x ∂volume.restrict Ω) (fun s hs => by
      refine (h.derivB s hs _ (isTestField_gradM hφ)).congr_deriv ?_
      refine Finset.sum_eq_zero fun ij _ => ?_
      simp [curlM_gradM fun i => (hφ i).contDiff.of_le (by simp)]) t ht
  simp only [gradM] at hc
  rw [hc]
  exact h.divB0 φ hφ

/-! ### The weak violation system -/

variable {T : ℝ} {E B : ℝ → L2F ℝ Ω Ix}

theorem WeakEB.deriv_axE (h : WeakEB Ω T E B) {t : ℝ} (ht : t ∈ Icc 0 T) (k : Fin 3)
    {ψ : R3 → ℝ} (hψ : IsTest Ω ψ) :
    HasDerivWithinAt (fun s => ∫ x, axV (E s) k x * ψ x ∂volume.restrict Ω)
      (∫ x, trV (B t) x * pd k ψ x ∂volume.restrict Ω -
        ∫ x, axV (B t) (k + 1) x * pd (k + 2) ψ x ∂volume.restrict Ω +
        ∫ x, axV (B t) (k + 2) x * pd (k + 1) ψ x ∂volume.restrict Ω) (Icc 0 T) t := by
  simp_rw [integral_axV _ k hψ.memLp]
  refine (h.derivE t ht _ (isTestField_cT (cAx k) hψ)).congr_deriv ?_
  rw [sum_integral_curlM_cAx _ (h.divB t ht) k hψ]
  ring

theorem WeakEB.deriv_trE (h : WeakEB Ω T E B) {t : ℝ} (ht : t ∈ Icc 0 T)
    {ψ : R3 → ℝ} (hψ : IsTest Ω ψ) :
    HasDerivWithinAt (fun s => ∫ x, trV (E s) x * ψ x ∂volume.restrict Ω)
      (-∑ c, ∫ x, axV (B t) c x * pd c ψ x ∂volume.restrict Ω) (Icc 0 T) t := by
  simp_rw [integral_trV _ hψ.memLp]
  refine (h.derivE t ht _ (isTestField_cT cTr hψ)).congr_deriv ?_
  rw [sum_integral_curlM_cTr _ hψ]

theorem WeakEB.deriv_axB (h : WeakEB Ω T E B) {t : ℝ} (ht : t ∈ Icc 0 T) (k : Fin 3)
    {ψ : R3 → ℝ} (hψ : IsTest Ω ψ) :
    HasDerivWithinAt (fun s => ∫ x, axV (B s) k x * ψ x ∂volume.restrict Ω)
      (-∫ x, trV (E t) x * pd k ψ x ∂volume.restrict Ω +
        ∫ x, axV (E t) (k + 1) x * pd (k + 2) ψ x ∂volume.restrict Ω -
        ∫ x, axV (E t) (k + 2) x * pd (k + 1) ψ x ∂volume.restrict Ω) (Icc 0 T) t := by
  simp_rw [integral_axV _ k hψ.memLp]
  refine (h.derivB t ht _ (isTestField_cT (cAx k) hψ)).congr_deriv ?_
  rw [sum_integral_curlM_cAx _ (h.divE t ht) k hψ]

theorem WeakEB.deriv_trB (h : WeakEB Ω T E B) {t : ℝ} (ht : t ∈ Icc 0 T)
    {ψ : R3 → ℝ} (hψ : IsTest Ω ψ) :
    HasDerivWithinAt (fun s => ∫ x, trV (B s) x * ψ x ∂volume.restrict Ω)
      (∑ c, ∫ x, axV (E t) c x * pd c ψ x ∂volume.restrict Ω) (Icc 0 T) t := by
  simp_rw [integral_trV _ hψ.memLp]
  refine (h.derivB t ht _ (isTestField_cT cTr hψ)).congr_deriv ?_
  rw [sum_integral_curlM_cTr _ hψ]

end Weak

/-! ## The violation is a weak solution of a symmetric hyperbolic system -/

section Violation

variable {Ω : Set R3}

/-- The violation `W = (a(E), τ(E), a(B), τ(B))` of a pair `(E, B)`. -/
def viol (E B : L2F ℝ Ω Ix) : L2F ℝ Ω VIdx :=
  WithLp.toLp 2 fun j => match j with
    | .inl (.inl k) => axV E k
    | .inl (.inr _) => trV E
    | .inr (.inl k) => axV B k
    | .inr (.inr _) => trV B

@[simp] theorem viol_aE (E B : L2F ℝ Ω Ix) (k : Fin 3) : viol E B (.inl (.inl k)) = axV E k := rfl
@[simp] theorem viol_tE (E B : L2F ℝ Ω Ix) (u : Unit) : viol E B (.inl (.inr u)) = trV E := rfl
@[simp] theorem viol_aB (E B : L2F ℝ Ω Ix) (k : Fin 3) : viol E B (.inr (.inl k)) = axV B k := rfl
@[simp] theorem viol_tB (E B : L2F ℝ Ω Ix) (u : Unit) : viol E B (.inr (.inr u)) = trV B := rfl

theorem continuous_axV (k : Fin 3) : Continuous fun X : L2F ℝ Ω Ix => axV X k :=
  (L2F.continuous_apply _).sub (L2F.continuous_apply _)

theorem continuous_trV : Continuous fun X : L2F ℝ Ω Ix => trV X :=
  continuous_finsetSum _ fun _ _ => L2F.continuous_apply _

theorem continuous_viol : Continuous fun p : L2F ℝ Ω Ix × L2F ℝ Ω Ix => viol p.1 p.2 := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
  rcases j with (k | _) | (k | _)
  · exact (continuous_axV k).comp continuous_fst
  · exact continuous_trV.comp continuous_fst
  · exact (continuous_axV k).comp continuous_snd
  · exact continuous_trV.comp continuous_snd

/-- Directional derivatives in the pairing: `∫ u ∂_v g = Σ_c v_c ∫ u ∂_c g`. -/
theorem integral_mul_fderiv (u : L2 ℝ Ω) {g : R3 → ℝ} (hg : IsTest Ω g) (v : R3) :
    ∫ x, u x * fderiv ℝ g x v ∂volume.restrict Ω =
      ∑ c, v c * ∫ x, u x * pd c g x ∂volume.restrict Ω := by
  have hv : ∀ x, fderiv ℝ g x v = ∑ c, v c * pd c g x := fun x => by
    have e : v = ∑ c, v c • (Pi.single c 1 : R3) := by
      funext i; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [e]
    simp [map_sum, map_smul, pd]
  simp only [hv, Finset.mul_sum]
  rw [integral_finsetSum _ fun c _ => ?_]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [← integral_const_mul]
    congr 1; ext x; ring
  · exact (integrable_mul u (hg.fderiv_apply (Pi.single c 1)).memLp).const_mul (v c) |>.congr
      (Eventually.of_forall fun x => by simp only [pd]; ring)

/-- The time derivative of `∫ Wⱼ ψⱼ` along the interior equations. -/
def violDeriv (E B : L2F ℝ Ω Ix) (ψ : VIdx → R3 → ℝ) : VIdx → ℝ
  | Sum.inl (Sum.inl k) => ∫ x, trV B x * pd k (ψ (.inl (.inl k))) x ∂volume.restrict Ω -
      ∫ x, axV B (k + 1) x * pd (k + 2) (ψ (.inl (.inl k))) x ∂volume.restrict Ω +
      ∫ x, axV B (k + 2) x * pd (k + 1) (ψ (.inl (.inl k))) x ∂volume.restrict Ω
  | Sum.inl (Sum.inr u) => -∑ c, ∫ x, axV B c x * pd c (ψ (.inl (.inr u))) x ∂volume.restrict Ω
  | Sum.inr (Sum.inl k) => -∫ x, trV E x * pd k (ψ (.inr (.inl k))) x ∂volume.restrict Ω +
      ∫ x, axV E (k + 1) x * pd (k + 2) (ψ (.inr (.inl k))) x ∂volume.restrict Ω -
      ∫ x, axV E (k + 2) x * pd (k + 1) (ψ (.inr (.inl k))) x ∂volume.restrict Ω
  | Sum.inr (Sum.inr u) => ∑ c, ∫ x, axV E c x * pd c (ψ (.inr (.inr u))) x ∂volume.restrict Ω

/-- **The violation solves the violation system weakly** (any open `Ω`, no boundary
condition). -/
theorem WeakEB.isWeakSolution_viol {T : ℝ} {E B : ℝ → L2F ℝ Ω Ix} (h : WeakEB Ω T E B) :
    FiniteSpeed.IsWeakSolution violDir Ω T (fun s => viol (E s) (B s)) := by
  refine ⟨continuous_viol.comp_continuousOn (h.contE.prodMk h.contB), fun t ht ψ hψ => ?_⟩
  have hd : HasDerivWithinAt (fun s => ∑ j, ∫ x, viol (E s) (B s) j x * ψ j x ∂volume.restrict Ω)
      (∑ j, violDeriv (E t) (B t) ψ j) (Icc 0 T) t := by
    refine HasDerivWithinAt.fun_sum fun j _ => ?_
    rcases j with (k | u) | (k | u)
    · exact h.deriv_axE ht k (hψ _)
    · exact h.deriv_trE ht (hψ _)
    · exact h.deriv_axB ht k (hψ _)
    · exact h.deriv_trB ht (hψ _)
  simp only [inner_testField_eq]
  convert hd using 1
  -- the right-hand side `⟪W, Pᵗ ψ⟫`
  have hP : ∀ i x, (FiniteSpeed.hypOp violDir).formalAdj.apply ψ i x =
      -∑ j, fderiv ℝ (ψ j) x (violDir j i) := fun i x =>
    FiniteSpeed.hypOp_formalAdj_apply _ _ _ _
  have hsplit : ∀ i, ∫ x, viol (E t) (B t) i x *
      (FiniteSpeed.hypOp violDir).formalAdj.apply ψ i x ∂volume.restrict Ω =
      -∑ j, ∑ c, violDir j i c * ∫ x, viol (E t) (B t) i x * pd c (ψ j) x ∂volume.restrict Ω := by
    intro i
    simp only [hP, mul_neg, integral_neg, Finset.mul_sum]
    rw [integral_finsetSum _ fun j _ => integrable_mul _ ((hψ j).fderiv_apply _).memLp]
    simp only [integral_mul_fderiv _ (hψ _)]
  simp only [hsplit]
  simp [Fintype.sum_sum_type, Fin.sum_univ_three, violDir, violDeriv, crossDir, Pi.single_apply]
  ring

end Violation

/-! ## Finite speed: the violation vanishes on the domain of dependence -/

section Cone

variable {Ω : Set R3} {T : ℝ} {E B : ℝ → L2F ℝ Ω Ix}

/-- **Interior TSD propagation in the `L²` setting of `WeakEB`** (any open `Ω`, no boundary
condition, no boundedness): if the violation vanishes at `t = 0` and the Euclidean ball
`{|z - x| < r}` lies in `Ω`, then at time `t ∈ [0, T]` the violation vanishes a.e. on
`{|y - x| < r - t}`. -/
theorem WeakEB.ae_viol_eq_zero (hΩ : IsOpen Ω) (h : WeakEB Ω T E B)
    (h0 : viol (E 0) (B 0) = 0) {x : R3} {r : ℝ} (hr : ∀ z, dist (euc z) (euc x) < r → z ∈ Ω)
    {t : ℝ} (ht : t ∈ Icc 0 T) (j : VIdx) :
    ∀ᵐ y ∂volume.restrict {y | dist (euc y) (euc x) < r - t}, viol (E t) (B t) j y = 0 := by
  have hz : ∀ i, ∀ᵐ y ∂volume.restrict (euc ⁻¹' Metric.ball (euc x) r),
      viol (E 0) (B 0) i y = 0 := fun i => by
    rw [h0, PiLp.zero_apply]
    exact ae_restrict_of_ae_restrict_of_subset (fun z hz => hr z hz)
      ((Lp.coeFn_zero ℝ 2 (volume.restrict Ω)).mono fun x hx => hx)
  have := h.isWeakSolution_viol.ae_eq_zero_of_preimage_ball euc measurePreserving_euc
    measurePreserving_euc_symm isSymmHyperbolic_violDir hΩ (x := x) (R := r)
    (fun z hz => hr z hz) hz ht j
  simpa [Metric.ball, one_mul] using this

/-- The **domain of dependence** of `Ω` at time `t`: the points whose Euclidean distance to
`ℝ³ \ Ω` exceeds `t`. -/
def depDomain (Ω : Set R3) (t : ℝ) : Set R3 :=
  {y | ∃ r, t < r ∧ ∀ z, dist (euc z) (euc y) < r → z ∈ Ω}

theorem depDomain_subset {t : ℝ} (ht : 0 ≤ t) : depDomain Ω t ⊆ Ω := fun y ⟨r, htr, h⟩ =>
  h y (by rw [dist_self]; linarith)

theorem isOpen_ball_euc (x : R3) (r : ℝ) : IsOpen {y | dist (euc y) (euc x) < r} :=
  isOpen_lt (euc.continuous.dist continuous_const) continuous_const

/-- `depDomain Ω t` is the union of the cones `{|y - x| < r - t}` of the Euclidean balls
`{|z - x| < r} ⊆ Ω`. -/
theorem depDomain_eq_iUnion (t : ℝ) :
    depDomain Ω t = ⋃ p : {p : R3 × ℝ // ∀ z, dist (euc z) (euc p.1) < p.2 → z ∈ Ω},
      {y | dist (euc y) (euc p.1.1) < p.1.2 - t} := by
  ext y
  simp only [depDomain, mem_iUnion, mem_ofPred_eq, Subtype.exists, Prod.exists]
  constructor
  · rintro ⟨r, htr, h⟩
    exact ⟨y, r, h, by rw [dist_self]; linarith⟩
  · rintro ⟨q, r, h, hy⟩
    refine ⟨r - dist (euc y) (euc q), by linarith, fun z hz => h z ?_⟩
    linarith [dist_triangle (euc z) (euc y) (euc q)]

theorem isOpen_depDomain (t : ℝ) : IsOpen (depDomain Ω t) := by
  rw [depDomain_eq_iUnion]
  exact isOpen_iUnion fun p => isOpen_ball_euc _ _

theorem measurableSet_depDomain (t : ℝ) : MeasurableSet (depDomain Ω t) :=
  (isOpen_depDomain t).measurableSet

/-- **Interior finite speed of propagation on an arbitrary open `Ω ⊆ ℝ³`**: under `WeakEB` with
vanishing initial violation, the violation vanishes a.e. on `depDomain Ω t`. -/
theorem WeakEB.ae_viol_eq_zero_depDomain (hΩ : IsOpen Ω) (h : WeakEB Ω T E B)
    (h0 : viol (E 0) (B 0) = 0) {t : ℝ} (ht : t ∈ Icc 0 T) (j : VIdx) :
    ∀ᵐ y ∂volume.restrict (depDomain Ω t), viol (E t) (B t) j y = 0 := by
  set s : {p : R3 × ℝ // ∀ z, dist (euc z) (euc p.1) < p.2 → z ∈ Ω} → Set R3 :=
    fun p => {y | dist (euc y) (euc p.1.1) < p.1.2 - t}
  obtain ⟨I, hI, hIU⟩ := TopologicalSpace.isOpen_iUnion_countable s
    fun p => isOpen_ball_euc _ _
  rw [depDomain_eq_iUnion, ← hIU, ae_restrict_biUnion_iff _ hI]
  intro p _
  exact h.ae_viol_eq_zero hΩ h0 p.2 ht j

end Cone

/-! ## Symmetric trace-free fields -/

section SymTF

variable {Ω : Set R3}

/-- `X(y)` is symmetric and trace-free (pointwise, for the chosen representatives). -/
def SymTF (X : L2F ℝ Ω Ix) (y : R3) : Prop :=
  (∀ i j, X (i, j) y = X (j, i) y) ∧ ∑ i, X (i, i) y = 0

theorem ae_symTF_of_viol (X : L2F ℝ Ω Ix) {S : Set R3} (hSΩ : S ⊆ Ω)
    (h : ∀ᵐ y ∂volume.restrict S, (∀ k, axV X k y = 0) ∧ trV X y = 0) :
    ∀ᵐ y ∂volume.restrict S, SymTF X y := by
  have ha : ∀ k, ∀ᵐ y ∂volume.restrict S, axV X k y = X (k + 1, k + 2) y - X (k + 2, k + 1) y :=
    fun k => ae_restrict_of_ae_restrict_of_subset hSΩ (Lp.coeFn_sub _ _)
  have ht : ∀ᵐ y ∂volume.restrict S, trV X y = X (0, 0) y + X (1, 1) y + X (2, 2) y := by
    have e : trV X = X (0, 0) + X (1, 1) + X (2, 2) := by simp [trV, Fin.sum_univ_three]
    rw [e]
    refine ae_restrict_of_ae_restrict_of_subset hSΩ ?_
    filter_upwards [Lp.coeFn_add (X (0, 0) + X (1, 1)) (X (2, 2)),
      Lp.coeFn_add (X (0, 0)) (X (1, 1))] with y h1 h2
    rw [h1, Pi.add_apply, h2, Pi.add_apply]
  filter_upwards [h, ae_all_iff.2 ha, ht] with y ⟨h1, h2⟩ h3 h4
  have e0 := (h3 0).symm.trans (h1 0)
  have e1 := (h3 1).symm.trans (h1 1)
  have e2 := (h3 2).symm.trans (h1 2)
  simp only [Fin.isValue, Fin.reduceAdd] at e0 e1 e2
  refine ⟨fun i j => ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp <;> linarith
  · rw [Fin.sum_univ_three, ← h4, h2]

/-- A.e. symmetric and trace-free on `Ω` plus weakly divergence-free gives `L²(TSD)`. -/
theorem mem_tsd_of_ae_symTF {X : L2F ℝ Ω Ix} (hX : ∀ᵐ y ∂volume.restrict Ω, SymTF X y)
    (hd : ∀ φ : Fin 3 → R3 → ℝ, IsTestField Ω φ →
      ∑ ij : Ix, ∫ x, X ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Ω = 0) : X ∈ tsd Ω := by
  refine ⟨fun i j => Lp.ext ?_, ?_, fun φ hφ => by rw [inner_grad_testField _ hφ]; exact hd φ hφ⟩
  · filter_upwards [hX] with y hy using hy.1 i j
  · have e : ∑ i, X (i, i) = X (0, 0) + X (1, 1) + X (2, 2) := by simp [Fin.sum_univ_three]
    rw [e]
    refine Lp.ext ?_
    filter_upwards [hX, Lp.coeFn_add (X (0, 0) + X (1, 1)) (X (2, 2)),
      Lp.coeFn_add (X (0, 0)) (X (1, 1)), Lp.coeFn_zero ℝ 2 (volume.restrict Ω)]
      with y hy h1 h2 h3
    rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, Pi.zero_apply, ← hy.2, Fin.sum_univ_three]

theorem viol_eq_zero_of_mem_tsd {E B : L2F ℝ Ω Ix} (hE : E ∈ tsd Ω) (hB : B ∈ tsd Ω) :
    viol E B = 0 := by
  obtain ⟨hE1, hE2⟩ := axV_trV_eq_zero_of_mem_tsd hE
  obtain ⟨hB1, hB2⟩ := axV_trV_eq_zero_of_mem_tsd hB
  refine PiLp.ext fun j => ?_
  rcases j with (k | _) | (k | _) <;> simp [hE1, hE2, hB1, hB2]

variable {T : ℝ} {E B : ℝ → L2F ℝ Ω Ix}

/-- Under `WeakEB` with TSD-violation-free data, `E(t)`, `B(t)` are symmetric and trace-free a.e.
on the domain of dependence. -/
theorem WeakEB.ae_symTF_depDomain (hΩ : IsOpen Ω) (h : WeakEB Ω T E B)
    (h0 : viol (E 0) (B 0) = 0) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∀ᵐ y ∂volume.restrict (depDomain Ω t), SymTF (E t) y ∧ SymTF (B t) y := by
  have hv := fun j => h.ae_viol_eq_zero_depDomain hΩ h0 ht j
  have hS := depDomain_subset (Ω := Ω) ht.1
  have h1 := ae_symTF_of_viol (E t) hS (by
    filter_upwards [ae_all_iff.2 fun k => hv (.inl (.inl k)), hv (.inl (.inr ()))] with y h1 h2
    exact ⟨fun k => by simpa using h1 k, by simpa using h2⟩)
  have h2 := ae_symTF_of_viol (B t) hS (by
    filter_upwards [ae_all_iff.2 fun k => hv (.inr (.inl k)), hv (.inr (.inr ()))] with y h1 h2
    exact ⟨fun k => by simpa using h1 k, by simpa using h2⟩)
  filter_upwards [h1, h2] with y h1 h2 using ⟨h1, h2⟩

theorem depDomain_univ (t : ℝ) : depDomain (univ : Set R3) t = univ :=
  eq_univ_of_forall fun _ => ⟨t + 1, by linarith, fun _ _ => mem_univ _⟩

/-- **TSD propagation on `ℝ³`**: if `E, B` satisfy the weak equations `WeakEB` on `Ω = ℝ³` and
`E(0), B(0) ∈ L²(TSD)`, then `E(t), B(t) ∈ L²(TSD)` for all `t ∈ [0, T]`: divergence-freeness is
conserved, symmetry and trace-freeness propagate by finite speed (the domain of dependence of
`ℝ³` is `ℝ³`). The solution is assumed, not constructed. Thesis: Prop 4.17 -/
theorem WeakEB.mem_tsd_univ {E B : ℝ → L2F ℝ (univ : Set R3) Ix} (h : WeakEB univ T E B)
    (hE₀ : E 0 ∈ tsd univ) (hB₀ : B 0 ∈ tsd univ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    E t ∈ tsd univ ∧ B t ∈ tsd univ := by
  have hs := h.ae_symTF_depDomain isOpen_univ (viol_eq_zero_of_mem_tsd hE₀ hB₀) ht
  rw [depDomain_univ] at hs
  exact ⟨mem_tsd_of_ae_symTF (hs.mono fun y hy => hy.1) (h.divE t ht),
    mem_tsd_of_ae_symTF (hs.mono fun y hy => hy.2) (h.divB t ht)⟩

end SymTF

/-! ## Strong solutions of the Hodge wave equation of the grad–curl complex -/

section Strong

-- Over `ℝ` the generic real structure on the window spaces duplicates the inner-product one.
attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

variable {Ω : Set R3}

/-- Weakly divergence-free fields are the kernel of `d₀†`. -/
theorem weakDiv_eq_zero_of_mem_ker (hΩ : IsOpen Ω) {X : L2F ℝ Ω Ix}
    (hX : X ∈ (gradCurl ℝ hΩ).d₀†.ker) (φ : Fin 3 → R3 → ℝ) (hφ : IsTestField Ω φ) :
    ∑ ij : Ix, ∫ x, X ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Ω = 0 := by
  rw [← inner_grad_testField _ hφ]
  obtain ⟨y, rfl, hy⟩ := LinearPMap.mem_ker_iff.1 hX
  rw [← (gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).adjoint_minimal_inner_testField hΩ y hφ]
  erw [hy]
  exact inner_zero_left _

/-- Conversely, weakly divergence-free fields lie in `N(d₀†)`. -/
theorem mem_ker_of_weakDiv_eq_zero (hΩ : IsOpen Ω) {X : L2F ℝ Ω Ix}
    (hX : ∀ φ : Fin 3 → R3 → ℝ, IsTestField Ω φ →
      ∑ ij : Ix, ∫ x, X ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Ω = 0) :
    X ∈ (gradCurl ℝ hΩ).d₀†.ker := by
  have h : ∀ (φ : Fin 3 → R3 → ℝ) (hφ : IsTestField Ω φ),
      ⟪X, testField ((gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).isTestField_apply hφ)⟫_ℝ = 0 :=
    fun φ hφ => by rw [inner_grad_testField _ hφ]; exact hX φ hφ
  rw [LinearPMap.mem_ker_iff]
  have hmem := ((gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).mem_adjoint_minimal_domain_iff hΩ).2
    ⟨0, fun φ hφ => by rw [inner_zero_left, h φ hφ]⟩
  exact ⟨⟨X, hmem⟩, rfl, (gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).adjoint_minimal_apply_eq hΩ _
    fun φ hφ => by rw [inner_zero_left, h φ hφ]⟩

/-- The window of `(σ, E, B)`. -/
abbrev Win (Ω : Set R3) := PiLp 2 (ShortHilbertComplex.W3 (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix)
  (L2F ℝ Ω Ix))

/-- The scalar potential `σ` of `(σ, E, B)`. -/
def winσ (u : Win Ω) : L2F ℝ Ω (Fin 3) := u 0

/-- The electric field `E` of `(σ, E, B)`. -/
def winE (u : Win Ω) : L2F ℝ Ω Ix := u 1

/-- The magnetic field `B` of `(σ, E, B)`. -/
def winB (u : Win Ω) : L2F ℝ Ω Ix := u 2

/-- **Strong solutions with divergence-free data satisfy the interior equations.** For a strong
solution of `U' = L U` of the grad–curl complex from `(0, E₀, B₀)` with `E₀, B₀` weakly
divergence-free: `σ ≡ 0` and `E ∈ N(d₀†)` (Prop 4.16, `divFree_propagates`), and `(E, B)`
satisfies `WeakEB` (`wave_apply_one`, `wave_apply_two`; test fields lie in `D(d₁) = H̊(curl)` and
`d₁†` extends the classical curl). No boundedness of `Ω` is needed. -/
theorem weakEB_of_isStrongSolution (hΩ : IsOpen Ω) {T : ℝ} {U : ℝ → Win Ω}
    (hU : Evolution.IsStrongSolution (gradCurl ℝ hΩ).wave (Icc 0 T) 0 U)
    (h0 : winσ (U 0) = 0)
    (hE₀ : winE (U 0) ∈ (gradCurl ℝ hΩ).d₀†.ker)
    (hB₀ : winB (U 0) ∈ (gradCurl ℝ hΩ).d₀†.ker) :
    (∀ t ∈ Icc 0 T, winσ (U t) = 0 ∧
        winE (U t) ∈ (gradCurl ℝ hΩ).d₀†.ker) ∧
      WeakEB Ω T (fun t => winE (U t)) (fun t => winB (U t)) := by
  set S := gradCurl ℝ hΩ
  have hred := S.reducingSubcomplex_divFreeSub (⊤ : Submodule ℝ (L2F ℝ Ω Ix))
    (fun _ => Submodule.mem_top)
  have hU0 : U 0 ∈ HilbertComplex.totalSub (S.divFreeSub ⊤) := by
    intro i
    match i with
    | 0 => exact (Submodule.mem_bot ℝ (M := L2F ℝ Ω (Fin 3))).2 h0
    | 1 => exact hE₀
    | 2 => exact (Submodule.mem_top : winB (U 0) ∈ (⊤ : Submodule ℝ (L2F ℝ Ω Ix)))
  have hprop := hred.propagates hU hU0 fun _ _ => Submodule.zero_mem _
  have hσ : ∀ t ∈ Icc 0 T, winσ (U t) = 0 ∧
      winE (U t) ∈ S.d₀†.ker := fun t ht =>
    ⟨(Submodule.mem_bot ℝ (M := L2F ℝ Ω (Fin 3))).1 (hprop t ht 0), hprop t ht 1⟩
  refine ⟨hσ, ?_⟩
  have hcont : ∀ i, ContinuousOn (fun t => (U t : Win Ω) i) (Icc 0 T) := fun i =>
    (PiLp.continuous_apply 2 _ i).comp_continuousOn hU.continuousOn
  -- the derivative of a component paired with a fixed field
  have hcomp : ∀ (i : Fin 3) (V : ShortHilbertComplex.W3 (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix)
      (L2F ℝ Ω Ix) i) {t : ℝ} (ht : t ∈ Icc 0 T),
      HasDerivWithinAt (fun s => ⟪V, (U s : Win Ω) i⟫_ℝ)
        ⟪V, (S.wave ⟨U t, hU.mem_domain ht⟩ : Win Ω) i⟫_ℝ (Icc 0 T) t := by
    intro i V t ht
    have := ((innerSL ℝ V).comp (PiLp.proj 2 _ i)).hasFDerivAt.comp_hasDerivWithinAt t
      (hU.hasDerivWithinAt ht)
    simp only [Pi.zero_apply, add_zero] at this
    exact this
  refine ⟨hcont 1, hcont 2, weakDiv_eq_zero_of_mem_ker hΩ hE₀,
    weakDiv_eq_zero_of_mem_ker hΩ hB₀, fun t ht Φ hΦ => ?_, fun t ht Φ hΦ => ?_⟩
  · have hd := hcomp 1 (testField hΦ) ht
    have e1 : (fun s => ∑ ij, ∫ x, winE (U s) ij x * Φ ij x ∂volume.restrict Ω) =
        fun s => ⟪testField hΦ, winE (U s)⟫_ℝ := funext fun s => by
      rw [real_inner_comm, inner_testField_eq]
    rw [e1]
    refine hd.congr_deriv ?_
    have hx := hU.mem_domain ht
    change ⟪testField hΦ, ((S.wave ⟨U t, hx⟩ : Win Ω) 1 : L2F ℝ Ω Ix)⟫_ℝ = _
    rw [S.wave_apply_one]
    have e0 : S.d₀ ⟨winσ (U t), hx.1 0 1⟩ = 0 := by
      have : (⟨winσ (U t), hx.1 0 1⟩ : S.d₀.domain) = 0 :=
        Subtype.ext (hσ t ht).1
      rw [this, LinearPMap.map_zero]
    erw [e0]
    rw [zero_sub, inner_neg_right, real_inner_comm,
      LinearPMap.adjoint_isFormalAdjoint S.dense₁ _
        ⟨_, (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).testField_mem_minimal_domain hΩ hΦ⟩]
    change -⟪winB (U t),
      (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω
        ⟨_, (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).testField_mem_minimal_domain hΩ hΦ⟩⟫_ℝ = _
    rw [(curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal_testField hΩ hΦ, inner_testField_eq]
    simp only [← curlM_eq_apply]
  · have hd := hcomp 2 (testField hΦ) ht
    have e1 : (fun s => ∑ ij, ∫ x, winB (U s) ij x * Φ ij x ∂volume.restrict Ω) =
        fun s => ⟪testField hΦ, winB (U s)⟫_ℝ := funext fun s => by
      rw [real_inner_comm, inner_testField_eq]
    rw [e1]
    refine hd.congr_deriv ?_
    have hx := hU.mem_domain ht
    change ⟪testField hΦ, ((S.wave ⟨U t, hx⟩ : Win Ω) 2 : L2F ℝ Ω Ix)⟫_ℝ = _
    rw [S.wave_apply_two, real_inner_comm]
    have := (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).closure_testGraph_inner_testField
      ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).mem_closure_minimal hΩ
        ⟨winE (U t), hx.1 1 2⟩) hΦ
    change ⟪(curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω ⟨_, hx.1 1 2⟩, testField hΦ⟫_ℝ = _
    erw [this]
    rw [inner_testField_eq]
    simp only [← curlM_eq_formalAdj_apply]

/-- **Interior TSD propagation (finite speed) for the Hodge wave equation of the grad–curl
complex** on an open `Ω ⊆ ℝ³` (bounded or not): for a strong solution from TSD data
`(0, E₀, B₀)` and every Euclidean ball `{|z - x| < r} ⊆ Ω`, at time `t ∈ [0, T]`: `σ(t) = 0`,
`E(t)`, `B(t)` are weakly divergence-free in `Ω`, and symmetric and trace-free a.e. on
`{|y - x| < r - t}`. Thesis: Prop 4.17 -/
theorem tsd_cone (hΩ : IsOpen Ω) {T : ℝ} {U : ℝ → Win Ω}
    (hU : Evolution.IsStrongSolution (gradCurl ℝ hΩ).wave (Icc 0 T) 0 U)
    (h0 : winσ (U 0) = 0)
    (hE₀ : winE (U 0) ∈ tsd Ω) (hB₀ : winB (U 0) ∈ tsd Ω)
    {x : R3} {r : ℝ} (hr : ∀ z, dist (euc z) (euc x) < r → z ∈ Ω) {t : ℝ} (ht : t ∈ Icc 0 T) :
    winσ (U t) = 0 ∧
      winE (U t) ∈ (gradCurl ℝ hΩ).d₀†.ker ∧
      winB (U t) ∈ (gradCurl ℝ hΩ).d₀†.ker ∧
      ∀ᵐ y ∂volume.restrict {y | dist (euc y) (euc x) < r - t},
        SymTF (winE (U t)) y ∧ SymTF (winB (U t)) y := by
  have hker : ∀ X ∈ tsd Ω, X ∈ (gradCurl ℝ hΩ).d₀†.ker := fun X hX =>
    ((mem_tsd_iff_ker hΩ).1 hX).2.2
  obtain ⟨hσ, hW⟩ := weakEB_of_isStrongSolution hΩ hU h0 (hker _ hE₀) (hker _ hB₀)
  have hv0 := viol_eq_zero_of_mem_tsd hE₀ hB₀
  have hsub : {y | dist (euc y) (euc x) < r - t} ⊆ Ω := fun y hy => hr y (by
    simp only [mem_ofPred_eq] at hy; linarith [ht.1])
  have hv := fun j => hW.ae_viol_eq_zero hΩ hv0 hr ht j
  have h1 := ae_symTF_of_viol _ hsub (by
    filter_upwards [ae_all_iff.2 fun k => hv (.inl (.inl k)), hv (.inl (.inr ()))] with y h1 h2
    exact ⟨fun k => h1 k, h2⟩)
  have h2 := ae_symTF_of_viol _ hsub (by
    filter_upwards [ae_all_iff.2 fun k => hv (.inr (.inl k)), hv (.inr (.inr ()))] with y h1 h2
    exact ⟨fun k => h1 k, h2⟩)
  have hB : winB (U t) ∈ (gradCurl ℝ hΩ).d₀†.ker :=
    mem_ker_of_weakDiv_eq_zero hΩ (hW.divB t ht)
  exact ⟨(hσ t ht).1, (hσ t ht).2, hB, by filter_upwards [h1, h2] with y h1 h2 using ⟨h1, h2⟩⟩

/-- **TSD on the domain of dependence.** For a strong solution of the Hodge wave equation of the
grad–curl complex on an open `Ω ⊆ ℝ³` (bounded or not) with TSD data `(0, E₀, B₀)`, at every
`t ∈ [0, T]`, `E(t)` and `B(t)` are symmetric and trace-free a.e. on `depDomain Ω t`, the points
at Euclidean distance `> t` from `ℝ³ \ Ω`: the boundary violation travels inward at most at unit
speed. Thesis: Prop 4.17 -/
theorem tsd_depDomain (hΩ : IsOpen Ω) {T : ℝ} {U : ℝ → Win Ω}
    (hU : Evolution.IsStrongSolution (gradCurl ℝ hΩ).wave (Icc 0 T) 0 U) (h0 : winσ (U 0) = 0)
    (hE₀ : winE (U 0) ∈ tsd Ω) (hB₀ : winB (U 0) ∈ tsd Ω) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∀ᵐ y ∂volume.restrict (depDomain Ω t), SymTF (winE (U t)) y ∧ SymTF (winB (U t)) y := by
  set s : {p : R3 × ℝ // ∀ z, dist (euc z) (euc p.1) < p.2 → z ∈ Ω} → Set R3 :=
    fun p => {y | dist (euc y) (euc p.1.1) < p.1.2 - t}
  obtain ⟨I, hI, hIU⟩ := TopologicalSpace.isOpen_iUnion_countable s
    fun p => isOpen_ball_euc _ _
  rw [depDomain_eq_iUnion, ← hIU, ae_restrict_biUnion_iff _ hI]
  intro p _
  exact (tsd_cone hΩ hU h0 hE₀ hB₀ p.2 ht).2.2.2

/-- **Existence form.** For TSD data `U₀ = (0, E₀, B₀) ∈ D(L)` and every `T`, the orbit
`t ↦ e^{tL} U₀` is a strong solution on `[0, T]`, every strong solution from `U₀` equals it, and
it is TSD on `depDomain Ω t` for every `t ∈ [0, T]`. -/
theorem existsUnique_tsd_depDomain (hΩ : IsOpen Ω) {U₀ : Win Ω}
    (hD : U₀ ∈ (gradCurl ℝ hΩ).wave.domain) (h0 : winσ U₀ = 0) (hE₀ : winE U₀ ∈ tsd Ω)
    (hB₀ : winB U₀ ∈ tsd Ω) (T : ℝ) :
    Evolution.IsStrongSolution (gradCurl ℝ hΩ).wave (Icc 0 T) 0
        (fun t => (gradCurl ℝ hΩ).toHilbertComplex.waveGroup.S t U₀) ∧
      (∀ V, V 0 = U₀ → Evolution.IsStrongSolution (gradCurl ℝ hΩ).wave (Icc 0 T) 0 V →
        ∀ t ∈ Icc 0 T, V t = (gradCurl ℝ hΩ).toHilbertComplex.waveGroup.S t U₀) ∧
      ∀ t ∈ Icc 0 T, ∀ᵐ y ∂volume.restrict (depDomain Ω t),
        SymTF (winE ((gradCurl ℝ hΩ).toHilbertComplex.waveGroup.S t U₀)) y ∧
          SymTF (winB ((gradCurl ℝ hΩ).toHilbertComplex.waveGroup.S t U₀)) y := by
  have hS := (gradCurl ℝ hΩ).toHilbertComplex.isStrongSolution_waveGroup hD T
  have hS0 : (gradCurl ℝ hΩ).toHilbertComplex.waveGroup.S 0 U₀ = U₀ := by simp
  refine ⟨hS, fun V hV0 hV t ht =>
    (gradCurl ℝ hΩ).toHilbertComplex.eq_waveGroup_of_isStrongSolution hD hV0 hV ht,
    fun t ht => tsd_depDomain hΩ hS (by rw [hS0]; exact h0) (by rw [hS0]; exact hE₀)
      (by rw [hS0]; exact hB₀) ht⟩

/-- If `V = 0` a.e. on a measurable `S`, then `∫_Ω V g = 0` for every `g` supported in `S`. -/
theorem integral_mul_eq_zero_of_ae {S : Set R3} (hS : MeasurableSet S) {V g : R3 → ℝ}
    (hV : ∀ᵐ y ∂volume.restrict S, V y = 0) (hg : Function.support g ⊆ S) :
    ∫ y, V y * g y ∂volume.restrict Ω = 0 := by
  refine integral_eq_zero_of_ae (ae_restrict_of_ae ?_)
  filter_upwards [(ae_restrict_iff' hS).1 hV] with y hy
  by_cases hyS : y ∈ S
  · simp [hy hyS]
  · simp [Function.notMem_support.1 fun h => hyS (hg h)]

/-- **Distributional form**: for `g` supported in `depDomain Ω t`,
`∫_Ω (E_{ij} - E_{ji}) g = 0` and `∫_Ω (tr E) g = 0`, and likewise for `B`. -/
theorem tsd_depDomain_distrib (hΩ : IsOpen Ω) {T : ℝ} {U : ℝ → Win Ω}
    (hU : Evolution.IsStrongSolution (gradCurl ℝ hΩ).wave (Icc 0 T) 0 U) (h0 : winσ (U 0) = 0)
    (hE₀ : winE (U 0) ∈ tsd Ω) (hB₀ : winB (U 0) ∈ tsd Ω) {t : ℝ} (ht : t ∈ Icc 0 T)
    {g : R3 → ℝ} (hg : Function.support g ⊆ depDomain Ω t) :
    (∀ i j, ∫ y, (winE (U t) (i, j) y - winE (U t) (j, i) y) * g y ∂volume.restrict Ω = 0) ∧
      ∫ y, (∑ i, winE (U t) (i, i) y) * g y ∂volume.restrict Ω = 0 ∧
      (∀ i j, ∫ y, (winB (U t) (i, j) y - winB (U t) (j, i) y) * g y ∂volume.restrict Ω = 0) ∧
      ∫ y, (∑ i, winB (U t) (i, i) y) * g y ∂volume.restrict Ω = 0 := by
  have h := tsd_depDomain hΩ hU h0 hE₀ hB₀ ht
  have hm := measurableSet_depDomain (Ω := Ω) t
  refine ⟨fun i j => integral_mul_eq_zero_of_ae hm (h.mono fun y hy => ?_) hg,
    integral_mul_eq_zero_of_ae hm (h.mono fun y hy => hy.1.2) hg,
    fun i j => integral_mul_eq_zero_of_ae hm (h.mono fun y hy => ?_) hg,
    integral_mul_eq_zero_of_ae hm (h.mono fun y hy => hy.2.2) hg⟩
  · rw [hy.1.1 i j, sub_self]
  · rw [hy.2.1 i j, sub_self]

/-- Restriction `L²(Ω) → L²(S)` for `S ⊆ Ω`. -/
def resL2 {S : Set R3} (hS : S ⊆ Ω) (f : L2 ℝ Ω) : L2 ℝ S :=
  (Measure.restrict_restrict_of_subset (μ := volume) hS ▸ (Lp.memLp f).restrict S).toLp _

theorem coeFn_resL2 {S : Set R3} (hS : S ⊆ Ω) (f : L2 ℝ Ω) :
    (resL2 hS f : R3 → ℝ) =ᵐ[volume.restrict S] f :=
  MemLp.coeFn_toLp _

/-- Restriction `L²(Ω; ℝ³ˣ³) → L²(S; ℝ³ˣ³)`, componentwise. -/
def resM {S : Set R3} (hS : S ⊆ Ω) (X : L2F ℝ Ω Ix) : L2F ℝ S Ix :=
  WithLp.toLp 2 fun ij => resL2 hS (X ij)

/-- **Local `L²(TSD)`**: if `X` is weakly divergence-free in `Ω` and symmetric and trace-free a.e.
on an open `S ⊆ Ω`, its restriction lies in `L²(TSD)(S)`. -/
theorem resM_mem_tsd (hΩ : IsOpen Ω) {S : Set R3} (hS : S ⊆ Ω) {X : L2F ℝ Ω Ix}
    (hX : ∀ φ : Fin 3 → R3 → ℝ, IsTestField Ω φ →
      ∑ ij : Ix, ∫ x, X ij x * pd ij.2 (φ ij.1) x ∂volume.restrict Ω = 0)
    (hsym : ∀ᵐ y ∂volume.restrict S, SymTF X y) : resM hS X ∈ tsd S := by
  have hc : ∀ ij, ((resM hS X) ij : R3 → ℝ) =ᵐ[volume.restrict S] X ij := fun ij =>
    coeFn_resL2 hS (X ij)
  refine mem_tsd_of_ae_symTF ?_ fun φ hφ => ?_
  · filter_upwards [hsym, ae_all_iff.2 hc] with y hy hcy
    refine ⟨fun i j => ?_, ?_⟩
    · rw [hcy, hcy, hy.1]
    · simp only [hcy]; exact hy.2
  · have hφΩ : IsTestField Ω φ := fun i => (hφ i).mono hS
    rw [← hX φ hφΩ]
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [integral_congr_ae ((hc ij).mono fun y hy => by simp only; rw [hy]),
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩ.measurableSet hS fun y hy => ?_]
    have : y ∉ tsupport (φ ij.1) := fun h => hy.2 ((hφ ij.1).tsupport_subset h)
    simp [pd, fderiv_of_notMem_tsupport (𝕜 := ℝ) this]

/-- **Local `L²(TSD)` form**: at `t ∈ [0, T]` the restrictions of `E(t)` and `B(t)` to the open
set `depDomain Ω t` lie in `L²(TSD)(depDomain Ω t)`. -/
theorem tsd_depDomain_local (hΩ : IsOpen Ω) {T : ℝ} {U : ℝ → Win Ω}
    (hU : Evolution.IsStrongSolution (gradCurl ℝ hΩ).wave (Icc 0 T) 0 U) (h0 : winσ (U 0) = 0)
    (hE₀ : winE (U 0) ∈ tsd Ω) (hB₀ : winB (U 0) ∈ tsd Ω) {t : ℝ} (ht : t ∈ Icc 0 T) :
    resM (depDomain_subset ht.1) (winE (U t)) ∈ tsd (depDomain Ω t) ∧
      resM (depDomain_subset ht.1) (winB (U t)) ∈ tsd (depDomain Ω t) := by
  have h := tsd_depDomain hΩ hU h0 hE₀ hB₀ ht
  obtain ⟨-, hdE, hdB, -⟩ := tsd_cone hΩ hU h0 hE₀ hB₀ (x := 0) (r := 0)
    (fun z hz => absurd hz (not_lt.2 dist_nonneg)) ht
  exact ⟨resM_mem_tsd hΩ _ (weakDiv_eq_zero_of_mem_ker hΩ hdE) (h.mono fun y hy => hy.1),
    resM_mem_tsd hΩ _ (weakDiv_eq_zero_of_mem_ker hΩ hdB) (h.mono fun y hy => hy.2)⟩

end Strong


end Feec.Models.BoundedDomain
