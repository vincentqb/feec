module

public import Feec.Physics.EinsteinBianchi.System
public import Feec.Physics.LinearizedGravity.PlaneWave

/-!
# The linearized Einstein–Bianchi system for fields; gravitational plane waves

Lemma 3.5 and Prop 3.4 of [QuennevilleBelair2015] for matrix fields, and the TT plane waves of
[QuennevilleBelair2015], §3.5, whose Weyl fields solve the linearized system.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open Matrix Feec.MatrixSymbol Feec.DoubleForm
open Feec.LinearizedGravity (phaseL kTT ttAmp Rjet jet2 Jet2 symbolJet symbolJet_apply)

@[expose] public noncomputable section

namespace Feec.EinsteinBianchi

section Fields

variable {n : ℕ}

theorem partialDeriv_const_mul {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : DifferentiableAt ℝ f x) (c : ℝ) (i : Fin n) :
    partialDeriv i (fun y => c * f y) x = c * partialDeriv i f x :=
  partialDeriv_const_smul hf c i

theorem partialDeriv_fintype_sum {ι : Type*} [Fintype ι] {F : ι → (Fin n → ℝ) → ℝ}
    {x : Fin n → ℝ} (hF : ∀ c, DifferentiableAt ℝ (F c) x) (i : Fin n) :
    partialDeriv i (fun y => ∑ c, F c y) x = ∑ c, partialDeriv i (F c) x :=
  partialDeriv_sum Finset.univ (fun c _ => hF c) i

theorem differentiable_partialDeriv' {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (i : Fin n) :
    Differentiable ℝ (partialDeriv i f) :=
  hf.differentiable_partialDeriv le_rfl i

/-- Spatial jet `(∂_c A)(x)` of a matrix field on `ℝ³`. -/
def jet3 (A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) : SpaceJet :=
  fun c => Matrix.of fun a b => partialDeriv c (fun y => A y a b) x

/-- The matrix field `curl A`. -/
def curlF (A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ := curl (jet3 A x)

theorem div_curl_field {A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ∀ a b, ContDiff ℝ 2 fun y => A y a b) (x : Fin 3 → ℝ) :
    div (jet3 (curlF A) x) = 0 := by
  have hd : ∀ c a d, Differentiable ℝ (partialDeriv c fun y => A y a d) := fun c a d =>
    differentiable_partialDeriv' (hA a d) c
  have e : ∀ b, jet3 (curlF A) x b =
      curl (fun c => Matrix.of fun a d => partialDeriv b (partialDeriv c fun y => A y a d) x) := by
    intro b; ext a b'
    simp only [jet3, curlF, curl, Matrix.of_apply]
    rw [partialDeriv_fintype_sum (fun c => (Differentiable.fun_sum fun d _ =>
      ((hd c a d).const_mul (leviCivita3 ℝ b' c d))) x)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [partialDeriv_fintype_sum (fun d => ((hd c a d).const_mul _) x)]
    exact Finset.sum_congr rfl fun d _ => partialDeriv_const_mul ((hd c a d) x) _ _
  rw [show jet3 (curlF A) x = fun b => curl (fun c => Matrix.of fun a d =>
      partialDeriv b (partialDeriv c fun y => A y a d) x) from funext e]
  exact div_curl _ fun b c => by ext a d; simp [partialDeriv_comm (hA a d)]

/-- If a `C²` matrix field `A` on `ℝ³` is symmetric, trace-free and divergence-free everywhere, so
is `curl A`. [QuennevilleBelair2015], Lemma 3.5 (adapted) -/
theorem curl_TSD_field {A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ∀ a b, ContDiff ℝ 2 fun y => A y a b) (hsym : ∀ y, (A y)ᵀ = A y)
    (htr : ∀ y, (A y).trace = 0) (hdiv : ∀ y, div (jet3 A y) = 0) (x : Fin 3 → ℝ) :
    (curlF A x)ᵀ = curlF A x ∧ (curlF A x).trace = 0 ∧ div (jet3 (curlF A) x) = 0 := by
  have hjs : ∀ c, (jet3 A x c)ᵀ = jet3 A x c := by
    intro c; ext i j
    simp only [jet3, Matrix.transpose_apply, Matrix.of_apply]
    congr 1; funext y
    simpa [Matrix.transpose_apply] using congrFun (congrFun (hsym y) i) j
  have hjt : ∀ c, (jet3 A x c).trace = 0 := by
    intro c
    have hd : ∀ i, DifferentiableAt ℝ (fun y => A y i i) x := fun i =>
      ((hA i i).differentiable (by norm_num)) x
    have h1 : (jet3 A x c).trace = partialDeriv c (fun y => ∑ i, A y i i) x := by
      rw [partialDeriv_fintype_sum hd]; rfl
    have h2 : (fun y => ∑ i, A y i i) = fun _ => 0 := funext htr
    rw [h1, h2]; simp [partialDeriv]
  obtain ⟨h1, h2⟩ := curl_isTSD hjs hjt (hdiv x)
  exact ⟨h1, h2, div_curl_field hA x⟩

/-- Spacetime jet `(∂_μ X)(p)` of a matrix field on `ℝ⁴`. -/
def jet4 (M : (Fin 4 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (p : (Fin 4 → ℝ)) : Jet4 :=
  fun μ => Matrix.of fun i j => partialDeriv μ (fun y => M y i j) p

theorem jet4_symm {M : (Fin 4 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} (hM : ∀ y, (M y)ᵀ = M y) (p : (Fin 4 → ℝ))
    (μ : Fin 4) : (jet4 M p μ)ᵀ = jet4 M p μ := by
  ext i j
  simp only [jet4, Matrix.transpose_apply, Matrix.of_apply]
  congr 1; funext y
  simpa [Matrix.transpose_apply] using congrFun (congrFun (hM y) i) j

theorem pd_weyl {E B : (Fin 4 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {p : (Fin 4 → ℝ)}
    (hE : ∀ i j, DifferentiableAt ℝ (fun y => E y i j) p)
    (hB : ∀ i j, DifferentiableAt ℝ (fun y => B y i j) p) (α β γ δ θ : Fin 4) :
    partialDeriv α (fun y => ofBlocks (E y) (B y) (B y) (-E y) β γ δ θ) p =
      dWeyl (jet4 E p) (jet4 B p) α β γ δ θ := by
  simp only [dWeyl, ofBlocks, ofMat_apply]
  generalize pidx β γ = I
  generalize pidx δ θ = J
  rcases I with i | i <;> rcases J with j | j <;>
    simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.neg_apply, jet4, Matrix.of_apply]
  · exact partialDeriv_const_mul (hE i j) _ _
  · exact partialDeriv_const_mul (hB i j) _ _
  · exact partialDeriv_const_mul (hB i j) _ _
  · simp only [mul_neg]
    rw [partialDeriv_neg, partialDeriv_const_mul (hE i j)]

/-- For symmetric `E`, `B` differentiable at `p`, the linearized Bianchi identity for
`[[E, B], [B, -E]]` holds at `p` iff `EBJet` does. [QuennevilleBelair2015], Prop 3.4 (adapted) -/
theorem linBianchi_field_iff {E B : (Fin 4 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} (p : (Fin 4 → ℝ))
    (hEs : ∀ y, (E y)ᵀ = E y) (hBs : ∀ y, (B y)ᵀ = B y)
    (hE : ∀ i j, DifferentiableAt ℝ (fun y => E y i j) p)
    (hB : ∀ i j, DifferentiableAt ℝ (fun y => B y i j) p) :
    (∀ α β γ δ θ, partialDeriv α (fun y => ofBlocks (E y) (B y) (B y) (-E y) β γ δ θ) p +
        partialDeriv β (fun y => ofBlocks (E y) (B y) (B y) (-E y) γ α δ θ) p +
        partialDeriv γ (fun y => ofBlocks (E y) (B y) (B y) (-E y) α β δ θ) p = 0) ↔
      EBJet (jet4 E p) (jet4 B p) := by
  simp only [pd_weyl hE hB]
  exact linBianchi_iff _ _ (jet4_symm hEs p) (jet4_symm hBs p)

/-! ### §3.5: plane waves -/

/-- Electric amplitude of the §3.5 plane wave. -/
def ampE (Ap Ax : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![-Ap, -Ax, 0; -Ax, Ap, 0; 0, 0, 0]

/-- Magnetic amplitude of the §3.5 plane wave. -/
def ampB (Ap Ax : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![-Ax, Ap, 0; Ap, Ax, 0; 0, 0, 0]

/-- The linearized Riemann tensor of the TT 2-jet `k_i k_j A_ab s` is `[[E, B], [B, -E]]`, with
`E = (κ²/2) s · ampE`, `B = (κ²/2) s · ampB`. [QuennevilleBelair2015], §3.5 (adapted) -/
theorem planeWave_weyl (κ Ap Ax s : ℝ) :
    Rjet (fun i j a b => kTT κ i * kTT κ j * ttAmp Ap Ax a b * s) =
      ofBlocks ((κ ^ 2 / 2 * s) • ampE Ap Ax) ((κ ^ 2 / 2 * s) • ampB Ap Ax)
        ((κ ^ 2 / 2 * s) • ampB Ap Ax) (-((κ ^ 2 / 2 * s) • ampE Ap Ax)) := by
  rw [eq_ofBlocks_blocks
    (LinearizedGravity.Rjet_pairSkew (LinearizedGravity.ttWaveJet_props κ Ap Ax s).1)]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [blkE, blkB, blkH, blkD, toMat, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, p, q, Rjet, kTT, ttAmp, ampE, ampB,
      invOf_eq_inv] <;> ring

/-- The §3.5 electric field `E(x) = (κ²/2) f''(k·x) ampE`. -/
def waveE (κ Ap Ax : ℝ) (f : ℝ → ℝ) (y : (Fin 4 → ℝ)) : Matrix (Fin 3) (Fin 3) ℝ :=
  (κ ^ 2 / 2 * deriv (deriv f) (phaseL (kTT κ) y)) • ampE Ap Ax

/-- The §3.5 magnetic field `B(x) = (κ²/2) f''(k·x) ampB`. -/
def waveB (κ Ap Ax : ℝ) (f : ℝ → ℝ) (y : (Fin 4 → ℝ)) : Matrix (Fin 3) (Fin 3) ℝ :=
  (κ ^ 2 / 2 * deriv (deriv f) (phaseL (kTT κ) y)) • ampB Ap Ax

private theorem jet4_wave {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) (κ : ℝ)
    (P : Matrix (Fin 3) (Fin 3) ℝ) (p : (Fin 4 → ℝ)) :
    jet4 (fun y => (κ ^ 2 / 2 * deriv (deriv f) (phaseL (kTT κ) y)) • P) p =
      fun μ => (κ ^ 2 / 2 * kTT κ μ * deriv (deriv (deriv f)) (phaseL (kTT κ) p)) • P := by
  have h3 : Differentiable ℝ (deriv (deriv f)) := by
    have := hf.differentiable_iteratedDeriv 2 (by norm_num)
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using this
  funext μ; ext i j
  simp only [jet4, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  have e : (fun y => κ ^ 2 / 2 * deriv (deriv f) (phaseL (kTT κ) y) * P i j) =
      fun y => (κ ^ 2 / 2 * P i j) * deriv (deriv f) (phaseL (kTT κ) y) := by
    funext y; ring
  rw [e, LinearizedGravity.partialDeriv_wave h3]
  ring

/-- For `f ∈ C³`, the TT plane wave `ttAmp f(κ(x³ - x⁰))` has Weyl field `[[E, B], [B, -E]]`,
`E`, `B` symmetric, trace-free and solving `EBJet`. [QuennevilleBelair2015], §3.5 -/
theorem planeWave_EB {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) (κ Ap Ax : ℝ) (p : (Fin 4 → ℝ)) :
    Rjet (jet2 (fun y => Matrix.of fun a b => ttAmp Ap Ax a b * f (phaseL (kTT κ) y)) p) =
      ofBlocks (waveE κ Ap Ax f p) (waveB κ Ap Ax f p) (waveB κ Ap Ax f p) (-waveE κ Ap Ax f p) ∧
    ((waveE κ Ap Ax f p)ᵀ = waveE κ Ap Ax f p ∧ (waveE κ Ap Ax f p).trace = 0) ∧
    ((waveB κ Ap Ax f p)ᵀ = waveB κ Ap Ax f p ∧ (waveB κ Ap Ax f p).trace = 0) ∧
    EBJet (jet4 (waveE κ Ap Ax f) p) (jet4 (waveB κ Ap Ax f) p) := by
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [LinearizedGravity.jet2_wave (hf.of_le (by norm_num))]
    have e : (deriv (deriv f) (phaseL (kTT κ) p) • symbolJet (kTT κ) (ttAmp Ap Ax) :
        Jet2 (Fin 4) ℝ) = fun i j => Matrix.of fun a b =>
          kTT κ i * kTT κ j * ttAmp Ap Ax a b * deriv (deriv f) (phaseL (kTT κ) p) := by
      funext i j; ext a b
      simp only [Pi.smul_apply, Matrix.smul_apply, symbolJet_apply, smul_eq_mul, Matrix.of_apply]
      ring
    rw [e]
    simp only [waveE, waveB]
    exact planeWave_weyl κ Ap Ax (deriv (deriv f) (phaseL (kTT κ) p))
  · ext i j; fin_cases i <;> fin_cases j <;> simp [waveE, ampE]
  · simp [waveE, ampE, Matrix.trace, Fin.sum_univ_three]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [waveB, ampB]
  · simp [waveB, ampB, Matrix.trace, Fin.sum_univ_three]
  · have e1 : waveE κ Ap Ax f = fun y =>
        (κ ^ 2 / 2 * deriv (deriv f) (phaseL (kTT κ) y)) • ampE Ap Ax := rfl
    have e2 : waveB κ Ap Ax f = fun y =>
        (κ ^ 2 / 2 * deriv (deriv f) (phaseL (kTT κ) y)) • ampB Ap Ax := rfl
    rw [e1, e2, jet4_wave hf, jet4_wave hf]
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext i; fin_cases i <;> simp [div, sp, Fin.sum_univ_three, kTT, ampE]
    · ext i; fin_cases i <;> simp [div, sp, Fin.sum_univ_three, kTT, ampB]
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [curl, sp, leviCivita3_apply, Fin.sum_univ_three, kTT, ampE, ampB]
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [curl, sp, leviCivita3_apply, Fin.sum_univ_three, kTT, ampE, ampB]

end Fields

end Feec.EinsteinBianchi
