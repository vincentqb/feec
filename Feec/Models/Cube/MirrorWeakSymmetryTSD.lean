module

public import Feec.Models.Cube.MirrorWeakSymmetryConvergence
public import Feec.Models.Cube.MirrorBGG

/-!
# The mirror scheme (6.5) converges to the TSD solution

[QuennevilleBelair2015], Ch. 6, solves the linearized Einstein–Bianchi system through the Hodge
wave equation of the BGG complex (5.1) with the symmetry of `E` imposed weakly. On the cube
`Q = (0, ½)³` with the mirror boundary conditions this is the complex
`Feec.Models.Cube.MirrorBGG.complexQ` (complex scalars, matrix fields), where TSD data have TSD
solutions (`Feec.Models.Cube.MirrorBGG.existsUnique_memQ`). The scheme (6.5) is the
discretization of the multiplier problem (6.2) for the mirror data in the forms model
(`Feec.Models.Cube.MirrorWeakSymmetryComplex.mirrorBGGSegment`), proved convergent for classical
solutions of (6.2) in `Feec.Models.Cube.MirrorWeakSymmetryConvergence`. This file identifies the
two: **the real part of the TSD solution is a classical solution of (6.2)**, so the scheme converges
to it.

**The identification.** Both sides are parity models of the torus, compared through Fourier
coefficients. For a matrix field `E` on `Q`, the row `a` of `Re E` is a `1`-form in the class
`HΛ_{a}(Q)` of the bottom row (vanishing tangential trace on the faces normal to `eₐ`): the
parity class of the coefficient of `dx_b` is the tensor parity of `E_{ab}` (`pcJ_one`), and the
row `a` of `B` through the Hodge star has the pseudo-tensor parity (`pcJ_two`). The real parity
extension of the forms is the complex mirror extension of the complexified field, so the
coefficients of `Re E` are `½ (Ê(m) + conj Ê(-m))` (`coeff_JfJ_rowRe`), and `d_ξ` of a row is the
row of the curl symbol through the Hodge star (`deRham_rowF`). Hence
* `E ∈ D((S₁, curl))` gives rows in `D(d_{a})` with `d (Re E)_a = (Re curl E)_a` (`rowRe_mem`);
* real rows in `D(d_{a})` give a field of `D((S₁, curl))` (`ofRealRows_mem`);
* TSD coefficients (`Ê(m) ξ_m = 0`) make `Re E` orthogonal to `grad` of the bottom `0`-forms
  (`inner_rowRe_dPart_zero`), and a symmetric `E` has `S¹ (Re E) = 0` (`wsL2_rowsW1L_of_symm`).

**The TSD solution as a classical solution of (6.2).** For a datum `U₀ ∈ D(L²)` in the constraint
(`TSDDatum`), `U(t) = e^{tL} U₀` is the solution of `existsUnique_memQ`
(`TSDDatum.eqOn_of_isStrongSolution`), and `(σ, φ, u, M, ρ, ℓ) = (0, 0, Re E, 0, ⋆Re B, 0)` is a
classical solution of (6.2) for the mirror data without source (`TSDDatum.exactWave`): (6.2a) is
the divergence condition, (6.2b) is `E' = -d₁† (0, B)` tested against complexified bottom
`1`-forms, (6.2c) is `S¹ E = 0`, (6.2d) is `B' = curl E`. The regularity of `ExactWave`
(time derivatives of `d u`) is where `L U₀ ∈ D(L)` is used.

## Main results

* **`mirror_waveFEM`**: for every TSD datum in `D(L²)` and every `ε > 0`, for all large `N` the
  scheme (6.5) from the elliptic projection (6.4) of the initial forms state has a solution with
  `‖σₕ‖, ‖Re E − uₕ‖, ‖Mₕ‖, ‖Re B − ρₕ‖ ≤ ε` and `‖Bₕ − Bₕᵀ‖ ≤ 2ε` on `[0,T]`, and the continuous
  solution keeps `σ ≡ 0`, `M ≡ 0`, `E`, `B` TSD.
* `cosDatum`: `E₀ = 2 cos(2π x₃) diag(1, -1, 0)`, a non-stationary TSD datum in `D(L²)`.
* `TSDDatum.exactWave`, `TSDDatum.eqOn_of_isStrongSolution`, `rowRe_mem`, `ofRealRows_mem`,
  `coeff_JfJ_rowRe`, `deRham_rowF`, `inner_rowRe_dPart_zero`, `wsL2_rowsW1L_of_symm`.

## Remarks

Rates: `Feec.Models.Cube.MirrorWaveRegularity` (`O(h)` for TSD data in `D(L³)`). The scheme works with real fields: the imaginary part of a
complex TSD solution is the real part of the solution from `-i U₀`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 5 ((5.1)), Ch. 6 (§6.1 (6.2), §6.2 (6.4), §6.3 (6.5))
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4.3 (boundary conditions)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ComplexConjugate LinearPMap
open Set MeasureTheory Filter Finset UnitAddTorus

@[expose] public noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

namespace Feec.Models.Cube.MirrorWeakSymmetry

open Feec.Fourier.Exterior (Form koszul_apply koszulDeg_apply res_apply ext_apply
  ext_apply_of_ne deRham_m_succ)
open Feec.Fourier.GradCurl (Mat Vec curl curl_apply)

def sub1 (b : Fin 3) : {s : Finset (Fin 3) // (#s : ℤ) = 1} := ⟨{b}, by simp⟩
def sub2 (i : Fin 3) : {s : Finset (Fin 3) // (#s : ℤ) = 2} :=
  ⟨univ.erase i, by rw [Finset.card_erase_of_mem (mem_univ i)]; rfl⟩

theorem sub1_bijective : Function.Bijective sub1 := by decide
theorem sub2_bijective : Function.Bijective sub2 := by decide

/-- The index equivalence `Fin 3 ≃ formIdx 3 1`, `b ↦ dx_b`. -/
def eq1 : Fin 3 ≃ {s : Finset (Fin 3) // (#s : ℤ) = 1} := Equiv.ofBijective sub1 sub1_bijective
/-- The index equivalence `Fin 3 ≃ formIdx 3 2`, `i ↦ ⋆dx_i`. -/
def eq2 : Fin 3 ≃ {s : Finset (Fin 3) // (#s : ℤ) = 2} := Equiv.ofBijective sub2 sub2_bijective

@[simp] theorem eq1_apply (b : Fin 3) : eq1 b = sub1 b := rfl
@[simp] theorem eq2_apply (i : Fin 3) : eq2 i = sub2 i := rfl
@[simp] theorem eq1_symm_sub1 (b : Fin 3) : eq1.symm (sub1 b) = b := eq1.symm_apply_apply b
@[simp] theorem eq2_symm_sub2 (i : Fin 3) : eq2.symm (sub2 i) = i := eq2.symm_apply_apply i

def sg2 (i : Fin 3) : ℝ := if i = 1 then -1 else 1

theorem sg2_mul_self (i : Fin 3) : sg2 i * sg2 i = 1 := by unfold sg2; split_ifs <;> norm_num

theorem abs_sg2 (i : Fin 3) : |sg2 i| = 1 := by unfold sg2; split_ifs <;> norm_num

def rowF (M : Mat) (a : Fin 3) : Form ℂ (Fin 3) 1 := WithLp.toLp 2 fun t => M (a, eq1.symm t)
def rowF2 (M : Mat) (a : Fin 3) : Form ℂ (Fin 3) 2 :=
  WithLp.toLp 2 fun t => (sg2 (eq2.symm t) : ℂ) * M (a, eq2.symm t)

@[simp] theorem rowF_apply (M : Mat) (a : Fin 3) (t) : rowF M a t = M (a, eq1.symm t) := rfl
@[simp] theorem rowF2_apply (M : Mat) (a : Fin 3) (t) :
    rowF2 M a t = (sg2 (eq2.symm t) : ℂ) * M (a, eq2.symm t) := rfl

theorem sgn_val (j : Fin 3) (s : Finset (Fin 3)) :
    (Feec.ExteriorFibre.sgn j s : ℂ) = (-1) ^ #({l ∈ s | l < j}) := rfl

theorem koszulDeg_sub2 (ξ : EuclideanSpace ℝ (Fin 3)) (x : Form ℂ (Fin 3) 1) {i j k : Fin 3}
    (hs : (univ : Finset (Fin 3)).erase i = {j, k}) (hjk : j ≠ k)
    (hj : #({l ∈ ({j, k} : Finset (Fin 3)) | l < j}) = 0)
    (hk : #({l ∈ ({j, k} : Finset (Fin 3)) | l < k}) = 1)
    (h1 : ({j, k} : Finset (Fin 3)).erase j = {k}) (h2 : ({j, k} : Finset (Fin 3)).erase k = {j}) :
    Feec.Fourier.Exterior.koszulDeg 1 ξ x (sub2 i) =
      (ξ j : ℂ) * x (sub1 k) - (ξ k : ℂ) * x (sub1 j) := by
  rw [koszulDeg_apply, res_apply]
  change Feec.Fourier.Exterior.koszul ξ (Feec.Fourier.Exterior.ext 1 x) (univ.erase i) = _
  rw [hs, koszul_apply, Finset.sum_pair hjk, h1, h2, sgn_val, sgn_val, hj, hk,
    ext_apply 1 _ (by simp), ext_apply 1 _ (by simp)]
  simp only [pow_zero, pow_one, one_mul, neg_mul]
  rw [← sub_eq_add_neg]
  rfl

theorem koszulDeg_sub2_zero (ξ : EuclideanSpace ℝ (Fin 3)) (x : Form ℂ (Fin 3) 1) :
    Feec.Fourier.Exterior.koszulDeg 1 ξ x (sub2 0) =
      (ξ 1 : ℂ) * x (sub1 2) - (ξ 2 : ℂ) * x (sub1 1) :=
  koszulDeg_sub2 ξ x (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem koszulDeg_sub2_one (ξ : EuclideanSpace ℝ (Fin 3)) (x : Form ℂ (Fin 3) 1) :
    Feec.Fourier.Exterior.koszulDeg 1 ξ x (sub2 1) =
      (ξ 0 : ℂ) * x (sub1 2) - (ξ 2 : ℂ) * x (sub1 0) :=
  koszulDeg_sub2 ξ x (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem koszulDeg_sub2_two (ξ : EuclideanSpace ℝ (Fin 3)) (x : Form ℂ (Fin 3) 1) :
    Feec.Fourier.Exterior.koszulDeg 1 ξ x (sub2 2) =
      (ξ 0 : ℂ) * x (sub1 1) - (ξ 1 : ℂ) * x (sub1 0) :=
  koszulDeg_sub2 ξ x (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem deRham_rowF (ξ : EuclideanSpace ℝ (Fin 3)) (M : Mat) (a : Fin 3) :
    (Feec.Fourier.Exterior.deRham (Fin 3)).m 1 (1 + 1) ξ (rowF M a) = rowF2 (curl ξ M) a := by
  ext t
  obtain ⟨i, rfl⟩ := eq2.surjective t
  rw [deRham_m_succ, smul_apply, PiLp.smul_apply, eq2_apply, rowF2_apply, eq2_symm_sub2, curl_apply]
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  · rw [koszulDeg_sub2_zero]
    simp [Fin.sum_univ_three, leviCivita3_apply, sg2]
    ring
  · rw [koszulDeg_sub2_one]
    simp [Fin.sum_univ_three, leviCivita3_apply, sg2]
    ring
  · rw [koszulDeg_sub2_two]
    simp [Fin.sum_univ_three, leviCivita3_apply, sg2]
    ring

theorem koszulDeg_sub1 (ξ : EuclideanSpace ℝ (Fin 3)) (c : Form ℂ (Fin 3) 0) (b : Fin 3) :
    Feec.Fourier.Exterior.koszulDeg 0 ξ c (sub1 b) = (ξ b : ℂ) * c ⟨∅, by simp⟩ := by
  rw [koszulDeg_apply, res_apply]
  change Feec.Fourier.Exterior.koszul ξ (Feec.Fourier.Exterior.ext 0 c) {b} = _
  rw [koszul_apply, Finset.sum_singleton, sgn_val, Finset.erase_singleton,
    ext_apply 0 _ (by simp)]
  simp [Finset.filter_singleton]

/-- `d_ξ c = i c ξ` on `0`-forms, in the coordinates `dx_b`. -/
theorem deRham_zero_sub1 (ξ : EuclideanSpace ℝ (Fin 3)) (c : Form ℂ (Fin 3) 0) (b : Fin 3) :
    (Feec.Fourier.Exterior.deRham (Fin 3)).m 0 (0 + 1) ξ c (sub1 b) =
      Complex.I * ((ξ b : ℂ) * c ⟨∅, by simp⟩) := by
  rw [deRham_m_succ, smul_apply, PiLp.smul_apply, koszulDeg_sub1, smul_eq_mul]

theorem curl_neg (ξ : EuclideanSpace ℝ (Fin 3)) (M : Mat) : curl (-ξ) M = -curl ξ M := by
  ext p
  rw [curl_apply, PiLp.neg_apply, curl_apply]
  simp only [PiLp.neg_apply, Complex.ofReal_neg, neg_mul, mul_neg, Finset.sum_neg_distrib]

/-! ### Parities -/

open Feec.Models.Cube.Mirror (MQ VQ cE_sq cB_sq conj_cE conj_cB extL2_congr)
open Feec.Models.Cube.MirrorExt (extL2 extF extF_coeff)
open Feec.Models.Cube.DeRhamIdent (JfJ JfJ_apply JR_apply pcJ pcJF pcJF_mul_self
  star_extL2 cjForm cjForm_apply ofRealF_apply)
open Feec.Models.Cube.RowWise (ofRealL reL coeFn_ofRealL coeFn_reL norm_reL_le)
open Feec.Domain (L2F L2 formIdx)
open Feec.Models.Cube.Geometry (Q)

/-- The parity class of the coefficient of `dx_b` in the row `a` of the bottom row is the tensor
parity of `E_{ab}`. -/
theorem pcJ_one (a b : Fin 3) : pcJ {a} {b} = Mirror.cE (a, b) := by
  funext k
  fin_cases a <;> fin_cases b <;> fin_cases k <;>
    simp [pcJ, DeRham.mixedSign, DeRham.reflSign, Mirror.cE, MirrorTorus.sgn]

/-- The parity class of the coefficient of `⋆dx_i` in the row `a` of the bottom `2`-forms is the
pseudo-tensor parity of `B_{ai}`. -/
theorem pcJ_two (a i : Fin 3) : pcJ {a} (univ.erase i) = Mirror.cB (a, i) := by
  funext k
  fin_cases a <;> fin_cases i <;> fin_cases k <;>
    simp [pcJ, DeRham.mixedSign, DeRham.reflSign, Mirror.cB, MirrorTorus.sgn]

/-! ### Real parts -/

theorem ofRealL_reL_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : Lp ℂ 2 μ) :
    ofRealL μ (reL μ f) = (1 / 2 : ℂ) • (f + star f) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_ofRealL (reL μ f), coeFn_reL f, Lp.coeFn_smul (1 / 2 : ℂ) (f + star f),
    Lp.coeFn_add f (star f), Lp.coeFn_star f] with x h1 h2 h3 h4 h5
  rw [h1, h2, h3, Pi.smul_apply, h4, Pi.add_apply, h5, Pi.star_apply, Complex.re_eq_add_conj]
  simp only [smul_eq_mul, RCLike.star_def]
  ring

theorem mFourierCoeff_smul_add {d : Type*} [Fintype d] (c : ℂ)
    (g h : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (m : d → ℤ) :
    mFourierCoeff (⇑(c • (g + h))) m = c * (mFourierCoeff (⇑g) m + mFourierCoeff (⇑h) m) := by
  rw [← mFourierBasis_repr, ← mFourierBasis_repr, ← mFourierBasis_repr, map_smul, map_add]
  simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem mFourierCoeff_smul' {d : Type*} [Fintype d] (c : ℂ)
    (g : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (m : d → ℤ) :
    mFourierCoeff (⇑(c • g)) m = c * mFourierCoeff (⇑g) m := by
  rw [← mFourierBasis_repr, ← mFourierBasis_repr, map_smul]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]

theorem real_smul_Lp {α : Type*} [MeasurableSpace α] {μ : Measure α} (r : ℝ) (g : Lp ℂ 2 μ) :
    r • g = (r : ℂ) • g := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_smul r g, Lp.coeFn_smul (r : ℂ) g] with x h1 h2
  rw [h1, h2, Pi.smul_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul]

theorem mFourierCoeff_extL2_re {c : Fin 3 → ℂ} (hc : ∀ j, c j * c j = 1)
    (hcr : ∀ j, conj (c j) = c j) (f : L2 ℂ (Q (Fin 3))) (m : Fin 3 → ℤ) :
    mFourierCoeff (extL2 hc (ofRealL _ (reL _ f)) : UnitAddTorus (Fin 3) → ℂ) m =
      (1 / 2 : ℂ) * (mFourierCoeff (extL2 hc f : UnitAddTorus (Fin 3) → ℂ) m +
        conj (mFourierCoeff (extL2 hc f : UnitAddTorus (Fin 3) → ℂ) (-m))) := by
  rw [ofRealL_reL_eq, map_smul, map_add, ← star_extL2 hc hcr, mFourierCoeff_smul_add,
    Feec.Fourier.TorusWeak.mFourierCoeff_star]

/-! ### Rows of matrix fields as forms -/

/-- **The real part of the row `a` of a matrix field, as a `1`-form on `Q`**:
`Σ_b Re E_{ab} dx_b`. -/
def rowRe (E : MQ) (a : Fin 3) : L2F ℝ (Q (Fin 3)) (formIdx 3 ((1 : ℕ) : ℤ)) :=
  WithLp.toLp 2 fun s => reL _ (E (a, eq1.symm s))

/-- **The real part of the row `a` of a matrix field, as a `2`-form on `Q`** (Hodge star):
`Σ_i ± Re B_{ai} ⋆dx_i`. -/
def rowRe2 (B : MQ) (a : Fin 3) : L2F ℝ (Q (Fin 3)) (formIdx 3 ((2 : ℕ) : ℤ)) :=
  WithLp.toLp 2 fun s => sg2 (eq2.symm s) • reL _ (B (a, eq2.symm s))

theorem coeff_JfJ_rowRe (E : MQ) (a : Fin 3) (m : Fin 3 → ℤ) :
    (JfJ {a} 1 (rowRe E a) : (Fin 3 → ℤ) → Form ℂ (Fin 3) 1) m =
      (1 / 2 : ℂ) • (rowF ((MirrorBGG.J₁ E : (Fin 3 → ℤ) → Mat) m) a +
        cjForm (rowF ((MirrorBGG.J₁ E : (Fin 3 → ℤ) → Mat) (-m)) a)) := by
  ext t
  obtain ⟨b, rfl⟩ := eq1.surjective t
  rw [JfJ_apply, JR_apply, extF_coeff, ofRealF_apply]
  simp only [PiLp.smul_apply, PiLp.add_apply, rowF_apply, cjForm_apply, eq1_apply, eq1_symm_sub1,
    smul_eq_mul]
  rw [extF_coeff, extF_coeff,
    extL2_congr (show pcJF {a} (sub1 b) = Mirror.cE (a, b) from pcJ_one a b) _
      (cE_sq (a, b))]
  change mFourierCoeff (extL2 (cE_sq (a, b))
    (ofRealL _ (reL _ (E (a, eq1.symm (sub1 b))))) : _ → ℂ) m = _
  rw [eq1_symm_sub1, mFourierCoeff_extL2_re (cE_sq (a, b)) (conj_cE (a, b))]

theorem coeff_JfJ_rowRe2 (B : MQ) (a : Fin 3) (m : Fin 3 → ℤ) :
    (JfJ {a} 2 (rowRe2 B a) : (Fin 3 → ℤ) → Form ℂ (Fin 3) 2) m =
      (1 / 2 : ℂ) • (rowF2 ((extF (c := Mirror.cB) cB_sq B : (Fin 3 → ℤ) → Mat) m) a +
        cjForm (rowF2 ((extF (c := Mirror.cB) cB_sq B : (Fin 3 → ℤ) → Mat) (-m)) a)) := by
  ext t
  obtain ⟨i, rfl⟩ := eq2.surjective t
  rw [JfJ_apply, JR_apply, extF_coeff, ofRealF_apply]
  simp only [PiLp.smul_apply, PiLp.add_apply, rowF2_apply, cjForm_apply, eq2_apply, eq2_symm_sub2,
    smul_eq_mul]
  rw [extF_coeff, extF_coeff,
    extL2_congr (show pcJF {a} (sub2 i) = Mirror.cB (a, i) from pcJ_two a i) _
      (cB_sq (a, i))]
  change mFourierCoeff (extL2 (cB_sq (a, i)) (ofRealL _
    (sg2 (eq2.symm (sub2 i)) •
      reL _ (B (a, eq2.symm (sub2 i))))) : _ → ℂ) m = _
  rw [eq2_symm_sub2, map_smul, real_smul_Lp, map_smul,
    mFourierCoeff_smul', mFourierCoeff_extL2_re (cB_sq (a, i)) (conj_cB (a, i)), map_mul,
    Complex.conj_ofReal]
  ring

theorem rowF2_neg (M : Mat) (a : Fin 3) : rowF2 (-M) a = -rowF2 M a := by
  ext t; simp

theorem cjForm_neg {k : ℕ} (v : Form ℂ (Fin 3) k) : cjForm (-v) = -cjForm v := by
  ext t; simp

theorem rowF2_injective {M N : Mat} {a : Fin 3} (h : rowF2 M a = rowF2 N a) (i : Fin 3) :
    M (a, i) = N (a, i) := by
  have e := congrArg (fun v : Form ℂ (Fin 3) 2 => v (sub2 i)) h
  simp only [rowF2_apply, eq2_symm_sub2] at e
  have hs : (sg2 i : ℂ) ≠ 0 := by unfold sg2; split_ifs <;> norm_num
  exact mul_left_cancel₀ hs e

open Feec.Models.Cube.DeRhamIdent (dPart mem_dPart_of_JfJ injective_JfJ coeff_d_dPart)
open Feec.FiniteElement (wsL2 wsL2_apply wsCoeff wsCoeff_eq)

/-! ### The second operator of the BGG complex on the Fourier side -/

/-- The curl part of `d₁ E = (S₁ E, curl E)` on `Q`, on the Fourier side:
`(curl E)^(n) = curl_{ξ_n} Ê(n)` for the mirror extensions. -/
theorem coeff_curl (E : (MirrorBGG.complexQ.d 1 2).domain) (n : Fin 3 → ℤ) :
    (extF (c := Mirror.cB) cB_sq (WithLp.ofLp (MirrorBGG.complexQ.d 1 2 E : MirrorBGG.W2Q)).2 :
      (Fin 3 → ℤ) → Mat) n =
      curl (Fourier.Torus.freq n) ((MirrorBGG.J₁ (show MQ from E.1) : (Fin 3 → ℤ) → Mat) n) := by
  obtain ⟨h, e⟩ := MirrorBGG.complexQ_d₁_eq E
  have hB : (WithLp.ofLp (MirrorBGG.complexQ.d 1 2 E : MirrorBGG.W2Q)).2 =
      Mirror.complexQ.d 1 2 ⟨E.1, h⟩ := by
    rw [e]
  rw [hB]
  have h2 : extF (c := Mirror.cB) cB_sq (Mirror.complexQ.d 1 2 ⟨E.1, h⟩) =
      Models.Torus.GradCurl.complex.d 1 2 ⟨Mirror.J 1 E.1, _⟩ :=
    Mirror.J_complexQ_d (i := 1) (j := 2) ⟨E.1, h⟩
  rw [h2]
  exact Operator.coeFn_mulOp_count (𝕜 := ℂ)
    (fun n => Fourier.GradCurl.gradCurl.m 1 2 (Fourier.Torus.freq n)) _ n

/-- **The rows of a field of `D((S₁, curl))` are in `HΛ_{a}¹(Q)`** (real parts), with `d` the
rows of `curl E` through the Hodge star. -/
theorem rowRe_mem (E : (MirrorBGG.complexQ.d 1 2).domain) (a : Fin 3) :
    ∃ h : rowRe (show MQ from E.1) a ∈ (dPart (Q (Fin 3)) {a} ((1 : ℕ) : ℤ)).domain,
      dPart (Q (Fin 3)) {a} ((1 : ℕ) : ℤ) ⟨_, h⟩ =
        rowRe2 (WithLp.ofLp (MirrorBGG.complexQ.d 1 2 E : MirrorBGG.W2Q)).2 a := by
  set B := (WithLp.ofLp (MirrorBGG.complexQ.d 1 2 E : MirrorBGG.W2Q)).2
  obtain ⟨hu, e⟩ := mem_dPart_of_JfJ (J := {a}) (k := 1) (u := rowRe (show MQ from E.1) a)
    (y := JfJ {a} (1 + 1) (rowRe2 B a)) fun m => by
      change (Feec.Fourier.Exterior.deRham (Fin 3)).m 1 (1 + 1) (Fourier.Torus.freq m) _ = _
      rw [coeff_JfJ_rowRe, coeff_JfJ_rowRe2, map_smul, map_add, deRham_rowF,
        Feec.Models.Cube.DeRhamIdent.deRham_cjForm, deRham_rowF, coeff_curl E m, coeff_curl E (-m),
        Fourier.Torus.freq_neg, curl_neg, rowF2_neg, cjForm_neg]
  exact ⟨hu, injective_JfJ {a} (1 + 1) e⟩

/-! ### Real rows as matrix fields -/

/-- **Real `1`-forms `v_a` on `Q` as the rows of a complex matrix field**:
`E_{ab} = (v_a)_{dx_b}`. -/
def ofRealRows (v : Fin 3 → L2F ℝ (Q (Fin 3)) (formIdx 3 ((1 : ℕ) : ℤ))) : MQ :=
  WithLp.toLp 2 fun p => ofRealL _ (v p.1 (sub1 p.2))

/-- **Real `2`-forms `w_a` on `Q` as the rows of a complex matrix field** (Hodge star):
`B_{ai} = ± (w_a)_{⋆dx_i}`. -/
def ofRealRows2 (w : Fin 3 → L2F ℝ (Q (Fin 3)) (formIdx 3 ((2 : ℕ) : ℤ))) : MQ :=
  WithLp.toLp 2 fun p => (sg2 p.2 : ℂ) • ofRealL _ (w p.1 (sub2 p.2))

theorem rowF_J₁_ofRealRows (v : Fin 3 → L2F ℝ (Q (Fin 3)) (formIdx 3 ((1 : ℕ) : ℤ))) (a : Fin 3)
    (m : Fin 3 → ℤ) :
    rowF ((MirrorBGG.J₁ (ofRealRows v) : (Fin 3 → ℤ) → Mat) m) a =
      (JfJ {a} 1 (v a) : (Fin 3 → ℤ) → Form ℂ (Fin 3) 1) m := by
  ext t
  obtain ⟨b, rfl⟩ := eq1.surjective t
  rw [rowF_apply, eq1_apply, eq1_symm_sub1, JfJ_apply, JR_apply, extF_coeff,
    extF_coeff, ofRealF_apply,
    extL2_congr (show pcJF {a} (sub1 b) = Mirror.cE (a, b) from pcJ_one a b) _
      (cE_sq (a, b))]
  rfl

theorem rowF2_extF_ofRealRows2 (w : Fin 3 → L2F ℝ (Q (Fin 3)) (formIdx 3 ((2 : ℕ) : ℤ)))
    (a : Fin 3) (m : Fin 3 → ℤ) :
    rowF2 ((extF (c := Mirror.cB) cB_sq (ofRealRows2 w) : (Fin 3 → ℤ) → Mat) m) a =
      (JfJ {a} 2 (w a) : (Fin 3 → ℤ) → Form ℂ (Fin 3) 2) m := by
  ext t
  obtain ⟨i, rfl⟩ := eq2.surjective t
  rw [rowF2_apply, eq2_apply, eq2_symm_sub2, JfJ_apply, JR_apply, extF_coeff,
    extF_coeff, ofRealF_apply,
    extL2_congr (show pcJF {a} (sub2 i) = Mirror.cB (a, i) from pcJ_two a i) _
      (cB_sq (a, i))]
  change (sg2 i : ℂ) * mFourierCoeff (extL2 (cB_sq (a, i))
    ((sg2 i : ℂ) • ofRealL _ (w a (sub2 i))) : _ → ℂ) m = _
  rw [map_smul, mFourierCoeff_smul', ← mul_assoc, ← Complex.ofReal_mul, sg2_mul_self,
    Complex.ofReal_one, one_mul]

/-- **Rows of `HΛ_{a}¹(Q)` give a field of `D((S₁, curl))`**, with
`d₁ E = (S₁ E, rows of d v_a)`. -/
theorem ofRealRows_mem (v : Fin 3 → L2F ℝ (Q (Fin 3)) (formIdx 3 ((1 : ℕ) : ℤ)))
    (hv : ∀ a, v a ∈ (dPart (Q (Fin 3)) {a} ((1 : ℕ) : ℤ)).domain) :
    ∃ h : ofRealRows v ∈ (MirrorBGG.complexQ.d 1 2).domain,
      (MirrorBGG.complexQ.d 1 2 ⟨_, h⟩ : MirrorBGG.W2Q) = WithLp.toLp 2
        (MirrorBGG.axialQ (ofRealRows v),
          ofRealRows2 fun a => dPart (Q (Fin 3)) {a} ((1 : ℕ) : ℤ) ⟨v a, hv a⟩) := by
  set w := fun a => dPart (Q (Fin 3)) {a} ((1 : ℕ) : ℤ) ⟨v a, hv a⟩ with hw
  set V := ofRealRows v
  have hcoef : ∀ n, Fourier.BGG.bggFamily.m 1 2 (Fourier.Torus.freq n)
      ((MirrorBGG.J₁ V : (Fin 3 → ℤ) → Mat) n) =
      (MirrorBGG.J₂ (WithLp.toLp 2 (MirrorBGG.axialQ V, ofRealRows2 w)) :
        (Fin 3 → ℤ) → Fourier.BGG.VM) n := by
    intro n
    rw [MirrorBGG.J₂, Feec.Models.Cube.MirrorExt.pairLp_coeff]
    change Fourier.BGG.bgg (Fourier.Torus.freq n) _ = _
    rw [Fourier.BGG.bgg_apply, WithLp.ofLp_toLp, MirrorBGG.extF_axialQ, MirrorBGG.axialLp_apply]
    refine congrArg (WithLp.toLp 2) (Prod.ext rfl ?_)
    ext ⟨a, i⟩
    refine rowF2_injective (a := a) ?_ i
    rw [← deRham_rowF, rowF_J₁_ofRealRows, rowF2_extF_ofRealRows2, hw]
    exact coeff_d_dPart {a} 1 ⟨v a, hv a⟩ n
  obtain ⟨hJ, eJ⟩ := Feec.Models.Cube.MirrorExt.exists_mulOp_count_eq _ hcoef
  have hV : (show MirrorBGG.SpaceQ 1 from V) ∈ (MirrorBGG.complexQ.d 1 2).domain :=
    MirrorBGG.mem_complexQ_domain_iff.2 hJ
  refine ⟨hV, MirrorBGG.embeddingQ.J_injective 2 ?_⟩
  have e1' := MirrorBGG.J_complexQ_d (i := 1) (j := 2) ⟨_, hV⟩
  exact e1'.trans eJ

/-! ### Real parts of inner products -/

theorem re_inner_ofRealL {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : Lp ℂ 2 μ)
    (g : Lp ℝ 2 μ) : RCLike.re ⟪f, ofRealL μ g⟫_ℂ = ⟪reL μ f, g⟫_ℝ := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def,
    ← integral_re (L2.integrable_inner f _)]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_ofRealL g, coeFn_reL f] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

@[simp] theorem rowRe_eq1 (E : MQ) (a b : Fin 3) : rowRe E a (eq1 b) = reL _ (E (a, b)) := by
  simp [rowRe]

@[simp] theorem rowRe2_eq2 (B : MQ) (a i : Fin 3) :
    rowRe2 B a (eq2 i) = sg2 i • reL _ (B (a, i)) := by
  simp [rowRe2]

theorem re_inner_ofRealRows (E : MQ) (v : Fin 3 → L2F ℝ (Q (Fin 3)) (formIdx 3 ((1 : ℕ) : ℤ))) :
    RCLike.re ⟪E, ofRealRows v⟫_ℂ = ∑ a, ⟪rowRe E a, v a⟫_ℝ := by
  rw [PiLp.inner_apply, map_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [PiLp.inner_apply, ← Fintype.sum_equiv (κ := formIdx 3 ((1 : ℕ) : ℤ)) eq1
    (fun b => ⟪rowRe E a (eq1 b), v a (eq1 b)⟫_ℝ) _ fun _ => rfl]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [rowRe_eq1]
  exact re_inner_ofRealL _ _

theorem re_inner_ofRealRows2 (B : MQ) (w : Fin 3 → L2F ℝ (Q (Fin 3)) (formIdx 3 ((2 : ℕ) : ℤ))) :
    RCLike.re ⟪B, ofRealRows2 w⟫_ℂ = ∑ a, ⟪rowRe2 B a, w a⟫_ℝ := by
  rw [PiLp.inner_apply, map_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [PiLp.inner_apply, ← Fintype.sum_equiv (κ := formIdx 3 ((2 : ℕ) : ℤ)) eq2
    (fun i => ⟪rowRe2 B a (eq2 i), w a (eq2 i)⟫_ℝ) _ fun _ => rfl]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rowRe2_eq2, real_inner_smul_left]
  change RCLike.re ⟪B (a, i), (sg2 i : ℂ) • ofRealL _ (w a (eq2 i))⟫_ℂ = _
  rw [inner_smul_right]
  change Complex.re ((sg2 i : ℂ) * _) = _
  rw [Complex.re_ofReal_mul, ← re_inner_ofRealL]
  rfl

/-! ### TSD fields are divergence-free against the bottom `0`-forms -/

/-- **`⟪Re E_a, grad ψ⟫ = 0`** for `ψ ∈ HΛ_{a}⁰(Q)` when the coefficients of `E` are TSD
(`Ê(n) ξ_n = 0`): on the Fourier side the pairing vanishes frequency by frequency. -/
theorem inner_rowRe_dPart_zero (E : MQ)
    (hE : ∀ n, (MirrorBGG.J₁ E : (Fin 3 → ℤ) → Mat) n ∈ Fourier.GradCurl.tsd (Fourier.Torus.freq n))
    (a : Fin 3) (ψ : (dPart (Q (Fin 3)) {a} ((0 : ℕ) : ℤ)).domain) :
    ⟪rowRe E a, (dPart (Q (Fin 3)) {a} ((0 : ℕ) : ℤ) ψ :
      L2F ℝ (Q (Fin 3)) (formIdx 3 ((1 : ℕ) : ℤ)))⟫_ℝ = 0 := by
  have h8 := Feec.Models.Cube.DeRhamIdent.inner_JfJ {a} 1 (rowRe E a)
    (dPart (Q (Fin 3)) {a} ((0 : ℕ) : ℤ) ψ)
  have hz : ⟪JfJ {a} 1 (rowRe E a), JfJ {a} 1 (dPart (Q (Fin 3)) {a} ((0 : ℕ) : ℤ) ψ)⟫_ℝ = 0 := by
    rw [MeasureTheory.L2.real_inner_eq_re_inner EuclideanSpace.real_inner_eq_re_inner,
      MeasureTheory.L2.inner_def]
    have hpt : ∀ m, ⟪(JfJ {a} 1 (rowRe E a) : (Fin 3 → ℤ) → Form ℂ (Fin 3) 1) m,
        (JfJ {a} 1 (dPart (Q (Fin 3)) {a} ((0 : ℕ) : ℤ) ψ) : (Fin 3 → ℤ) → Form ℂ (Fin 3) 1) m⟫_ℂ
          = 0 := by
      intro m
      have hg : (JfJ {a} 1 (dPart (Q (Fin 3)) {a} ((0 : ℕ) : ℤ) ψ) :
          (Fin 3 → ℤ) → Form ℂ (Fin 3) 1) m =
          (Feec.Fourier.Exterior.deRham (Fin 3)).m 0 (0 + 1) (Fourier.Torus.freq m)
            ((JfJ {a} 0 (ψ : L2F ℝ (Q (Fin 3)) (formIdx 3 ((0 : ℕ) : ℤ))) :
              (Fin 3 → ℤ) → Form ℂ (Fin 3) 0) m) :=
        (coeff_d_dPart {a} 0 ψ m).symm
      rw [hg, coeff_JfJ_rowRe, PiLp.inner_apply,
        ← Fintype.sum_equiv eq1 (fun b => ⟪((1 / 2 : ℂ) • (rowF ((MirrorBGG.J₁ E :
          (Fin 3 → ℤ) → Mat) m) a + cjForm (rowF ((MirrorBGG.J₁ E : (Fin 3 → ℤ) → Mat) (-m)) a)))
          (eq1 b), (Feec.Fourier.Exterior.deRham (Fin 3)).m 0 (0 + 1) (Fourier.Torus.freq m)
            ((JfJ {a} 0 (ψ : L2F ℝ (Q (Fin 3)) (formIdx 3 ((0 : ℕ) : ℤ))) :
              (Fin 3 → ℤ) → Form ℂ (Fin 3) 0) m) (eq1 b)⟫_ℂ) _ fun _ => rfl]
      simp only [eq1_apply, deRham_zero_sub1, PiLp.smul_apply, PiLp.add_apply, rowF_apply,
        eq1_symm_sub1, cjForm_apply, RCLike.inner_apply, Fin.sum_univ_three, smul_eq_mul]
      have h1 := hE m
      have h2 := hE (-m)
      rw [Fourier.GradCurl.mem_tsd] at h1 h2
      have h1a := congrFun h1.2.2 a
      have h2a := congrFun h2.2.2 a
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fourier.GradCurl.toMatrix_apply,
        Fourier.GradCurl.cfreq, Pi.zero_apply, Fourier.Torus.freq_neg, PiLp.neg_apply,
        Complex.ofReal_neg] at h1a h2a
      have h1c := congrArg (starRingEnd ℂ) h1a
      simp only [map_add, map_mul, Complex.conj_ofReal, map_zero] at h1c
      simp only [map_add, map_mul, Complex.conj_conj, map_div₀, map_one, map_ofNat]
      linear_combination (1 / 2 * Complex.I *
          (JfJ {a} 0 (ψ : L2F ℝ (Q (Fin 3)) (formIdx 3 ((0 : ℕ) : ℤ))) :
            (Fin 3 → ℤ) → Form ℂ (Fin 3) 0) m ⟨∅, by simp⟩) * (h1c + -h2a)
    calc _ = RCLike.re (∫ _m, (0 : ℂ) ∂Measure.count) := by
          congr 1; exact integral_congr_ae (Eventually.of_forall hpt)
      _ = 0 := by simp
  rw [hz] at h8
  have h8' : (2 : ℝ) ^ 3 * ⟪rowRe E a, (dPart (Q (Fin 3)) {a} ((0 : ℕ) : ℤ) ψ :
      L2F ℝ (Q (Fin 3)) (formIdx 3 ((1 : ℕ) : ℤ)))⟫_ℝ = 0 := h8.symm
  exact (mul_eq_zero.1 h8').resolve_left (by norm_num)

/-! ### `S¹` vanishes on symmetric matrices -/

theorem wsCoeff_swap (t : formIdx 3 ((1 : ℤ) + 1)) (a b : Fin 3) :
    wsCoeff 1 t (b, eq1 a) = -wsCoeff 1 t (a, eq1 b) := by
  obtain ⟨i, rfl⟩ := eq2.surjective t
  rw [wsCoeff_eq, wsCoeff_eq]
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp (config := { decide := true }) [eq2, sub2, Equiv.ofBijective, Feec.ExteriorFibre.sgn]

/-- **`S¹ = 2 vskw` vanishes on symmetric rows**: `(S v)_{jk} = ±(v_j{k} − v_k{j})`. -/
theorem wsL2_eq_zero_of_symm {Ω : Set (Fin 3 → ℝ)}
    (v : PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 1)))
    (hv : ∀ a b, v a (eq1 b) = v b (eq1 a)) : wsL2 (Ω := Ω) 1 v = 0 := by
  refine PiLp.ext fun t => ?_
  rw [wsL2_apply]
  set F : Fin 3 × Fin 3 → L2 ℝ Ω := fun q => wsCoeff 1 t (q.1, eq1 q.2) • v q.1 (eq1 q.2) with hF
  have h1 : ∑ p : Fin 3 × formIdx 3 1, wsCoeff 1 t p • v p.1 p.2 = ∑ q, F q :=
    (Fintype.sum_equiv ((Equiv.refl _).prodCongr eq1) _ _ fun q => rfl).symm
  have h2 : ∑ q, F q = -∑ q, F q := by
    calc ∑ q, F q = ∑ q : Fin 3 × Fin 3, F (q.2, q.1) :=
          Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun q => rfl
      _ = ∑ q, -F q := Finset.sum_congr rfl fun q _ => by
          simp only [hF]
          rw [wsCoeff_swap, hv q.2 q.1, neg_smul]
      _ = -∑ q, F q := Finset.sum_neg_distrib F
  have h3 : ∑ q, F q = 0 := by
    have h4 : (2 : ℝ) • ∑ q, F q = 0 := by
      rw [two_smul]; nth_rewrite 2 [h2]; exact add_neg_cancel _
    exact (smul_eq_zero.1 h4).resolve_left two_ne_zero
  rw [h1, h3]
  rfl

/-! ### The cube domain -/

/-- Transport of `L²` fields along an equality of domains. -/
def castL2 {Ω Ω' : Set (Fin 3 → ℝ)} (h : Ω = Ω') (ι : Type*) [Fintype ι] :
    L2F ℝ Ω ι ≃ₗᵢ[ℝ] L2F ℝ Ω' ι := by
  subst h; exact LinearIsometryEquiv.refl ℝ _

theorem dPart_graph_castL2 {Ω : Set (Fin 3 → ℝ)} (h : Ω = Q (Fin 3)) (J : Finset (Fin 3)) (k : ℤ)
    (x : L2F ℝ Ω (formIdx 3 k)) (y : L2F ℝ Ω (formIdx 3 (k + 1))) :
    (x, y) ∈ (dPart Ω J k).graph ↔
      (castL2 h _ x, castL2 h _ y) ∈ (dPart (Q (Fin 3)) J k).graph := by
  subst h; rfl

open Feec.Models.Cube.FEM (cubeDomain cubeDomain_eq_Q)

/-- `L²(cubeDomain 3) = L²(Q)`. -/
abbrev cQ (ι : Type*) [Fintype ι] : L2F ℝ (cubeDomain 3) ι ≃ₗᵢ[ℝ] L2F ℝ (Q (Fin 3)) ι :=
  castL2 (cubeDomain_eq_Q 3) ι

/-- `d_J` on the cube domain is `d_J` on `Q` (forms from `Q`). -/
theorem dPart_cube_of_Q {J : Finset (Fin 3)} {k : ℤ} {x : L2F ℝ (Q (Fin 3)) (formIdx 3 k)}
    {y : L2F ℝ (Q (Fin 3)) (formIdx 3 (k + 1))} (h : (x, y) ∈ (dPart (Q (Fin 3)) J k).graph) :
    ∃ hx : (cQ _).symm x ∈ (dPart (cubeDomain 3) J k).domain,
      dPart (cubeDomain 3) J k ⟨_, hx⟩ = (cQ _).symm y := by
  have h' : ((cQ _).symm x, (cQ _).symm y) ∈ (dPart (cubeDomain 3) J k).graph := by
    rw [dPart_graph_castL2 (cubeDomain_eq_Q 3), LinearIsometryEquiv.apply_symm_apply,
      LinearIsometryEquiv.apply_symm_apply]
    exact h
  have hx := LinearPMap.mem_domain_of_mem_graph h'
  exact ⟨hx, ((LinearPMap.image_iff hx).2 h').symm⟩

/-- `d_J` on `Q` is `d_J` on the cube domain (forms from the cube domain). -/
theorem dPart_Q_of_cube {J : Finset (Fin 3)} {k : ℤ} (x : (dPart (cubeDomain 3) J k).domain) :
    ∃ hx : cQ _ (x : L2F ℝ (cubeDomain 3) (formIdx 3 k)) ∈ (dPart (Q (Fin 3)) J k).domain,
      dPart (Q (Fin 3)) J k ⟨_, hx⟩ = cQ _ (dPart (cubeDomain 3) J k x) := by
  have h' := (dPart_graph_castL2 (cubeDomain_eq_Q 3) J k _ _).1
    ((dPart (cubeDomain 3) J k).mem_graph x)
  have hx := LinearPMap.mem_domain_of_mem_graph h'
  exact ⟨hx, ((LinearPMap.image_iff hx).2 h').symm⟩

/-! ### Matrix proxies -/

open Feec.Models.Cube.WeakSymmetry (W0 W1 W2 Wv)

/-- `E ↦ Re E_a` as a bounded real-linear map. -/
def rowReL (a : Fin 3) : MQ →L[ℝ] L2F ℝ (Q (Fin 3)) (formIdx 3 ((1 : ℕ) : ℤ)) :=
  (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : formIdx 3 ((1 : ℕ) : ℤ) => L2 ℝ (Q (Fin 3)))).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun s => (reL _) ∘L
      ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 × Fin 3 => L2 ℂ (Q (Fin 3)))
        (a, eq1.symm s)).restrictScalars ℝ)

/-- `B ↦ ⋆ Re B_a` as a bounded real-linear map. -/
def rowRe2L (a : Fin 3) : MQ →L[ℝ] L2F ℝ (Q (Fin 3)) (formIdx 3 ((2 : ℕ) : ℤ)) :=
  (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : formIdx 3 ((2 : ℕ) : ℤ) => L2 ℝ (Q (Fin 3)))).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun s => sg2 (eq2.symm s) • ((reL _) ∘L
      ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 × Fin 3 => L2 ℂ (Q (Fin 3)))
        (a, eq2.symm s)).restrictScalars ℝ))

/-- **The matrix proxy of the bottom `1`-forms**: the real rows of `E` as `(L²Λ¹(Q))³`. -/
def rowsW1L : MQ →L[ℝ] Wv W1 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => W1)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun a =>
      (cQ (formIdx 3 ((1 : ℕ) : ℤ))).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L rowReL a

/-- **The matrix proxy of the bottom `2`-forms**: the real rows of `B` through the Hodge star, as
`(L²Λ²(Q))³`. -/
def rowsW2L : MQ →L[ℝ] Wv W2 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => W2)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun a =>
      (cQ (formIdx 3 ((2 : ℕ) : ℤ))).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L rowRe2L a

@[simp] theorem rowsW1L_apply (E : MQ) (a : Fin 3) : rowsW1L E a = (cQ _).symm (rowRe E a) := rfl
@[simp] theorem rowsW2L_apply (B : MQ) (a : Fin 3) : rowsW2L B a = (cQ _).symm (rowRe2 B a) := rfl

/-- `‖rowsW1L E‖² = Σ_{ab} ‖Re E_{ab}‖²`. -/
theorem norm_sq_rowsW1L (E : MQ) : ‖rowsW1L E‖ ^ 2 = ∑ p, ‖reL _ (E p)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rowsW1L_apply, LinearIsometryEquiv.norm_map, PiLp.norm_sq_eq_of_L2]
  refine (Fintype.sum_equiv eq1 (fun b => ‖rowRe E a (eq1 b)‖ ^ 2) _ fun b => rfl).symm.trans ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [rowRe_eq1]

/-- `‖rowsW2L B‖² = Σ_{ai} ‖Re B_{ai}‖²`. -/
theorem norm_sq_rowsW2L (B : MQ) : ‖rowsW2L B‖ ^ 2 = ∑ p, ‖reL _ (B p)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rowsW2L_apply, LinearIsometryEquiv.norm_map, PiLp.norm_sq_eq_of_L2]
  refine (Fintype.sum_equiv eq2 (fun i => ‖rowRe2 B a (eq2 i)‖ ^ 2) _ fun i => rfl).symm.trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rowRe2_eq2, norm_smul, Real.norm_eq_abs, abs_sg2, one_mul]

/-- **The real rows of a matrix field are no larger than the field**: `‖Re E‖ ≤ ‖E‖`. -/
theorem sq_norm_rowsW1L_le (E : MQ) : ‖rowsW1L E‖ ^ 2 ≤ ‖E‖ ^ 2 := by
  rw [norm_sq_rowsW1L, PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_le_sum fun p _ => pow_le_pow_left₀ (norm_nonneg _) (norm_reL_le _) 2

/-- The real rows of a matrix field through the Hodge star are no larger than the field. -/
theorem sq_norm_rowsW2L_le (B : MQ) : ‖rowsW2L B‖ ^ 2 ≤ ‖B‖ ^ 2 := by
  rw [norm_sq_rowsW2L, PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_le_sum fun p _ => pow_le_pow_left₀ (norm_nonneg _) (norm_reL_le _) 2

open Classical in
/-- The real rows of `E` in `∏ₐ H_{a}Λ¹(Q)` (`0` off the domain). -/
def rowsBU (E : MQ) : BU1 :=
  WithLp.toLp 2 fun a => if h : (cQ _).symm (rowRe E a) ∈ (BD1 a).domain then ⟨_, h⟩ else 0

theorem rowsBU_mem (E : (MirrorBGG.complexQ.d 1 2).domain) (a : Fin 3) :
    ∃ h : (cQ _).symm (rowRe (show MQ from E.1) a) ∈ (BD1 a).domain,
      BD1 a ⟨_, h⟩ = (cQ _).symm (rowRe2 (WithLp.ofLp (MirrorBGG.complexQ.d 1 2 E :
        MirrorBGG.W2Q)).2 a) := by
  obtain ⟨h, e⟩ := rowRe_mem E a
  have hg := (dPart (Q (Fin 3)) {a} ((1 : ℕ) : ℤ)).mem_graph ⟨_, h⟩
  rw [e] at hg
  exact dPart_cube_of_Q hg

theorem rowsBU_apply_of_mem (E : MQ) (a : Fin 3)
    (h : (cQ _).symm (rowRe E a) ∈ (BD1 a).domain) : rowsBU E a = ⟨_, h⟩ := by
  simp only [rowsBU, PiLp.toLp_apply]
  split_ifs with h'
  · rfl
  · exact absurd h h'

theorem bIncl1_rowsBU (E : (MirrorBGG.complexQ.d 1 2).domain) :
    bIncl1 (rowsBU (show MQ from E.1)) = rowsW1L (show MQ from E.1) := by
  refine PiLp.ext fun a => ?_
  rw [bIncl1_apply, rowsBU_apply_of_mem _ a (rowsBU_mem E a).1, rowsW1L_apply]

theorem bD1_rowsBU (E : (MirrorBGG.complexQ.d 1 2).domain) :
    bD1 (rowsBU (show MQ from E.1)) =
      rowsW2L (WithLp.ofLp (MirrorBGG.complexQ.d 1 2 E : MirrorBGG.W2Q)).2 := by
  refine PiLp.ext fun a => ?_
  rw [bD1_apply, rowsW2L_apply]
  obtain ⟨h, e⟩ := rowsBU_mem E a
  rw [← e, rowsBU_apply_of_mem _ a h]

/-- The forms model `⟪u, v⟫` on `∏ₐ H_{a}Λ¹(Q)` is the `L²` pairing. -/
theorem inner_BU1 (x y : BU1) : ⟪x, y⟫_ℝ = ⟪bIncl1 x, bIncl1 y⟫_ℝ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  rfl

/-- **The pairing of the matrix proxy with bottom `1`-forms is the real part of the complex
pairing with the complexified rows.** -/
theorem inner_rowsW1L (E : MQ) (v : BU1) :
    ⟪rowsW1L E, bIncl1 v⟫_ℝ =
      RCLike.re ⟪E, ofRealRows fun a => cQ _ ((v a : (BD1 a).domain) : W1)⟫_ℂ := by
  rw [re_inner_ofRealRows, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rowsW1L_apply, bIncl1_apply, ← LinearIsometryEquiv.inner_map_map (cQ _),
    LinearIsometryEquiv.apply_symm_apply]

theorem inner_rowsW2L (B : MQ) (w : Wv W2) :
    ⟪rowsW2L B, w⟫_ℝ = RCLike.re ⟪B, ofRealRows2 fun a => cQ _ (w a)⟫_ℂ := by
  rw [re_inner_ofRealRows2, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rowsW2L_apply, ← LinearIsometryEquiv.inner_map_map (cQ _),
    LinearIsometryEquiv.apply_symm_apply]

/-- **Bottom `1`-forms as matrix fields lie in `D((S₁, curl))`.** -/
theorem ofRealRows_BU1_mem (v : BU1) :
    ∃ h : ofRealRows (fun a => cQ _ ((v a : (BD1 a).domain) : W1)) ∈
        (MirrorBGG.complexQ.d 1 2).domain,
      (MirrorBGG.complexQ.d 1 2 ⟨_, h⟩ : MirrorBGG.W2Q) = WithLp.toLp 2
        (MirrorBGG.axialQ (ofRealRows fun a => cQ _ ((v a : (BD1 a).domain) : W1)),
          ofRealRows2 fun a => cQ _ (bD1 v a)) := by
  have hv : ∀ a, cQ _ ((v a : (BD1 a).domain) : W1) ∈
      (dPart (Q (Fin 3)) {a} ((1 : ℕ) : ℤ)).domain := fun a => (dPart_Q_of_cube (v a)).1
  obtain ⟨h, e⟩ := ofRealRows_mem _ hv
  refine ⟨h, e.trans ?_⟩
  congr 3
  funext a
  rw [bD1_apply]
  exact (dPart_Q_of_cube (v a)).2

/-! ### `S¹` on the matrix proxy -/

theorem wsL2_castL2 {Ω : Set (Fin 3 → ℝ)} (h : Ω = Q (Fin 3))
    (v : PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 1))) :
    castL2 h _ (wsL2 (Ω := Ω) 1 v) =
      wsL2 (Ω := Q (Fin 3)) 1 (WithLp.toLp 2 fun a => castL2 h _ (v a)) := by
  subst h; rfl

/-- **`S¹` vanishes on the proxy of a symmetric matrix field.** -/
theorem wsL2_rowsW1L_of_symm {E : MQ} (hE : ∀ i j, E (i, j) = E (j, i)) :
    wsL2 (Ω := cubeDomain 3) 1 (rowsW1L E) = 0 := by
  have h := wsL2_castL2 (cubeDomain_eq_Q 3) (rowsW1L E)
  have e : (WithLp.toLp 2 fun a => castL2 (cubeDomain_eq_Q 3) _ (rowsW1L E a) :
      PiLp 2 (fun _ : Fin 3 => L2F ℝ (Q (Fin 3)) (formIdx 3 1))) =
        WithLp.toLp 2 fun a => rowRe E a := by
    refine PiLp.ext fun a => ?_
    simp only [rowsW1L_apply]
    exact LinearIsometryEquiv.apply_symm_apply _ _
  have h0 : wsL2 (Ω := Q (Fin 3)) 1 (WithLp.toLp 2 fun a => rowRe E a :
      PiLp 2 (fun _ : Fin 3 => L2F ℝ (Q (Fin 3)) (formIdx 3 1))) = 0 :=
    wsL2_eq_zero_of_symm _ fun a b => by
      change rowRe E a (eq1 b) = rowRe E b (eq1 a)
      rw [rowRe_eq1, rowRe_eq1, hE]
  rw [e, h0] at h
  exact (castL2 (cubeDomain_eq_Q 3) _).map_eq_zero_iff.1 h

/-! ### The TSD solution of the Ch. 6 system on `Q` -/

open Feec.HilbertComplex (totalSub)

/-- **A TSD datum in `D(L²)`** for the Ch. 6 system on `Q` with mirror boundary conditions
(`Feec.Models.Cube.MirrorBGG.complexQ`): `U₀ ∈ D(L)`, `L U₀ ∈ D(L)`, and `U₀` in the constraint
`{0} × L²(TSD) × ({0} × L²(TSD))`. -/
structure TSDDatum where
  /-- The initial state `(σ₀, E₀, (M₀, B₀))`. -/
  U₀ : PiLp 2 MirrorBGG.SpaceQ
  mem : U₀ ∈ MirrorBGG.complexQ.wave.domain
  mem₂ : MirrorBGG.complexQ.wave ⟨U₀, mem⟩ ∈ MirrorBGG.complexQ.wave.domain
  tsd : U₀ ∈ totalSub MirrorBGG.tsdQ

namespace TSDDatum

variable (D : TSDDatum)

/-- `L U₀`. -/
def LU₀ : PiLp 2 MirrorBGG.SpaceQ := MirrorBGG.complexQ.wave ⟨D.U₀, D.mem⟩

/-- `L² U₀`. -/
def LLU₀ : PiLp 2 MirrorBGG.SpaceQ := MirrorBGG.complexQ.wave ⟨D.LU₀, D.mem₂⟩

/-- **The TSD solution** `U(t) = e^{tL} U₀`. -/
def U (t : ℝ) : PiLp 2 MirrorBGG.SpaceQ := MirrorBGG.complexQ.waveGroup.S t D.U₀

/-- `U'(t) = e^{tL} L U₀`. -/
def V (t : ℝ) : PiLp 2 MirrorBGG.SpaceQ := MirrorBGG.complexQ.waveGroup.S t D.LU₀

/-- `U''(t) = e^{tL} L² U₀`. -/
def W (t : ℝ) : PiLp 2 MirrorBGG.SpaceQ := MirrorBGG.complexQ.waveGroup.S t D.LLU₀

end TSDDatum

/-- The wave group maps `D(L)` into `D(L)` and commutes with `L` (`t ≥ 0`). -/
theorem waveGroupQ_graph {x : PiLp 2 MirrorBGG.SpaceQ} (hx : x ∈ MirrorBGG.complexQ.wave.domain)
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ h : MirrorBGG.complexQ.waveGroup.S t x ∈ MirrorBGG.complexQ.wave.domain,
      MirrorBGG.complexQ.wave ⟨_, h⟩ =
        MirrorBGG.complexQ.waveGroup.S t (MirrorBGG.complexQ.wave ⟨x, hx⟩) := by
  have hg : (x, MirrorBGG.complexQ.wave ⟨x, hx⟩) ∈
      MirrorBGG.complexQ.waveGroup.toC0Semigroup.generator.graph := by
    change _ ∈ MirrorBGG.complexQ.waveGroup.generator.graph
    rw [HilbertComplex.generator_waveGroup]
    exact LinearPMap.mem_graph _ ⟨x, hx⟩
  have h2 := MirrorBGG.complexQ.waveGroup.toC0Semigroup.S_mem_graph hg ht
  change _ ∈ MirrorBGG.complexQ.waveGroup.generator.graph at h2
  rw [HilbertComplex.generator_waveGroup] at h2
  have hm := LinearPMap.mem_domain_of_mem_graph h2
  exact ⟨hm, ((LinearPMap.image_iff hm).2 h2).symm⟩

/-- The orbit of `x ∈ D(L)` has right derivative `e^{tL} L x`. -/
theorem waveGroupQ_hasDerivWithinAt {x : PiLp 2 MirrorBGG.SpaceQ}
    (hx : x ∈ MirrorBGG.complexQ.wave.domain) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => MirrorBGG.complexQ.waveGroup.S s x)
      (MirrorBGG.complexQ.waveGroup.S t (MirrorBGG.complexQ.wave ⟨x, hx⟩)) (Ici t) t := by
  have hx' : x ∈ MirrorBGG.complexQ.waveGroup.toC0Semigroup.generator.domain := by
    change x ∈ MirrorBGG.complexQ.waveGroup.generator.domain
    rw [HilbertComplex.generator_waveGroup]; exact hx
  have h := MirrorBGG.complexQ.waveGroup.toC0Semigroup.hasDerivWithinAt_Ici_apply ⟨x, hx'⟩ ht
  have e : MirrorBGG.complexQ.waveGroup.toC0Semigroup.generator ⟨x, hx'⟩ =
      MirrorBGG.complexQ.wave ⟨x, hx⟩ :=
    LinearPMap.apply_eq_of_eq (HilbertComplex.generator_waveGroup MirrorBGG.complexQ) ⟨x, hx'⟩
      ⟨x, hx⟩ rfl
  rw [e] at h
  exact h

/-- In a constrained state, `(L x)₁ = -d₁† x₂`. -/
theorem waveQ_one_of_tsd (x : MirrorBGG.complexQ.wave.domain)
    (hx : (x : PiLp 2 MirrorBGG.SpaceQ) ∈ totalSub MirrorBGG.tsdQ) :
    (MirrorBGG.complexQ.wave x) 1 =
      -(MirrorBGG.complexQ.d 1 2)† ⟨(x : PiLp 2 MirrorBGG.SpaceQ) 2, x.2.2 2 1⟩ := by
  rw [HilbertComplex.wave_apply_fin3_one]
  have h0 : ((x : PiLp 2 MirrorBGG.SpaceQ) 0 : MirrorBGG.SpaceQ 0) = 0 :=
    (MirrorBGG.mem_tsdQ_iff.1 hx).1
  have e : MirrorBGG.complexQ.d 0 1 ⟨(x : PiLp 2 MirrorBGG.SpaceQ) 0, x.2.1 0 1⟩ = 0 := by
    rw [LinearPMap.apply_congr' _ _ (Submodule.zero_mem _) h0]
    exact LinearPMap.map_zero _
  rw [e, zero_sub]

/-- The magnetic slot `(M, B)` of a state. -/
def stW2 (x : PiLp 2 MirrorBGG.SpaceQ) : MirrorBGG.W2Q := x 2

/-- The electric slot `E` of a state. -/
def stE (x : PiLp 2 MirrorBGG.SpaceQ) : MQ := x 1

/-- **The complex form of `E' = -d₁† (M, B)`**: `⟪(L x)₁, X⟫ = -⟪x₂, d₁ X⟫`. -/
theorem inner_waveQ_one (x : MirrorBGG.complexQ.wave.domain)
    (hx : (x : PiLp 2 MirrorBGG.SpaceQ) ∈ totalSub MirrorBGG.tsdQ)
    (Xm : MQ) (hX : Xm ∈ (MirrorBGG.complexQ.d 1 2).domain) :
    ⟪stE (MirrorBGG.complexQ.wave x), Xm⟫_ℂ =
      -⟪stW2 x, (MirrorBGG.complexQ.d 1 2 ⟨Xm, hX⟩ : MirrorBGG.W2Q)⟫_ℂ := by
  have e' : stE (MirrorBGG.complexQ.wave x) =
      -((MirrorBGG.complexQ.d 1 2)† ⟨(x : PiLp 2 MirrorBGG.SpaceQ) 2, x.2.2 2 1⟩ : MQ) :=
    waveQ_one_of_tsd x hx
  have h2 := LinearPMap.adjoint_isFormalAdjoint (MirrorBGG.complexQ.dense 1 2)
    ⟨(x : PiLp 2 MirrorBGG.SpaceQ) 2, x.2.2 2 1⟩ ⟨Xm, hX⟩
  rw [e']
  exact (inner_neg_left _ _).trans (congrArg Neg.neg h2)

/-! ### The forms state of a constrained state of `D(L)` -/

/-- The electric slot `E` of a state. -/
def stEL : PiLp 2 MirrorBGG.SpaceQ →L[ℝ] MQ :=
  (PiLp.proj (𝕜 := ℂ) 2 MirrorBGG.SpaceQ (1 : Fin 3)).restrictScalars ℝ

/-- The magnetic slot `B` of a state. -/
def stBL : PiLp 2 MirrorBGG.SpaceQ →L[ℝ] MQ :=
  ((ContinuousLinearMap.snd ℂ Mirror.VQ MQ) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℂ Mirror.VQ MQ).toContinuousLinearMap ∘L
      (PiLp.proj (𝕜 := ℂ) 2 MirrorBGG.SpaceQ (2 : Fin 3) :
        PiLp 2 MirrorBGG.SpaceQ →L[ℂ] MirrorBGG.W2Q)).restrictScalars ℝ

theorem stEL_apply (x : PiLp 2 MirrorBGG.SpaceQ) : stEL x = stE x := rfl
theorem stBL_apply (x : PiLp 2 MirrorBGG.SpaceQ) : stBL x = (WithLp.ofLp (stW2 x)).2 := rfl

theorem isometry_bIncl1 : Isometry bIncl1 := AddMonoidHomClass.isometry_of_norm bIncl1 norm_bIncl1

/-- Derivatives through a linear isometry. -/
theorem hasDerivWithinAt_of_isometry {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (ι : E →ₗ[ℝ] F) (hι : ∀ x, ‖ι x‖ = ‖x‖)
    {f : ℝ → E} {y : E} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt (fun r => ι (f r)) (ι y) s t) : HasDerivWithinAt f y s t := by
  rw [hasDerivWithinAt_iff_isLittleO] at h ⊢
  rw [← Asymptotics.isLittleO_norm_left] at h ⊢
  have e : (fun r => ‖f r - f t - (r - t) • y‖) =
      fun r => ‖ι (f r) - ι (f t) - (r - t) • ι y‖ := by
    funext r
    rw [← map_sub, ← map_smul, ← map_sub, hι]
  rw [e]
  exact h

section State

variable (x : MirrorBGG.complexQ.wave.domain)

/-- The electric slot is in `D((S₁, curl))`. -/
abbrev eDom : (MirrorBGG.complexQ.d 1 2).domain := ⟨(x : PiLp 2 MirrorBGG.SpaceQ) 1, x.2.1 1 2⟩

theorem stBL_wave : stBL (MirrorBGG.complexQ.wave x) =
    (WithLp.ofLp (MirrorBGG.complexQ.d 1 2 (eDom x) : MirrorBGG.W2Q)).2 := by
  have h := HilbertComplex.wave_apply_fin3_two MirrorBGG.complexQ x
  exact congrArg (fun z : MirrorBGG.W2Q => (WithLp.ofLp z).2) h

theorem bIncl1_rowsBU_state :
    bIncl1 (rowsBU (stEL x)) = rowsW1L (stEL x) := bIncl1_rowsBU (eDom x)

theorem bD1_rowsBU_state :
    bD1 (rowsBU (stEL x)) = rowsW2L (stBL (MirrorBGG.complexQ.wave x)) := by
  rw [stBL_wave]; exact bD1_rowsBU (eDom x)

variable {x} (hx : (x : PiLp 2 MirrorBGG.SpaceQ) ∈ totalSub MirrorBGG.tsdQ)
include hx

/-- **`S¹ u = 0`**: the electric field of a constrained state is symmetric. -/
theorem mS1_rowsBU_state : mS1 (rowsBU (stEL x)) = 0 := by
  rw [mS1_apply, bIncl1_rowsBU_state]
  exact wsL2_rowsW1L_of_symm (MirrorBGG.tsd_of_mem_tsdQ hx).2.2.1.1

/-- **`⟪u, grad ψ⟫ = 0`**: the electric field of a constrained state is divergence-free against the
bottom `0`-forms. -/
theorem inner_rowsBU_bD0 (ψ : BU0) : ⟪rowsBU (stEL x), bD0 ψ⟫_ℝ = 0 := by
  rw [inner_BU1, bIncl1_rowsBU_state, PiLp.inner_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [rowsW1L_apply, bIncl1_apply, bD0_apply, ← LinearIsometryEquiv.inner_map_map (cQ _),
    LinearIsometryEquiv.apply_symm_apply]
  obtain ⟨hψ, eψ⟩ := dPart_Q_of_cube (ψ a)
  have hE : ∀ n, (MirrorBGG.J₁ (stEL x) : (Fin 3 → ℤ) → Mat) n ∈
      Fourier.GradCurl.tsd (Fourier.Torus.freq n) := fun n =>
    Measure.ae_count_iff.1 (Operator.mem_fibreSub.1 (hx 1)) n
  have h := inner_rowRe_dPart_zero (stEL x) hE a ⟨_, hψ⟩
  calc _ = ⟪rowRe (stEL x) a, (dPart (Q (Fin 3)) {a} ((0 : ℕ) : ℤ) ⟨_, hψ⟩ :
        L2F ℝ (Q (Fin 3)) (formIdx 3 ((1 : ℕ) : ℤ)))⟫_ℝ :=
          congrArg (fun z => ⟪rowRe (stEL x) a, z⟫_ℝ) eψ.symm
    _ = 0 := h

/-- **`⟪u', v⟫ + ⟪ρ, d v⟫ = 0`**: the equation `E' = -d₁† (0, B)` of a constrained state, in the
forms model. -/
theorem inner_rowsBU_wave_add (hL : MirrorBGG.complexQ.wave x ∈ MirrorBGG.complexQ.wave.domain)
    (v : BU1) :
    ⟪rowsBU (stEL (MirrorBGG.complexQ.wave x)), v⟫_ℝ + ⟪rowsW2L (stBL x), bD1 v⟫_ℝ = 0 := by
  rw [inner_BU1, bIncl1_rowsBU_state (x := ⟨_, hL⟩), inner_rowsW1L, inner_rowsW2L]
  obtain ⟨hX, eX⟩ := ofRealRows_BU1_mem v
  have hM : (WithLp.ofLp (stW2 x)).1 = 0 := (MirrorBGG.mem_tsdQ_iff.1 hx).2.2.1
  rw [stEL_apply, inner_waveQ_one x hx _ hX, eX, WithLp.prod_inner_apply, WithLp.ofLp_toLp, hM,
    inner_zero_left, zero_add, map_neg, stBL_apply]
  exact neg_add_cancel _

end State

/-! ### The TSD solution as a classical solution of (6.2) -/

namespace TSDDatum

variable (D : TSDDatum)

theorem U_mem {t : ℝ} (ht : 0 ≤ t) : D.U t ∈ MirrorBGG.complexQ.wave.domain :=
  (waveGroupQ_graph D.mem ht).1

theorem wave_U {t : ℝ} (ht : 0 ≤ t) : MirrorBGG.complexQ.wave ⟨D.U t, D.U_mem ht⟩ = D.V t :=
  (waveGroupQ_graph D.mem ht).2

theorem V_mem {t : ℝ} (ht : 0 ≤ t) : D.V t ∈ MirrorBGG.complexQ.wave.domain :=
  (waveGroupQ_graph D.mem₂ ht).1

theorem wave_V {t : ℝ} (ht : 0 ≤ t) : MirrorBGG.complexQ.wave ⟨D.V t, D.V_mem ht⟩ = D.W t :=
  (waveGroupQ_graph D.mem₂ ht).2

theorem hasDerivWithinAt_U {t : ℝ} (ht : 0 ≤ t) : HasDerivWithinAt D.U (D.V t) (Ici t) t :=
  waveGroupQ_hasDerivWithinAt D.mem ht

theorem hasDerivWithinAt_V {t : ℝ} (ht : 0 ≤ t) : HasDerivWithinAt D.V (D.W t) (Ici t) t :=
  waveGroupQ_hasDerivWithinAt D.mem₂ ht

theorem continuous_U : Continuous D.U := MirrorBGG.complexQ.waveGroup.strongCont D.U₀
theorem continuous_V : Continuous D.V := MirrorBGG.complexQ.waveGroup.strongCont D.LU₀
theorem continuous_W : Continuous D.W := MirrorBGG.complexQ.waveGroup.strongCont D.LLU₀

theorem U_tsd (t : ℝ) : D.U t ∈ totalSub MirrorBGG.tsdQ :=
  MirrorBGG.reducingSubcomplexQ.waveGroup_mem t D.tsd

theorem LU₀_tsd : D.LU₀ ∈ totalSub MirrorBGG.tsdQ :=
  MirrorBGG.reducingSubcomplexQ.isReducing_wave.mapsTo ⟨D.U₀, D.mem⟩ D.tsd

theorem V_tsd (t : ℝ) : D.V t ∈ totalSub MirrorBGG.tsdQ :=
  MirrorBGG.reducingSubcomplexQ.waveGroup_mem t D.LU₀_tsd

/-- `d u = ρ'` along the solution. -/
theorem bD1_u {t : ℝ} (ht : 0 ≤ t) : bD1 (rowsBU (stEL (D.U t))) = rowsW2L (stBL (D.V t)) := by
  rw [bD1_rowsBU_state ⟨D.U t, D.U_mem ht⟩, D.wave_U ht]

theorem bD1_u' {t : ℝ} (ht : 0 ≤ t) : bD1 (rowsBU (stEL (D.V t))) = rowsW2L (stBL (D.W t)) := by
  rw [bD1_rowsBU_state ⟨D.V t, D.V_mem ht⟩, D.wave_V ht]

theorem bIncl1_u {t : ℝ} (ht : 0 ≤ t) : bIncl1 (rowsBU (stEL (D.U t))) = rowsW1L (stEL (D.U t)) :=
  bIncl1_rowsBU_state ⟨D.U t, D.U_mem ht⟩

theorem bIncl1_u' {t : ℝ} (ht : 0 ≤ t) :
    bIncl1 (rowsBU (stEL (D.V t))) = rowsW1L (stEL (D.V t)) :=
  bIncl1_rowsBU_state ⟨D.V t, D.V_mem ht⟩

theorem mS1_u {t : ℝ} (ht : 0 ≤ t) : mS1 (rowsBU (stEL (D.U t))) = 0 :=
  mS1_rowsBU_state (x := ⟨D.U t, D.U_mem ht⟩) (D.U_tsd t)

theorem mS1_u' {t : ℝ} (ht : 0 ≤ t) : mS1 (rowsBU (stEL (D.V t))) = 0 :=
  mS1_rowsBU_state (x := ⟨D.V t, D.V_mem ht⟩) (D.V_tsd t)

set_option maxHeartbeats 4000000 in
/-- **The TSD solution of the Ch. 6 system on `Q` as a classical solution of the multiplier
problem (6.2) for the mirror data**: `σ ≡ 0`, `φ ≡ 0`, `u` the real rows of `E`, `M ≡ 0`, `ρ` the
real rows of `B` through the Hodge star, multiplier `ℓ ≡ 0`, no source. The equations: `E` is
divergence-free against the bottom `0`-forms (6.2a), `E' = -curl* B` (6.2b), `S¹E = 0` since `E` is
symmetric (6.2c), `B' = curl E` (6.2d). See [QuennevilleBelair2015], §6.1, (6.2), and Ch. 6
(corrected). -/
def exactWave (T : ℝ) : Feec.BGG.ExactWave mirrorBGGSegment T (mirrorSrcFun 0) where
  σ _ := 0
  φ _ := 0
  u t := rowsBU (stEL (D.U t))
  M _ := 0
  ρ t := rowsW2L (stBL (D.U t))
  ℓ _ := 0
  σ' _ := 0
  φ' _ := 0
  u' t := rowsBU (stEL (D.V t))
  M' _ := 0
  ρ' t := rowsW2L (stBL (D.V t))
  ℓ' _ := 0
  cσ := continuousOn_const
  cu := isometry_bIncl1.comp_continuousOn_iff.1
    (((rowsW1L.comp stEL).continuous.comp D.continuous_U).continuousOn.congr fun t ht =>
      D.bIncl1_u ht.1)
  cM := continuousOn_const
  cρ := ((rowsW2L.comp stBL).continuous.comp D.continuous_U).continuousOn
  cdφ := continuousOn_const.congr fun _ _ => map_zero _
  cSu := (continuousOn_const (c := (0 : W2))).congr fun _ ht => D.mS1_u ht.1
  cdu := ((rowsW2L.comp stBL).continuous.comp D.continuous_V).continuousOn.congr fun _ ht =>
    D.bD1_u ht.1
  cℓ _ := continuousOn_const
  cσ' := continuousOn_const
  cu' := isometry_bIncl1.comp_continuousOn_iff.1
    (((rowsW1L.comp stEL).continuous.comp D.continuous_V).continuousOn.congr fun t ht =>
      D.bIncl1_u' ht.1)
  cM' := continuousOn_const
  cρ' := ((rowsW2L.comp stBL).continuous.comp D.continuous_V).continuousOn
  cdφ' := continuousOn_const.congr fun _ _ => map_zero _
  cSu' := (continuousOn_const (c := (0 : W2))).congr fun _ ht => D.mS1_u' ht.1
  cdu' := ((rowsW2L.comp stBL).continuous.comp D.continuous_W).continuousOn.congr fun _ ht =>
    D.bD1_u' ht.1
  cℓ' _ := continuousOn_const
  dσ _ _ := hasDerivWithinAt_const _ _ _
  du t ht := hasDerivWithinAt_of_isometry bIncl1 norm_bIncl1
    ((((rowsW1L.comp stEL).hasFDerivAt.comp_hasDerivWithinAt t (D.hasDerivWithinAt_U ht.1)).congr
      (fun r hr => D.bIncl1_u (ht.1.trans hr)) (D.bIncl1_u ht.1)).congr_deriv
        (D.bIncl1_u' ht.1).symm)
  dM _ _ := hasDerivWithinAt_const _ _ _
  dρ t ht := (rowsW2L.comp stBL).hasFDerivAt.comp_hasDerivWithinAt t (D.hasDerivWithinAt_U ht.1)
  ddφ _ _ := by simpa using hasDerivWithinAt_const _ _ (mirrorBGGSegment.dt0 0)
  dSu t ht := ((hasDerivWithinAt_const t (Ici t) (0 : W2)).congr
    (fun r hr => D.mS1_u (ht.1.trans hr)) (D.mS1_u ht.1)).congr_deriv (D.mS1_u' ht.1).symm
  ddu t ht := (((rowsW2L.comp stBL).hasFDerivAt.comp_hasDerivWithinAt t
    (D.hasDerivWithinAt_V ht.1)).congr (fun r hr => D.bD1_u (ht.1.trans hr))
      (D.bD1_u ht.1)).congr_deriv
      (D.bD1_u' ht.1).symm
  dℓ _ _ _ := hasDerivWithinAt_const _ _ _
  ea t ht τ ψ := by
    have h := inner_rowsBU_bD0 (x := ⟨D.U t, D.U_mem ht.1⟩) (D.U_tsd t) ψ
    change ⟪(0 : TU0), τ⟫_ℝ - ⟪rowsBU (stEL (D.U t)), bD0 ψ⟫_ℝ - (0 : TU1 →ₗ[ℝ] ℝ) _ = 0
    rw [h, inner_zero_left, LinearMap.zero_apply]
    ring
  eb t ht v := by
    have h := inner_rowsBU_wave_add (x := ⟨D.U t, D.U_mem ht.1⟩) (D.U_tsd t)
      (by rw [D.wave_U ht.1]; exact D.V_mem ht.1) v
    rw [D.wave_U ht.1] at h
    change ⟪rowsBU (stEL (D.V t)), v⟫_ℝ + ⟪bD0 0, v⟫_ℝ + ⟪(0 : W2), mS1 v⟫_ℝ +
      ⟪rowsW2L (stBL (D.U t)), bD1 v⟫_ℝ = mirrorSrcFun 0 t v
    rw [map_zero, inner_zero_left, inner_zero_left, mirrorSrcFun_apply, Pi.zero_apply,
      inner_zero_left]
    linarith
  ec t ht N := by
    change ⟪(0 : W2), N⟫_ℝ - ⟪mS1 (rowsBU (stEL (D.U t))), N⟫_ℝ = 0
    rw [D.mS1_u ht.1, inner_zero_left, sub_zero]
  ed t ht μ := by
    change ⟪rowsW2L (stBL (D.V t)), μ⟫_ℝ - ⟪bD1 (rowsBU (stEL (D.U t))), μ⟫_ℝ = 0
    rw [D.bD1_u ht.1, sub_self]
  ee _ _ := (map_zero _).trans (map_zero _).symm
  ee' _ _ := (map_zero _).trans (map_zero _).symm

end TSDDatum

/-! ### Identification with the solution of `MirrorBGG.existsUnique_memQ` -/

namespace TSDDatum

variable (D : TSDDatum)

theorem U_zero : D.U 0 = D.U₀ := by
  simp [TSDDatum.U, MirrorBGG.complexQ.waveGroup.map_zero]

/-- `U(t) = e^{tL} U₀` is a (classical, hence) strong solution of `U' = L U` on `[0,T]`. -/
theorem isStrongSolution (T : ℝ) :
    Evolution.IsStrongSolution MirrorBGG.complexQ.wave (Icc 0 T) 0 D.U := by
  have hx : D.U₀ ∈ MirrorBGG.complexQ.waveGroup.toC0Semigroup.generator.domain := by
    change D.U₀ ∈ MirrorBGG.complexQ.waveGroup.generator.domain
    rw [HilbertComplex.generator_waveGroup]; exact D.mem
  have h :=
    (MirrorBGG.complexQ.waveGroup.toC0Semigroup.isClassicalSolution_orbit hx 0 T).toIsStrongSolution
  have e : (fun t => MirrorBGG.complexQ.waveGroup.toC0Semigroup.S (t - 0) D.U₀) = D.U := by
    funext t; simp [TSDDatum.U]
  rw [e] at h
  change Evolution.IsStrongSolution MirrorBGG.complexQ.waveGroup.generator _ _ _ at h
  rwa [HilbertComplex.generator_waveGroup] at h

/-- **The solution of `Feec.Models.Cube.MirrorBGG.existsUnique_memQ` is `e^{tL} U₀`**: every strong
solution of the Ch. 6 system on `Q` from `U₀` agrees with `D.U` on `[0,T]`. -/
theorem eqOn_of_isStrongSolution {T : ℝ} {U : ℝ → PiLp 2 MirrorBGG.SpaceQ} (h0 : U 0 = D.U₀)
    (hU : Evolution.IsStrongSolution MirrorBGG.complexQ.wave (Icc 0 T) 0 U) :
    EqOn U D.U (Icc 0 T) := by
  have hadm : Evolution.ForcingClass.admissible MirrorBGG.complexQ.wave 0 T 0 :=
    Evolution.ForcingClass.contDomain.admissible ⟨fun _ _ => Submodule.zero_mem _,
      continuousOn_const, 0, continuousOn_const, fun _ _ => by convert LinearPMap.map_zero _⟩
  obtain ⟨W, -, -, -, huniq⟩ := MirrorBGG.existsUnique_memQ D.mem D.tsd hadm
    fun _ _ => Submodule.zero_mem _
  exact fun t ht => (huniq U h0 hU ht).trans (huniq D.U D.U_zero (D.isStrongSolution T) ht).symm

end TSDDatum

/-! ### The matrix proxy of the bottom `2`-forms -/

/-- **The matrix proxy of the bottom `2`-forms**: `ρ ↦ B`, `B_{ai} = ± ρ_a(⋆dx_i)` (inverse of
`rowsW2L` on real fields). -/
def matB (w : Wv W2) : MQ :=
  WithLp.toLp 2 fun p => (sg2 p.2 : ℂ) • ofRealL _ (cQ (formIdx 3 ((2 : ℕ) : ℤ)) (w p.1) (eq2 p.2))

theorem matB_sub (w w' : Wv W2) : matB (w - w') = matB w - matB w' := by
  refine PiLp.ext fun p => ?_
  simp only [matB, PiLp.toLp_apply, PiLp.sub_apply, map_sub, smul_sub]

theorem norm_ofRealL {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : Lp ℝ 2 μ) :
    ‖ofRealL μ f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  exact eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    ((coeFn_ofRealL f).mono fun x hx => by rw [hx, Complex.norm_real])

theorem norm_matB (w : Wv W2) : ‖matB w‖ = ‖w‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← LinearIsometryEquiv.norm_map (cQ (formIdx 3 ((2 : ℕ) : ℤ))) (w a), PiLp.norm_sq_eq_of_L2]
  refine Eq.trans ?_ (Fintype.sum_equiv eq2
    (fun i => ‖(cQ (formIdx 3 ((2 : ℕ) : ℤ)) (w a)) (eq2 i)‖ ^ 2)
    (fun s => ‖(cQ (formIdx 3 ((2 : ℕ) : ℤ)) (w a)) s‖ ^ 2) fun _ => rfl)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [matB, PiLp.toLp_apply, norm_smul, norm_ofRealL]
  have : ‖(sg2 i : ℂ)‖ = 1 := by unfold sg2; split_ifs <;> simp
  rw [this, one_mul]

/-- The transpose of matrix fields. -/
def transposeQ (X : MQ) : MQ := WithLp.toLp 2 fun p => X (p.2, p.1)

theorem transposeQ_sub (X Y : MQ) : transposeQ (X - Y) = transposeQ X - transposeQ Y := by
  refine PiLp.ext fun p => ?_
  simp [transposeQ]

theorem norm_transposeQ (X : MQ) : ‖transposeQ X‖ = ‖X‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  exact Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun p => rfl

theorem matB_rowsW2L (B : MQ) (p : Fin 3 × Fin 3) :
    matB (rowsW2L B) p = ofRealL _ (reL _ (B p)) := by
  rw [matB, PiLp.toLp_apply, rowsW2L_apply, LinearIsometryEquiv.apply_symm_apply, rowRe2_eq2,
    map_smul, real_smul_Lp, smul_smul, ← Complex.ofReal_mul, sg2_mul_self, Complex.ofReal_one,
    one_smul]

theorem transposeQ_matB_rowsW2L {B : MQ} (hB : ∀ i j, B (i, j) = B (j, i)) :
    transposeQ (matB (rowsW2L B)) = matB (rowsW2L B) := by
  refine PiLp.ext fun p => ?_
  rw [transposeQ, PiLp.toLp_apply, matB_rowsW2L, matB_rowsW2L, hB]

/-- **`‖B_h − B_hᵀ‖ ≤ 2 ‖ρ − ρ_h‖`** when `ρ` is the proxy of a symmetric field. -/
theorem norm_matB_sub_transpose_le {B : MQ} (hB : ∀ i j, B (i, j) = B (j, i)) (w : Wv W2) :
    ‖matB w - transposeQ (matB w)‖ ≤ 2 * ‖rowsW2L B - w‖ := by
  have e : matB w - transposeQ (matB w) =
      transposeQ (matB (rowsW2L B - w)) - matB (rowsW2L B - w) := by
    rw [matB_sub, transposeQ_sub, transposeQ_matB_rowsW2L hB]
    abel
  rw [e]
  calc _ ≤ ‖transposeQ (matB (rowsW2L B - w))‖ + ‖matB (rowsW2L B - w)‖ := norm_sub_le _ _
    _ = 2 * ‖rowsW2L B - w‖ := by rw [norm_transposeQ, norm_matB]; ring

open Feec.Models.Cube.Mirror (k0 M0 cosCoeff cosCoeff_eq_zero cosE coe_cosE)

/-! ### Convergence of the mirror scheme (6.5) to the TSD solution -/

section Main

open Feec.Models.Cube.FEM Feec.Mesh Feec.FiniteElement

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C)

theorem sqrt_four_le {a b c d ε : ℝ} (h : √(a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ≤ ε) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) : a ≤ ε ∧ b ≤ ε ∧ c ≤ ε ∧ d ≤ ε := by
  have k : ∀ x : ℝ, 0 ≤ x → x ^ 2 ≤ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 → x ≤ ε := fun x hx hxE =>
    ((abs_of_nonneg hx).symm.le.trans (Real.abs_le_sqrt hxE)).trans h
  have p1 := sq_nonneg a; have p2 := sq_nonneg b; have p3 := sq_nonneg c; have p4 := sq_nonneg d
  exact ⟨k a ha (by linarith), k b hb (by linarith), k c hc (by linarith), k d hd (by linarith)⟩

theorem sqrt_four_congr {a b c d a' b' c' d' K : ℝ} (h : √(a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ≤ K)
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') :
    √(a' ^ 2 + b' ^ 2 + c' ^ 2 + d' ^ 2) ≤ K := by
  subst ha hb hc hd; exact h

theorem norm_zero_sub' {E : Type*} [SeminormedAddCommGroup E] (x : E) : ‖(0 : E) - x‖ = ‖x‖ := by
  rw [zero_sub, norm_neg]

theorem TSDDatum.norm_exactWave_u_sub (D : TSDDatum) {T : ℝ} {U : ℝ → PiLp 2 MirrorBGG.SpaceQ}
    (hEq : EqOn U D.U (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) (v : BU1) :
    ‖(D.exactWave T).u t - v‖ = ‖rowsW1L (stEL (U t)) - bIncl1 v‖ := by
  rw [hEq ht, ← D.bIncl1_u ht.1, ← map_sub, norm_bIncl1]
  rfl

theorem TSDDatum.norm_exactWave_ρ_sub (D : TSDDatum) {T : ℝ} {U : ℝ → PiLp 2 MirrorBGG.SpaceQ}
    (hEq : EqOn U D.U (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) (w : Wv W2) :
    ‖(D.exactWave T).ρ t - w‖ = ‖rowsW2L (stBL (U t)) - w‖ := by
  rw [hEq ht]; rfl

/-- The componentwise bounds, `σₕ`, `Mₕ` small and `Bₕ` nearly symmetric. -/
theorem tsd_bounds {X Y : Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]
    {x : X} {y : Y} {z : Wv W1} {B : MQ} {w : Wv W2} {ε : ℝ}
    (h : √(‖x‖ ^ 2 + ‖z‖ ^ 2 + ‖y‖ ^ 2 + ‖rowsW2L B - w‖ ^ 2) ≤ ε)
    (hB : ∀ i j, B (i, j) = B (j, i)) :
    ‖x‖ ≤ ε ∧ ‖z‖ ≤ ε ∧ ‖y‖ ≤ ε ∧ ‖rowsW2L B - w‖ ≤ ε ∧
      ‖matB w - transposeQ (matB w)‖ ≤ 2 * ε := by
  obtain ⟨b1, b2, b3, b4⟩ := sqrt_four_le h (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _)
  exact ⟨b1, b2, b3, b4, (norm_matB_sub_transpose_le hB w).trans (by linarith)⟩

/-- **The mirror scheme (6.5) converges to the TSD solution of the Ch. 6 system on `Q`**, the main
theorem of the mirror repair of [QuennevilleBelair2015], Ch. 6. Let `U₀ ∈ D(L²)` lie in the
constraint `{0} × L²(TSD) × ({0} × L²(TSD))` (`TSDDatum`), and let `U` be its solution of the Hodge
wave equation of the mirror BGG complex on `Q` (`Feec.Models.Cube.MirrorBGG.existsUnique_memQ`;
every strong solution from `U₀` qualifies, `TSDDatum.eqOn_of_isStrongSolution`). Then:
* `U(t)` stays in the constraint on `[0,T]`: `σ ≡ 0`, `M ≡ 0`, `E` and `B` TSD;
* for every `ε > 0` and all large `N`, the scheme (6.5) without source, started from the elliptic
  projection (6.4) of the forms state `(0, 0, Re E₀, 0, Re B₀)`, has a
  solution with, on `[0,T]`, `‖σₕ‖ ≤ ε`, `‖Re E − uₕ‖ ≤ ε`, `‖Mₕ‖ ≤ ε`, `‖Re B − ρₕ‖ ≤ ε` (rows of
  the matrix fields as forms, `B` through the Hodge star) and `‖Bₕ − Bₕᵀ‖ ≤ 2ε` for the matrix proxy
  `Bₕ = matB ρₕ`: `σₕ → 0`, `Mₕ → 0` and `Bₕ` becomes symmetric.
The scheme computes the real part `Re U`; the imaginary part is the real part of the solution from
`-i U₀`. The proof identifies `Re U` with a classical solution of (6.2) for the mirror data
(`TSDDatum.exactWave`, on the Fourier side of the parity models) and applies
`mirrorWave_converges`. See [QuennevilleBelair2015], Ch. 6, §6.3, (6.5). -/
theorem mirror_waveFEM (D : TSDDatum) {T : ℝ} (hT0 : 0 < T)
    {U : ℝ → PiLp 2 MirrorBGG.SpaceQ} (hU0 : U 0 = D.U₀)
    (hU : Evolution.IsStrongSolution MirrorBGG.complexQ.wave (Icc 0 T) 0 U) {ε : ℝ} (hε : 0 < ε) :
    (∀ t ∈ Icc 0 T, U t ∈ totalSub MirrorBGG.tsdQ) ∧
    ∀ᶠ N in atTop,
      ∃ sh : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T (mirrorSource hT hB N 0),
        (sh.σ 0, sh.u 0, sh.M 0, sh.ρ 0) =
          (Feec.BGG.ellipticProjection (mirrorWave hT hB N) (mirrorWave_dt0_injective hT hB N)
            (Feec.BGG.exists_sub_eq_of_surjective (mirrorWave_S0_surjective hT hB N))
            (Feec.BGG.ellipticRhs ((mirrorFEM hT hB N).ellipticDataH ((D.exactWave T).σ 0)
              ((D.exactWave T).φ 0) ((D.exactWave T).u 0) ((D.exactWave T).M 0)
              ((D.exactWave T).ρ 0) ((D.exactWave T).ℓ 0)) 0)).1.1 ∧
        ∀ t ∈ Icc 0 T, ‖(sh.σ t : TU0)‖ ≤ ε ∧
          ‖rowsW1L (stEL (U t)) - bIncl1 (sh.u t : BU1)‖ ≤ ε ∧ ‖(sh.M t : W2)‖ ≤ ε ∧
          ‖rowsW2L (stBL (U t)) - (sh.ρ t : Wv W2)‖ ≤ ε ∧
          ‖matB (sh.ρ t : Wv W2) - transposeQ (matB (sh.ρ t : Wv W2))‖ ≤ 2 * ε := by
  have hEq := D.eqOn_of_isStrongSolution hU0 hU
  refine ⟨fun t ht => hEq ht ▸ D.U_tsd t, ?_⟩
  have hmult : ∀ t ∈ Icc 0 T, ∀ μ : TU1, |(D.exactWave T).ℓ t μ| ≤ 0 * ‖μ‖ ∧
      |(D.exactWave T).ℓ' t μ| ≤ 0 * ‖μ‖ := fun t _ μ =>
    ⟨by simp [TSDDatum.exactWave], by simp [TSDDatum.exactWave]⟩
  have hf : ContinuousOn (0 : ℝ → Wv W1) (Icc 0 T) := continuousOn_const
  refine (mirrorWave_converges hT hB hT0 hf (D.exactWave T) le_rfl hmult hε).mono
    fun N hN => ⟨hN.choose, hN.choose_spec.1, fun t ht => ?_⟩
  exact tsd_bounds (sqrt_four_congr (hN.choose_spec.2 t ht) (norm_zero_sub' _)
    (D.norm_exactWave_u_sub hEq ht _) (norm_zero_sub' _) (D.norm_exactWave_ρ_sub hEq ht _))
    (MirrorBGG.tsd_of_mem_tsdQ (hEq ht ▸ D.U_tsd t)).2.2.2.1

end Main

/-! ### Non-vacuity: a non-stationary TSD datum in `D(L²)` -/

section NonVacuity

/-- Finitely supported coefficient sequences lie in the domains of the torus BGG complex. -/
theorem torusBGG_mem_domain_of_finite {i j : Fin 3} {x : Models.Torus.BGG.Space i}
    (S : Finset (Fin 3 → ℤ)) (hx : ∀ n ∉ S, (x : (Fin 3 → ℤ) → _) n = 0) :
    x ∈ (Models.Torus.BGG.complex.d i j).domain :=
  Feec.Models.Cube.MirrorExt.mem_mulDomain_of_finite _ S hx

theorem torusBGG_mem_adjoint_domain_of_finite {i j : Fin 3} {x : Models.Torus.BGG.Space j}
    (S : Finset (Fin 3 → ℤ)) (hx : ∀ n ∉ S, (x : (Fin 3 → ℤ) → _) n = 0) :
    x ∈ ((Models.Torus.BGG.complex.d i j)†).domain := by
  rw [show (Models.Torus.BGG.complex.d i j)† = Operator.mulOp Measure.count fun n =>
      ContinuousLinearMap.adjoint (Fourier.BGG.bggFamily.m i j (Fourier.Torus.freq n)) from
    (Fourier.Torus.symbolComplex Fourier.BGG.bggFamily).adjoint_d i j]
  exact Feec.Models.Cube.MirrorExt.mem_mulDomain_of_finite _ S hx

theorem torusBGG_d_eq_zero {i j : Fin 3} (x : (Models.Torus.BGG.complex.d i j).domain)
    (S : Finset (Fin 3 → ℤ))
    (hx : ∀ n ∉ S, ((x : Models.Torus.BGG.Space i) : (Fin 3 → ℤ) → _) n = 0)
    (n : Fin 3 → ℤ) (hn : n ∉ S) :
    ((Models.Torus.BGG.complex.d i j x : Models.Torus.BGG.Space j) : (Fin 3 → ℤ) → _) n = 0 := by
  exact (Operator.coeFn_mulOp_count (𝕜 := ℂ)
    (fun n => Fourier.BGG.bggFamily.m i j (Fourier.Torus.freq n)) x n).trans
      (by rw [hx n hn, map_zero])

theorem torusBGG_adjoint_eq_zero {i j : Fin 3}
    (y : ((Models.Torus.BGG.complex.d i j)†).domain)
    (S : Finset (Fin 3 → ℤ))
    (hy : ∀ n ∉ S, ((y : Models.Torus.BGG.Space j) : (Fin 3 → ℤ) → _) n = 0)
    (n : Fin 3 → ℤ) (hn : n ∉ S) :
    (((Models.Torus.BGG.complex.d i j)† y : Models.Torus.BGG.Space i) : (Fin 3 → ℤ) → _) n = 0 := by
  have e : (Models.Torus.BGG.complex.d i j)† = Operator.mulOp Measure.count fun n =>
      ContinuousLinearMap.adjoint (Fourier.BGG.bggFamily.m i j (Fourier.Torus.freq n)) :=
    (Fourier.Torus.symbolComplex Fourier.BGG.bggFamily).adjoint_d i j
  have hy' : (y : Models.Torus.BGG.Space j) ∈ (Operator.mulOp Measure.count fun n =>
      ContinuousLinearMap.adjoint (Fourier.BGG.bggFamily.m i j (Fourier.Torus.freq n))).domain :=
    e ▸ y.2
  rw [LinearPMap.apply_eq_of_eq e y ⟨_, hy'⟩ rfl]
  exact (Operator.coeFn_mulOp_count (𝕜 := ℂ) _ ⟨_, hy'⟩ n).trans (by rw [hy n hn, map_zero])

theorem coeFn_neg_count {E : Type*} [NormedAddCommGroup E]
    (f : Lp E 2 (Measure.count : Measure (Fin 3 → ℤ)))
    (n : Fin 3 → ℤ) : ((-f : Lp E 2 _) : (Fin 3 → ℤ) → E) n = -(f : (Fin 3 → ℤ) → E) n :=
  Measure.ae_count_iff.1 (Lp.coeFn_neg f) n

theorem coeFn_sub_count {E : Type*} [NormedAddCommGroup E]
    (f g : Lp E 2 (Measure.count : Measure (Fin 3 → ℤ))) (n : Fin 3 → ℤ) :
    ((f - g : Lp E 2 _) : (Fin 3 → ℤ) → E) n = (f : (Fin 3 → ℤ) → E) n - (g : (Fin 3 → ℤ) → E) n :=
  Measure.ae_count_iff.1 (Lp.coeFn_sub f g) n

/-- **On the torus, `L` preserves finitely supported states.** -/
theorem torusBGG_wave_finite (x : Models.Torus.BGG.complex.wave.domain)
    (S : Finset (Fin 3 → ℤ))
    (hx : ∀ i, ∀ n ∉ S, (((x : PiLp 2 Models.Torus.BGG.Space) i : Models.Torus.BGG.Space i) :
      (Fin 3 → ℤ) → _) n = 0) :
    ∀ i, ∀ n ∉ S, (((Models.Torus.BGG.complex.wave x) i : Models.Torus.BGG.Space i) :
      (Fin 3 → ℤ) → _) n = 0 := by
  intro i n hn
  fin_cases i
  · have e0 := HilbertComplex.wave_apply_fin3_zero Models.Torus.BGG.complex x
    change (((Models.Torus.BGG.complex.wave x) 0 : Models.Torus.BGG.Space 0) :
      (Fin 3 → ℤ) → _) n = 0
    rw [e0]
    exact (coeFn_neg_count _ n).trans (neg_eq_zero.2 (torusBGG_adjoint_eq_zero _ S (hx 1) n hn))
  · have e1 := HilbertComplex.wave_apply_fin3_one Models.Torus.BGG.complex x
    change (((Models.Torus.BGG.complex.wave x) 1 : Models.Torus.BGG.Space 1) :
      (Fin 3 → ℤ) → _) n = 0
    rw [e1]
    exact (coeFn_sub_count _ _ n).trans (by
      rw [torusBGG_d_eq_zero _ S (hx 0) n hn, torusBGG_adjoint_eq_zero _ S (hx 2) n hn, sub_zero])
  · have e2 := HilbertComplex.wave_apply_fin3_two Models.Torus.BGG.complex x
    change (((Models.Torus.BGG.complex.wave x) 2 : Models.Torus.BGG.Space 2) :
      (Fin 3 → ℤ) → _) n = 0
    rw [e2]
    exact torusBGG_d_eq_zero _ S (hx 1) n hn

theorem torusBGG_wave_mem_of_finite (x : Models.Torus.BGG.complex.wave.domain)
    (S : Finset (Fin 3 → ℤ))
    (hx : ∀ i, ∀ n ∉ S, (((x : PiLp 2 Models.Torus.BGG.Space) i : Models.Torus.BGG.Space i) :
      (Fin 3 → ℤ) → _) n = 0) :
    Models.Torus.BGG.complex.wave x ∈ Models.Torus.BGG.complex.wave.domain := by
  have h := torusBGG_wave_finite x S hx
  exact HilbertComplex.mem_wave_domain_fin3 _ (torusBGG_mem_domain_of_finite S (h 0))
    (torusBGG_mem_domain_of_finite S (h 1)) (torusBGG_mem_adjoint_domain_of_finite S (h 1))
    (torusBGG_mem_adjoint_domain_of_finite S (h 2))

theorem cosState_finite (i : Fin 3) :
    ∀ n ∉ ({k0, -k0} : Finset (Fin 3 → ℤ)), ((MirrorBGG.cosState i : Models.Torus.BGG.Space i) :
      (Fin 3 → ℤ) → _) n = 0 := by
  intro n hn
  fin_cases i
  · change ((MirrorBGG.cosState 0 : Models.Torus.BGG.Space 0) : (Fin 3 → ℤ) → _) n = 0
    rw [MirrorBGG.cosState_zero]
    exact Measure.ae_count_iff.1 (Lp.coeFn_zero _ 2 Measure.count) n
  · change ((MirrorBGG.cosState 1 : Models.Torus.BGG.Space 1) : (Fin 3 → ℤ) → _) n = 0
    rw [MirrorBGG.cosState_one]
    exact (coe_cosE n).trans (cosCoeff_eq_zero hn)
  · change ((MirrorBGG.cosState 2 : Models.Torus.BGG.Space 2) : (Fin 3 → ℤ) → _) n = 0
    rw [MirrorBGG.cosState_two]
    exact Measure.ae_count_iff.1 (Lp.coeFn_zero _ 2 Measure.count) n

/-- `L cosState ∈ D(L)` on the torus. -/
theorem cosState_wave_mem : Models.Torus.BGG.complex.wave ⟨_, MirrorBGG.cosState_mem_domain⟩ ∈
    Models.Torus.BGG.complex.wave.domain :=
  torusBGG_wave_mem_of_finite _ _ cosState_finite

theorem cosStateQ_mem : MirrorBGG.cosStateQ ∈ MirrorBGG.complexQ.wave.domain :=
  (HilbertComplex.mem_wave_domain_compress_iff Mirror.eight_pos MirrorBGG.inner_J
    MirrorBGG.reducingSubcomplex_range).2
      (MirrorBGG.totalJ_cosStateQ ▸ MirrorBGG.cosState_mem_domain)

theorem cosStateQ_wave_mem :
    MirrorBGG.complexQ.wave ⟨_, cosStateQ_mem⟩ ∈ MirrorBGG.complexQ.wave.domain := by
  refine (HilbertComplex.mem_wave_domain_compress_iff Mirror.eight_pos MirrorBGG.inner_J
    MirrorBGG.reducingSubcomplex_range).2 ?_
  have h := (HilbertComplex.wave_compress Mirror.eight_pos MirrorBGG.inner_J
    MirrorBGG.reducingSubcomplex_range).comm ⟨_, cosStateQ_mem⟩
  rw [← h, LinearPMap.apply_congr' _ _ MirrorBGG.cosState_mem_domain MirrorBGG.totalJ_cosStateQ]
  exact cosState_wave_mem

theorem cosStateQ_mem_tsd : MirrorBGG.cosStateQ ∈ totalSub MirrorBGG.tsdQ := fun i => by
  change MirrorBGG.J i (MirrorBGG.cosStateQ i) ∈ Models.Torus.BGG.constraint i
  rw [← HilbertComplex.totalJ_apply, MirrorBGG.totalJ_cosStateQ]
  exact MirrorBGG.cosState_mem_constraint i

/-- **The datum `(0, E₀, (0, 0))`, `E₀ = 2 cos(2π x₃) diag(1, -1, 0)`**, a TSD datum in `D(L²)`. -/
def cosDatum : TSDDatum where
  U₀ := MirrorBGG.cosStateQ
  mem := cosStateQ_mem
  mem₂ := cosStateQ_wave_mem
  tsd := cosStateQ_mem_tsd

theorem cosDatum_not_stationary : cosDatum.U₀ ∉ MirrorBGG.complexQ.waveGroup.stationary := by
  have hd : HilbertComplex.totalJ MirrorBGG.J MirrorBGG.cosStateQ ∈
      Models.Torus.BGG.complex.wave.domain :=
    MirrorBGG.totalJ_cosStateQ ▸ MirrorBGG.cosState_mem_domain
  exact (HilbertComplex.not_mem_stationary_compress Mirror.eight_pos MirrorBGG.inner_J
    MirrorBGG.reducingSubcomplex_range hd fun h0 => MirrorBGG.wave_cosState_ne
      ((LinearPMap.apply_congr' _ _ _ MirrorBGG.totalJ_cosStateQ.symm).trans h0)).2

end NonVacuity

end Feec.Models.Cube.MirrorWeakSymmetry
