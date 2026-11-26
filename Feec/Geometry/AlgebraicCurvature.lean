module

public import Feec.Algebra.Metric
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.CharP.Invertible

/-!
# Algebraic curvature tensors

The symmetries of `(0,4)`-tensors over any commutative ring, the geodesic deviation, the Ricci and
Einstein tensors (`einstein_eq_zero_iff`), and the space of algebraic curvature tensors in four
dimensions (`finrank_algCurv_four`) ([QuennevilleBelair2015], §2.3–§2.4).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset Matrix

@[expose] public noncomputable section

namespace Feec.CurvatureTensor

variable {ι : Type*} {R : Type*} [CommRing R]

/-! ### Symmetries -/

/-- Skew-symmetry in each of the two index pairs. [QuennevilleBelair2015], Prop 2.1 -/
def PairSkew (C : ι → ι → ι → ι → R) : Prop :=
  ∀ a b c d, C a b c d = -C b a c d ∧ C a b c d = -C a b d c

/-- The first (algebraic) Bianchi identity `C_{a[bcd]} = 0`. [QuennevilleBelair2015], Prop 2.1 -/
def Bianchi1 (C : ι → ι → ι → ι → R) : Prop := ∀ a b c d, C a b c d + C a c d b + C a d b c = 0

/-- The interchange (pair) symmetry `C_{abcd} = C_{cdab}`. [QuennevilleBelair2015], §2.3 -/
def Interchange (C : ι → ι → ι → ι → R) : Prop := ∀ a b c d, C a b c d = C c d a b

/-- Total antisymmetrisation in the four slots, unnormalised: `alt4 C a b c d = 24 C_[abcd]`. -/
def alt4 (C : ι → ι → ι → ι → R) (a b c d : ι) : R :=
  C a b c d - C a b d c - C a c b d + C a c d b + C a d b c - C a d c b
  - C b a c d + C b a d c + C b c a d - C b c d a - C b d a c + C b d c a
  + C c a b d - C c a d b - C c b a d + C c b d a + C c d a b - C c d b a
  - C d a b c + C d a c b + C d b a c - C d b c a - C d c a b + C d c b a

theorem eq_of_two_mul_eq [Invertible (2 : R)] {x y : R} (h : 2 * x = 2 * y) : x = y := by
  have := congrArg (⅟2 * ·) h
  simpa [← mul_assoc] using this

theorem interchange_of_bianchi [Invertible (2 : R)] {C : ι → ι → ι → ι → R} (hs : PairSkew C)
    (hb : Bianchi1 C) : Interchange C := by
  intro a b c d
  refine eq_of_two_mul_eq ?_
  linear_combination hb a b c d + (hs a b c d).2 - (hs a b d c).1 + (hs a c b d).1 -
    (hs a c b d).2 - (hs a d b c).1 + hb b a d c - (hs b c a d).2 + (hs b c d a).1 -
    (hs b d c a).1 - hb c a b d - (hs c d a b).1 + hb d a b c

theorem alt4_eq_zero_of_bianchi {C : ι → ι → ι → ι → R} (hs : PairSkew C) (hb : Bianchi1 C)
    (a b c d : ι) : alt4 C a b c d = 0 := by
  unfold alt4
  linear_combination (hs a b c d).1 - 2 * hb a b d c + (hs a b d c).1 + (hs a c b d).1 +
    (hs a c d b).1 + (hs a d b c).1 + (hs a d c b).1 - 2 * hb b a c d + (hs b c a d).1 +
    (hs b c d a).1 + (hs b d a c).1 + (hs b d c a).1 - 2 * hb c a d b + (hs c d a b).1 +
    (hs c d b a).1 - 2 * hb d a b c

/-- With `2` invertible, for `C` skew in each pair, the first Bianchi identity holds iff `C` has
the interchange symmetry and vanishing totally antisymmetric part. [QuennevilleBelair2015], §2.3 -/
theorem bianchi_iff [Invertible (2 : R)] {C : ι → ι → ι → ι → R} (hs : PairSkew C) :
    Bianchi1 C ↔ Interchange C ∧ ∀ a b c d, alt4 C a b c d = 0 := by
  refine ⟨fun hb => ⟨interchange_of_bianchi hs hb, alt4_eq_zero_of_bianchi hs hb⟩, ?_⟩
  rintro ⟨hi, ha⟩ a b c d
  have h := ha a b c d
  have h8 : (8 : R) * (C a b c d + C a c d b + C a d b c) = 0 := by
    unfold alt4 at h
    linear_combination 2 * (hs a b c d).1 + 4 * (hs a b c d).2 + hi a b c d -
      2 * (hs a b d c).1 - hi a b d c - (hs a c b d).1 + 5 * (hs a c b d).2 - 3 * hi a c b d +
      (hs a c d b).1 + hi a c d b + (hs a d b c).1 + 3 * (hs a d b c).2 + 3 * hi a d b c -
      (hs a d c b).1 - hi a d c b - hi b a c d + hi b a d c + 2 * (hs b c a d).2 -
      (hs b c d a).1 - 2 * (hs b d a c).2 + (hs b d c a).1 + h
  have h2 : (⅟2 : R) * 2 = 1 := invOf_mul_self 2
  linear_combination (⅟2 * ⅟2 * ⅟2) * h8 -
    (C a b c d + C a c d b + C a d b c) * (4 * ⅟2 * ⅟2 + 2 * ⅟2 + 1) * h2

/-! ### Geodesic deviation (2.3) -/

theorem eq_zero_of_symm_bd [Invertible (3 : R)] {C : ι → ι → ι → ι → R} (hs : PairSkew C)
    (hb : Bianchi1 C) (h : ∀ a b c d, C a b c d + C a d c b = 0) : C = 0 := by
  have key : ∀ a b c d, 2 * C a b c d = C a c b d := fun a b c d => by
    linear_combination (hs a b c d).2 - hb a b d c + h a b c d
  funext a b c d
  have h3 : (3 : R) * C a b c d = 0 := by
    linear_combination 2 * key a b c d + key a c b d
  have := congrArg (⅟3 * ·) h3
  simpa [← mul_assoc] using this

variable [Fintype ι]

/-- The scalar deviation form `C(Y, T, X, T) = C_abcd Y^a T^b X^c T^d` of (2.3). -/
def deviationForm (C : ι → ι → ι → ι → R) (Y T X : ι → R) : R :=
  ∑ a, ∑ b, ∑ c, ∑ d, C a b c d * Y a * T b * X c * T d

theorem eq_zero_of_deviationForm [DecidableEq ι] [Invertible (3 : R)]
    {C : ι → ι → ι → ι → R} (hs : PairSkew C) (hb : Bianchi1 C)
    (h : ∀ Y T X : ι → R, deviationForm C Y T X = 0) : C = 0 := by
  apply eq_zero_of_symm_bd hs hb
  intro a b c d
  have hQ : ∀ T : ι → R, ∑ b, ∑ d, C a b c d * T b * T d = 0 := by
    intro T
    have := h (Pi.single a 1) T (Pi.single c 1)
    simpa [deviationForm, Pi.single_apply, mul_ite, ite_mul, Finset.sum_ite_eq'] using this
  have hB : ∀ u v : ι → R, ∑ b, ∑ d, C a b c d * (u + v) b * (u + v) d =
      ∑ b, ∑ d, C a b c d * u b * u d + ∑ b, ∑ d, C a b c d * u b * v d
      + ∑ b, ∑ d, C a b c d * v b * u d + ∑ b, ∑ d, C a b c d * v b * v d := by
    intro u v
    simp only [← Finset.sum_add_distrib, Pi.add_apply]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  have hE : ∀ i j, ∑ b, ∑ d, C a b c d * (Pi.single i 1 : ι → R) b * (Pi.single j 1 : ι → R) d
      = C a i c j := by
    intro i j
    simp [Pi.single_apply]
  have := hB (Pi.single b 1 : ι → R) (Pi.single d 1)
  simp only [hQ, hE] at this
  linear_combination -this

/-- The geodesic deviation `a^a = -R^a_cbd X^b T^c T^d` of (2.3). -/
def deviation (gi : Matrix ι ι R) (C : ι → ι → ι → ι → R) (X T : ι → R) : ι → R :=
  fun a => -∑ e, gi a e * ∑ c, ∑ b, ∑ d, C e c b d * X b * T c * T d

/-- With `3` invertible, for an algebraic curvature tensor `C` and `g * gi = 1`, all geodesic
deviations vanish iff `C = 0`. [QuennevilleBelair2015], §2.3 -/
theorem deviation_eq_zero_iff [DecidableEq ι] [Invertible (3 : R)] {C : ι → ι → ι → ι → R}
    (hs : PairSkew C) (hb : Bianchi1 C) (g gi : Matrix ι ι R) (hinv : g * gi = 1) :
    (∀ X T : ι → R, deviation gi C X T = 0) ↔ C = 0 := by
  constructor
  · intro h
    apply eq_zero_of_deviationForm hs hb
    intro Y T X
    have hv : ∀ e, ∑ c, ∑ b, ∑ d, C e c b d * X b * T c * T d = 0 := by
      have h0 : gi.mulVec (fun e => ∑ c, ∑ b, ∑ d, C e c b d * X b * T c * T d) = 0 := by
        funext a
        have := congrFun (h X T) a
        simp only [deviation, Pi.zero_apply, neg_eq_zero] at this
        simpa [Matrix.mulVec, dotProduct] using this
      intro e
      have := congrArg g.mulVec h0
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, Matrix.mulVec_zero] at this
      exact congrFun this e
    unfold deviationForm
    refine Finset.sum_eq_zero fun a _ => ?_
    have := hv a
    calc ∑ b, ∑ c, ∑ d, C a b c d * Y a * T b * X c * T d
        = Y a * ∑ b, ∑ c, ∑ d, C a b c d * X c * T b * T d := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun _ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun _ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun _ _ => ?_
          ring
      _ = 0 := by rw [this, mul_zero]
  · rintro rfl X T
    funext a
    simp [deviation]

/-! ### Ricci and Einstein tensors -/

/-- The Ricci contraction `R_ab = g^{ce} C_eacb`. [QuennevilleBelair2015], §2.3 -/
def ricci (gi : Matrix ι ι R) (C : ι → ι → ι → ι → R) : Matrix ι ι R :=
  Matrix.of fun a b => ∑ c, ∑ e, gi c e * C e a c b

theorem ricci_isSymm {gi : Matrix ι ι R} (hgi : gi.IsSymm) {C : ι → ι → ι → ι → R}
    (hi : Interchange C) : (ricci gi C).IsSymm := by
  ext a b
  simp only [transpose_apply, ricci, of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun c _ => ?_
  rw [hi e b c a, hgi.apply e c]

theorem ricci_isSymm_of_inv [DecidableEq ι] {g gi : Matrix ι ι R} (hg : g.IsSymm)
    (hinv : gi * g = 1) {C : ι → ι → ι → ι → R} (hi : Interchange C) : (ricci gi C).IsSymm :=
  ricci_isSymm (Metric.isSymm_of_mul_eq_one hg hinv) hi

/-- The Einstein tensor `G = Ric - ½ (tr_g Ric) g`, with `tr_g Ric = tr(gi Ric)`. -/
def einstein [Invertible (2 : R)] (g gi Ric : Matrix ι ι R) : Matrix ι ι R :=
  Ric - (⅟2 * (gi * Ric).trace) • g

theorem einstein_isSymm [Invertible (2 : R)] {g gi Ric : Matrix ι ι R} (hg : g.IsSymm)
    (hRic : Ric.IsSymm) : (einstein g gi Ric).IsSymm :=
  hRic.sub (hg.smul _)

section Field

variable {K : Type*} [Field K] [Invertible (2 : K)] [DecidableEq ι]

/-- Over a field, for `gi * g = 1`, `G = 0 ↔ Ric = 0` whenever `n ≠ 2` in `K`.
[QuennevilleBelair2015], §2.4 (adapted) -/
theorem einstein_eq_zero_iff (hn : (Fintype.card ι : K) ≠ 2) (g gi Ric : Matrix ι ι K)
    (hinv : gi * g = 1) : einstein g gi Ric = 0 ↔ Ric = 0 := by
  unfold einstein
  constructor
  · intro h
    have hR : (gi * Ric).trace = 0 := by
      have h1 := congrArg (fun M => (gi * M).trace) h
      simp only [Matrix.mul_sub, Matrix.mul_smul, hinv, Matrix.trace_sub, Matrix.trace_smul,
        Matrix.trace_one, Matrix.mul_zero, Matrix.trace_zero, smul_eq_mul] at h1
      have h2 : (⅟2 : K) * 2 = 1 := invOf_mul_self 2
      have : (2 - (Fintype.card ι : K)) * (gi * Ric).trace = 0 := by
        linear_combination 2 * h1 + (Fintype.card ι : K) * (gi * Ric).trace * h2
      rcases mul_eq_zero.mp this with h3 | h3
      · exact absurd (by linear_combination -h3) hn
      · exact h3
    rw [hR, mul_zero, zero_smul, sub_zero] at h
    exact h
  · rintro rfl
    simp

end Field

/-! ### The space of algebraic curvature tensors -/

variable (R ι) in
/-- The algebraic curvature tensors: pair skew and first Bianchi. -/
def algCurv : Submodule R (ι → ι → ι → ι → R) where
  carrier := {C | PairSkew C ∧ Bianchi1 C}
  zero_mem' := ⟨fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩
  add_mem' := by
    rintro C D ⟨hC, hC'⟩ ⟨hD, hD'⟩
    refine ⟨fun a b c d => ?_, fun a b c d => ?_⟩
    · simp only [Pi.add_apply]
      constructor
      · rw [(hC a b c d).1, (hD a b c d).1]; ring
      · rw [(hC a b c d).2, (hD a b c d).2]; ring
    · simp only [Pi.add_apply]
      linear_combination hC' a b c d + hD' a b c d
  smul_mem' := by
    rintro r C ⟨hC, hC'⟩
    refine ⟨fun a b c d => ?_, fun a b c d => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      constructor
      · rw [(hC a b c d).1]; ring
      · rw [(hC a b c d).2]; ring
    · simp only [Pi.smul_apply, smul_eq_mul]
      linear_combination r * hC' a b c d

/-! ### Independent components for `n = 4` (over `ℝ`) -/

section Dimension

/-- Bivector index pairs `01, 02, 03, 12, 13, 23`. -/
def bivPair : Fin 6 → Fin 4 × Fin 4 := ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- The basis bivector `e_p ∧ e_q` for `bivPair I = (p, q)`, in components. -/
def bivForm (I : Fin 6) (a b : Fin 4) : ℝ :=
  if a = (bivPair I).1 ∧ b = (bivPair I).2 then 1
  else if a = (bivPair I).2 ∧ b = (bivPair I).1 then -1 else 0

theorem bivForm_swap (I : Fin 6) (a b : Fin 4) : bivForm I b a = -bivForm I a b := by
  fin_cases I <;> fin_cases a <;> fin_cases b <;> simp [bivForm, bivPair]

theorem sum_bivForm (X : Fin 4 → Fin 4 → ℝ) (hX : ∀ a b, X a b = -X b a) (a b : Fin 4) :
    ∑ I, bivForm I a b * X (bivPair I).1 (bivPair I).2 = X a b := by
  have h0 : ∀ a, X a a = 0 := fun a => by have := hX a a; linarith
  fin_cases a <;> fin_cases b <;> simp [bivForm, bivPair, Fin.sum_univ_six, h0] <;>
    linarith [hX 1 0, hX 2 0, hX 3 0, hX 2 1, hX 3 1, hX 3 2]

theorem alt4_swap12 (C : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (a b c d : Fin 4) :
    alt4 C b a c d = -alt4 C a b c d := by
  unfold alt4; ring

theorem alt4_swap23 (C : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (a b c d : Fin 4) :
    alt4 C a c b d = -alt4 C a b c d := by
  unfold alt4; ring

theorem alt4_swap34 (C : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (a b c d : Fin 4) :
    alt4 C a b d c = -alt4 C a b c d := by
  unfold alt4; ring

theorem alt4_all_iff (C : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∀ a b c d, alt4 C a b c d = 0) ↔ alt4 C 0 1 2 3 = 0 := by
  refine ⟨fun h => h 0 1 2 3, fun h a b c d => ?_⟩
  have s1 := alt4_swap12 C; have s2 := alt4_swap23 C; have s3 := alt4_swap34 C
  by_cases hab : a = b
  · subst hab; linarith [s1 a a c d]
  by_cases hbc : b = c
  · subst hbc; linarith [s2 a b b d]
  by_cases hcd : c = d
  · subst hcd; linarith [s3 a b c c]
  by_cases hac : a = c
  · subst hac; linarith [s2 a b a d, s1 a a b d]
  by_cases hbd : b = d
  · subst hbd; linarith [s3 a b c b, s2 a b b c]
  by_cases had : a = d
  · subst had; linarith [s3 a b c a, s2 a b a c, s1 a a b c]
  unfold alt4 at h
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | (exfalso; revert hab hbc hcd hac hbd had; decide)
    | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]; unfold alt4; linarith)

theorem alt4_eq_of_interchange {C : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ} (hs : PairSkew C)
    (hi : Interchange C) : alt4 C 0 1 2 3 = 8 * (C 0 1 2 3 + C 0 2 3 1 + C 0 3 1 2) := by
  unfold alt4
  have := hs 0 1 2 3; have := hs 0 2 1 3; have := hs 0 3 1 2; have := hs 0 1 3 2
  have := hs 0 2 3 1; have := hs 0 3 2 1
  have := hi 0 1 2 3; have := hi 0 1 3 2; have := hi 0 2 1 3; have := hi 0 2 3 1
  have := hi 0 3 1 2; have := hi 0 3 2 1; have := hi 1 0 2 3; have := hi 1 0 3 2
  have := hi 1 2 0 3; have := hi 1 2 3 0; have := hi 1 3 0 2; have := hi 1 3 2 0
  have := hs 1 2 0 3; have := hs 1 3 0 2; have := hs 2 3 0 1; have := hs 2 1 0 3
  have := hs 3 1 0 2; have := hs 3 2 0 1; have := hs 1 0 3 2; have := hs 2 0 3 1
  have := hs 3 0 2 1; have := hs 1 2 3 0; have := hs 1 3 2 0
  linarith

/-- Reconstruction of a pair-skew tensor from its `6 × 6` bivector matrix. -/
def recon (M : Fin 6 → Fin 6 → ℝ) : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun a b c d => ∑ I, ∑ J, bivForm I a b * bivForm J c d * M I J

/-- Bivector matrix of a tensor, `M_IJ = C(p_I, q_I, p_J, q_J)`. -/
def bivMat (C : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) : Fin 6 → Fin 6 → ℝ :=
  fun I J => C (bivPair I).1 (bivPair I).2 (bivPair J).1 (bivPair J).2

theorem bivForm_pair (I J : Fin 6) :
    bivForm I (bivPair J).1 (bivPair J).2 = if I = J then 1 else 0 := by
  fin_cases I <;> fin_cases J <;> simp [bivForm, bivPair]

theorem recon_pair (M : Fin 6 → Fin 6 → ℝ) (I J : Fin 6) :
    recon M (bivPair I).1 (bivPair I).2 (bivPair J).1 (bivPair J).2 = M I J := by
  simp [recon, bivForm_pair]

theorem recon_pairSkew (M : Fin 6 → Fin 6 → ℝ) : PairSkew (recon M) := by
  intro a b c d
  simp only [recon]
  constructor
  · rw [← sum_neg_distrib]
    refine sum_congr rfl fun I _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun J _ => ?_
    rw [bivForm_swap I b a]; ring
  · rw [← sum_neg_distrib]
    refine sum_congr rfl fun I _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun J _ => ?_
    rw [bivForm_swap J d c]; ring

theorem recon_interchange (M : Fin 6 → Fin 6 → ℝ) (hM : ∀ I J, M I J = M J I) :
    Interchange (recon M) := by
  intro a b c d
  simp only [recon]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun I _ => sum_congr rfl fun J _ => by rw [hM]; ring

theorem eq_recon {C : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ} (hs : PairSkew C) :
    C = recon (bivMat C) := by
  funext a b c d
  simp only [recon, bivMat]
  rw [← sum_bivForm (fun x y => C x y c d) (fun x y => (hs x y c d).1) a b]
  refine sum_congr rfl fun I _ => ?_
  rw [← sum_bivForm (fun x y => C (bivPair I).1 (bivPair I).2 x y)
    (fun x y => (hs _ _ x y).2) c d, mul_sum]
  exact sum_congr rfl fun J _ => by ring

/-- The bivector matrix of 20 free parameters; the entry `(03,12)` is determined by Bianchi. -/
def parMat (p : Fin 20 → ℝ) : Fin 6 → Fin 6 → ℝ :=
  ![![p 0, p 1, p 2, p 3, p 4, p 5],
    ![p 1, p 6, p 7, p 8, p 9, p 10],
    ![p 2, p 7, p 11, p 9 - p 5, p 12, p 13],
    ![p 3, p 8, p 9 - p 5, p 14, p 15, p 16],
    ![p 4, p 9, p 12, p 15, p 17, p 18],
    ![p 5, p 10, p 13, p 16, p 18, p 19]]

/-- The bivector-matrix entries used as coordinates. -/
def parIdx : Fin 20 → Fin 6 × Fin 6 :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5),
    (2, 2), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5)]

theorem parMat_symm (p : Fin 20 → ℝ) (I J : Fin 6) : parMat p I J = parMat p J I := by
  fin_cases I <;> fin_cases J <;> rfl

theorem recon_parMat_mem (p : Fin 20 → ℝ) : recon (parMat p) ∈ algCurv (Fin 4) ℝ := by
  have hs := recon_pairSkew (parMat p)
  have hi := recon_interchange (parMat p) (parMat_symm p)
  refine ⟨hs, (bianchi_iff hs).2 ⟨hi, (alt4_all_iff _).2 ?_⟩⟩
  rw [alt4_eq_of_interchange hs hi]
  have h1 : recon (parMat p) 0 1 2 3 = p 5 := recon_pair (parMat p) 0 5
  have h2 : recon (parMat p) 0 2 1 3 = p 9 := recon_pair (parMat p) 1 4
  have h3 : recon (parMat p) 0 3 1 2 = p 9 - p 5 := recon_pair (parMat p) 2 3
  have h4 := (hs 0 2 1 3).2
  linarith

/-- The algebraic curvature tensors in four dimensions are isomorphic to `ℝ²⁰`. -/
def algCurvEquiv : algCurv (Fin 4) ℝ ≃ₗ[ℝ] (Fin 20 → ℝ) where
  toFun C := fun k => bivMat C (parIdx k).1 (parIdx k).2
  map_add' C D := rfl
  map_smul' r C := rfl
  invFun p := ⟨recon (parMat p), recon_parMat_mem p⟩
  left_inv := by
    rintro ⟨C, hs, hb⟩
    apply Subtype.ext
    have hi := interchange_of_bianchi hs hb
    show recon _ = C
    conv_rhs => rw [eq_recon hs]
    congr 1
    funext I J
    fin_cases I <;> fin_cases J <;> simp [parMat, parIdx, bivMat, bivPair] <;>
      first
      | exact hi _ _ _ _
      | linarith [hb 0 1 2 3, (hs 0 2 3 1).2, hi 0 3 1 2, hi 1 2 0 3]
  right_inv := by
    intro p
    funext k
    simp only [bivMat, recon_pair]
    fin_cases k <;> rfl

/-- In four dimensions, the algebraic curvature tensors have dimension 20.
[QuennevilleBelair2015], §2.3 -/
theorem finrank_algCurv_four : Module.finrank ℝ (algCurv (Fin 4) ℝ) = 20 := by
  rw [algCurvEquiv.finrank_eq]; simp

end Dimension

end Feec.CurvatureTensor
