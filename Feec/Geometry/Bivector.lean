module

public import Feec.Algebra.LeviCivita
public import Feec.Algebra.Metric
public import Feec.Geometry.AlgebraicCurvature
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Data.Matrix.Block

/-!
# Double 2-forms in four dimensions and their bivector blocks

Double 2-forms in a Minkowski orthonormal frame, parametrised by their bivector blocks
`[[E, B], [H, D]]` ([QuennevilleBelair2015], §3.3), and the conditions of
[QuennevilleBelair2015], Prop 3.3 in terms of the blocks.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public section

open Matrix Equiv Feec.CurvatureTensor

noncomputable section

namespace Feec.DoubleForm

/-- A `(0,4)`-tensor on four-dimensional space-time, in components. -/
abbrev Tensor4 := Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ

/-! ### Bivector basis and the block parametrisation -/

/-- index set of the bivector basis `(t∧x, t∧y, t∧z | y∧z, z∧x, x∧y)`. -/
abbrev Ix := Fin 3 ⊕ Fin 3

/-- first leg of the basis bivector `I`. -/
def p : Ix → Fin 4
  | .inl _ => 0
  | .inr i => ![2, 3, 1] i

/-- second leg of the basis bivector `I`. -/
def q : Ix → Fin 4
  | .inl i => ![1, 2, 3] i
  | .inr i => ![3, 1, 2] i

/-- components of the basis bivector `I`: `β I a b = δ_{a p}δ_{b q} - δ_{a q}δ_{b p}`. -/
def β (I : Ix) (a b : Fin 4) : ℝ :=
  (if a = p I ∧ b = q I then 1 else 0) - (if a = q I ∧ b = p I then 1 else 0)

/-- the double 2-form with bivector matrix `M`: `C_{abcd} = ∑_{I,J} M_{IJ} β^I_{ab} β^J_{cd}`. -/
def ofMat (M : Matrix Ix Ix ℝ) : Tensor4 :=
  fun a b c d => ∑ I, ∑ J, β I a b * β J c d * M I J

/-- the double 2-form whose bivector matrix is `[[E, B], [H, D]]`. -/
def ofBlocks (E B H D : Matrix (Fin 3) (Fin 3) ℝ) : Tensor4 := ofMat (fromBlocks E B H D)

/-- the bivector matrix `M_{IJ} = C(e_I, e_J) = C_{p_I q_I p_J q_J}` of a (0,4)-tensor. -/
def toMat (C : Tensor4) : Matrix Ix Ix ℝ := Matrix.of fun I J => C (p I) (q I) (p J) (q J)

/-- sign of the pair `(a, b)` relative to the basis bivector `pidx a b` (zero on the diagonal). -/
def sgn : Fin 4 → Fin 4 → ℝ :=
  ![![0, 1, 1, 1], ![-1, 0, 1, -1], ![-1, -1, 0, 1], ![-1, 1, -1, 0]]

/-- the basis bivector carrying the pair `(a, b)`. -/
def pidx : Fin 4 → Fin 4 → Ix :=
  ![![.inl 0, .inl 0, .inl 1, .inl 2], ![.inl 0, .inl 0, .inr 2, .inr 1],
    ![.inl 1, .inr 2, .inl 0, .inr 0], ![.inl 2, .inr 1, .inr 0, .inl 0]]

theorem β_eq (I : Ix) (a b : Fin 4) : β I a b = if I = pidx a b then sgn a b else 0 := by
  rcases I with i | i <;> fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [β, p, q, pidx, sgn]

theorem ofMat_apply (M : Matrix Ix Ix ℝ) (a b c d : Fin 4) :
    ofMat M a b c d = sgn a b * sgn c d * M (pidx a b) (pidx c d) := by
  simp only [ofMat, β_eq, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem sgn_swap (a b : Fin 4) : sgn b a = -sgn a b := by
  fin_cases a <;> fin_cases b <;> simp [sgn]

theorem pidx_swap (a b : Fin 4) : pidx b a = pidx a b := by
  fin_cases a <;> fin_cases b <;> rfl

theorem sgn_pq (I : Ix) : sgn (p I) (q I) = 1 ∧ pidx (p I) (q I) = I := by
  rcases I with i | i <;> fin_cases i <;> simp [sgn, pidx, p, q]

theorem skew2_expand (w : Fin 4 → Fin 4 → ℝ) (hw : ∀ a b, w a b = -w b a) (a b : Fin 4) :
    w a b = sgn a b * w (p (pidx a b)) (q (pidx a b)) := by
  have h00 := hw 0 0; have h11 := hw 1 1; have h22 := hw 2 2; have h33 := hw 3 3
  fin_cases a <;> fin_cases b <;> simp [sgn, pidx, p, q] <;>
    linarith [hw 0 1, hw 0 2, hw 0 3, hw 1 2, hw 1 3, hw 2 3]

theorem toMat_ofMat (M : Matrix Ix Ix ℝ) : toMat (ofMat M) = M := by
  ext I J; simp [toMat, ofMat_apply, (sgn_pq I).1, (sgn_pq I).2, (sgn_pq J).1, (sgn_pq J).2]

theorem ofMat_injective : Function.Injective ofMat := fun M N h => by
  rw [← toMat_ofMat M, ← toMat_ofMat N, h]

theorem pairSkew_ofMat (M : Matrix Ix Ix ℝ) : PairSkew (ofMat M) := by
  intro a b c d
  rw [ofMat_apply, ofMat_apply, ofMat_apply, sgn_swap a b, sgn_swap c d, pidx_swap a b,
    pidx_swap c d]
  constructor <;> ring

theorem eq_ofMat_toMat {C : Tensor4} (hC : PairSkew C) : C = ofMat (toMat C) := by
  funext a b c d
  rw [ofMat_apply]
  simp only [toMat, Matrix.of_apply]
  rw [skew2_expand (fun a b => C a b c d) (fun a b => (hC a b c d).1) a b,
    skew2_expand (fun c d => C (p (pidx a b)) (q (pidx a b)) c d)
      (fun c d => (hC _ _ c d).2) c d]
  ring

/-- the `E`-block of the bivector matrix `[[E, B], [H, D]]`. -/
def blkE (C : Tensor4) : Matrix (Fin 3) (Fin 3) ℝ := (toMat C).toBlocks₁₁
/-- the `B`-block. -/
def blkB (C : Tensor4) : Matrix (Fin 3) (Fin 3) ℝ := (toMat C).toBlocks₁₂
/-- the `H`-block. -/
def blkH (C : Tensor4) : Matrix (Fin 3) (Fin 3) ℝ := (toMat C).toBlocks₂₁
/-- the `D`-block. -/
def blkD (C : Tensor4) : Matrix (Fin 3) (Fin 3) ℝ := (toMat C).toBlocks₂₂

theorem blkE_apply (C : Tensor4) (i j : Fin 3) : blkE C i j = C 0 i.succ 0 j.succ := by
  fin_cases i <;> fin_cases j <;> rfl

/-- a double 2-form is `ofBlocks` of its four blocks. -/
theorem eq_ofBlocks_blocks {C : Tensor4} (hC : PairSkew C) :
    C = ofBlocks (blkE C) (blkB C) (blkH C) (blkD C) := by
  rw [ofBlocks, blkE, blkB, blkH, blkD, fromBlocks_toBlocks]; exact eq_ofMat_toMat hC

@[simp] theorem blkE_ofBlocks (E B H D : Matrix (Fin 3) (Fin 3) ℝ) : blkE (ofBlocks E B H D) = E := by
  simp [blkE, ofBlocks, toMat_ofMat]
@[simp] theorem blkB_ofBlocks (E B H D : Matrix (Fin 3) (Fin 3) ℝ) : blkB (ofBlocks E B H D) = B := by
  simp [blkB, ofBlocks, toMat_ofMat]
@[simp] theorem blkH_ofBlocks (E B H D : Matrix (Fin 3) (Fin 3) ℝ) : blkH (ofBlocks E B H D) = H := by
  simp [blkH, ofBlocks, toMat_ofMat]
@[simp] theorem blkD_ofBlocks (E B H D : Matrix (Fin 3) (Fin 3) ℝ) : blkD (ofBlocks E B H D) = D := by
  simp [blkD, ofBlocks, toMat_ofMat]

theorem ofBlocks_neg (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    ofBlocks (-E) (-B) (-H) (-D) = -ofBlocks E B H D := by
  funext a b c d; simp [ofBlocks, ofMat_apply, ← fromBlocks_neg]

/-- the pair interchange `C_{abcd} ↦ C_{cdab}`. -/
def swapPairs (C : Tensor4) : Tensor4 := fun a b c d => C c d a b

theorem swapPairs_ofMat (M : Matrix Ix Ix ℝ) : swapPairs (ofMat M) = ofMat Mᵀ := by
  funext a b c d; simp only [swapPairs, ofMat_apply, transpose_apply]; ring

/-! ### Prop 3.3: interchange, total antisymmetry, trace -/

theorem interchange_iff_swapPairs (C : Tensor4) : Interchange C ↔ swapPairs C = C := by
  constructor
  · intro h; funext a b c d; exact (h a b c d).symm
  · intro h a b c d; exact (congrFun (congrFun (congrFun (congrFun h a) b) c) d).symm

theorem interchange_ofMat_iff (M : Matrix Ix Ix ℝ) : Interchange (ofMat M) ↔ Mᵀ = M := by
  rw [interchange_iff_swapPairs, swapPairs_ofMat, ofMat_injective.eq_iff]

/-- The interchange symmetry `C_{abcd} = C_{cdab}` holds iff `E`, `D` are symmetric and `H = Bᵀ`.
[QuennevilleBelair2015], Prop 3.3(i) -/
theorem interchange_iff (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    Interchange (ofBlocks E B H D) ↔ Eᵀ = E ∧ Dᵀ = D ∧ H = Bᵀ := by
  rw [ofBlocks, interchange_ofMat_iff, fromBlocks_transpose, fromBlocks_inj]
  constructor
  · rintro ⟨h1, -, h3, h4⟩; exact ⟨h1, h4, h3.symm⟩
  · rintro ⟨h1, h4, h3⟩; exact ⟨h1, by rw [h3, transpose_transpose], h3.symm, h4⟩

/-- total antisymmetrisation `C_{[abcd]} = (1/4!) ∑_σ sgn σ C_{σ(abcd)}`. -/
def altPart (C : Tensor4) : Tensor4 := fun a b c d =>
  (1 / 24) * ∑ σ : Perm (Fin 4), (Perm.sign σ : ℝ) *
    C (![a, b, c, d] (σ 0)) (![a, b, c, d] (σ 1)) (![a, b, c, d] (σ 2)) (![a, b, c, d] (σ 3))

private theorem sum_perm_succ {n : ℕ} (f : Perm (Fin (n + 1)) → ℝ) :
    ∑ σ, f σ = ∑ p, ∑ e : Perm (Fin n), f (Perm.decomposeFin.symm (p, e)) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv Perm.decomposeFin _ _ (fun σ => by simp)).trans rfl

theorem altPart_expand (C : Tensor4) (a b c d : Fin 4) : altPart C a b c d = (1 / 24) *
    (C a b c d - C a b d c - C a c b d + C a c d b - C a d c b + C a d b c
     - C b a c d + C b a d c + C b c a d - C b c d a + C b d c a - C b d a c
     - C c b a d + C c b d a + C c a b d - C c a d b + C c d a b - C c d b a
     - C d b c a + C d b a c + C d c b a - C d c a b + C d a c b - C d a b c) := by
  simp only [altPart, sum_perm_succ, Fin.sum_univ_succ, Perm.decomposeFin.symm_sign,
    Fintype.sum_unique]
  simp only [show (2 : Fin 4) = Fin.succ 1 from rfl, show (3 : Fin 4) = Fin.succ 2 from rfl,
    show (1 : Fin 4) = Fin.succ 0 from rfl, show (2 : Fin 3) = Fin.succ 1 from rfl,
    show (1 : Fin 3) = Fin.succ 0 from rfl, show (1 : Fin 2) = Fin.succ 0 from rfl,
    Perm.decomposeFin_symm_apply_succ, Perm.decomposeFin_symm_apply_zero]
  simp [Equiv.swap_apply_def]
  ring

private theorem altPart_comp (C : Tensor4) (v : Fin 4 → Fin 4) (τ : Perm (Fin 4)) :
    altPart C (v (τ 0)) (v (τ 1)) (v (τ 2)) (v (τ 3)) =
      (Perm.sign τ : ℝ) * altPart C (v 0) (v 1) (v 2) (v 3) := by
  have hv : ∀ w : Fin 4 → Fin 4, ![w 0, w 1, w 2, w 3] = w := fun w => by
    ext i; fin_cases i <;> rfl
  simp only [altPart]
  have e1 : ![v (τ 0), v (τ 1), v (τ 2), v (τ 3)] = fun k => v (τ k) := hv (fun k => v (τ k))
  rw [e1, hv v, ← Equiv.sum_comp (Equiv.mulLeft τ⁻¹)]
  have hτ : ∀ x, τ (τ⁻¹ x) = x := fun x => by simp
  simp only [Equiv.coe_mulLeft, Perm.mul_apply, hτ, Perm.sign_mul, Perm.sign_inv,
    Units.val_mul, Int.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

theorem altPart_eq_eps (C : Tensor4) (a b c d : Fin 4) :
    altPart C a b c d = leviCivita4 ℝ a b c d * altPart C 0 1 2 3 := by
  set v : Fin 4 → Fin 4 := ![a, b, c, d]
  by_cases hinj : Function.Injective v
  · set σ : Perm (Fin 4) := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj)
    have h := altPart_comp C id σ
    simp only [id] at h
    have he : leviCivita4 ℝ a b c d = (Perm.sign σ : ℝ) := by
      rw [leviCivita4_eq_int]
      have := leviCivita4Int_perm σ
      simp only [σ, Equiv.ofBijective_apply, v] at this
      exact_mod_cast this.symm
    rw [he]; simpa [σ, v] using h
  · obtain ⟨i, j, hij, hne⟩ : ∃ i j, v i = v j ∧ i ≠ j := by
      by_contra h; push Not at h
      exact hinj fun i j hij => by_contra fun hne => hne (h i j hij)
    have h := altPart_comp C v (Equiv.swap i j)
    have hvs : ∀ k, v (Equiv.swap i j k) = v k := fun k => by
      rcases eq_or_ne k i with rfl | hki
      · simp [hij]
      rcases eq_or_ne k j with rfl | hkj
      · simp [hij]
      rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
    rw [hvs, hvs, hvs, hvs, Perm.sign_swap hne] at h
    have h0 : altPart C (v 0) (v 1) (v 2) (v 3) = 0 := by push_cast at h; linarith
    have h0' : altPart C a b c d = 0 := h0
    rw [h0', leviCivita4_eq_int, leviCivita4Int_not_inj _ _ _ _ hinj]; simp

theorem altPart_0123 {C : Tensor4} (hC : PairSkew C) : altPart C 0 1 2 3 =
    (1 / 6) * (C 0 1 2 3 + C 0 2 3 1 + C 0 3 1 2 + C 2 3 0 1 + C 3 1 0 2 + C 1 2 0 3) := by
  rw [altPart_expand]
  have s1 := fun a b c d => (hC a b c d).1
  have s2 := fun a b c d => (hC a b c d).2
  linarith [s2 0 1 2 3, s1 1 0 2 3, s1 1 0 3 2, s2 0 2 1 3, s1 2 0 1 3, s1 2 0 3 1,
    s2 0 2 3 1, s2 0 3 2 1, s1 3 0 2 1, s1 3 0 1 2, s2 0 3 1 2, s2 1 2 0 3, s1 2 1 0 3,
    s1 2 1 3 0, s2 1 2 3 0, s2 1 3 2 0, s1 3 1 2 0, s1 3 1 0 2, s2 1 3 0 2, s1 1 3 0 2,
    s2 2 3 0 1, s1 3 2 0 1, s1 3 2 1 0, s2 2 3 1 0, s2 0 1 3 2, s1 0 2 1 3, s1 0 3 2 1,
    s1 1 2 3 0, s1 0 2 3 1]

/-- `C_{[abcd]} = 0` holds iff `tr B + tr H = 0`. [QuennevilleBelair2015], Prop 3.3(ii) -/
theorem altPart_ofBlocks_iff (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    (∀ a b c d, altPart (ofBlocks E B H D) a b c d = 0) ↔ trace B + trace H = 0 := by
  have h6 : altPart (ofBlocks E B H D) 0 1 2 3 = (1 / 6) * (trace B + trace H) := by
    rw [ofBlocks, altPart_0123 (pairSkew_ofMat _)]
    simp [ofMat_apply, sgn, pidx, trace, Fin.sum_univ_three]; ring
  constructor
  · intro h; have := h 0 1 2 3; rw [h6] at this; linarith
  · intro h a b c d; rw [altPart_eq_eps, h6, h]; ring


theorem altPart_eq_alt4 (C : Tensor4) (a b c d : Fin 4) :
    altPart C a b c d = (1 / 24) * CurvatureTensor.alt4 C a b c d := by
  rw [altPart_expand]; unfold CurvatureTensor.alt4; ring

theorem bianchi_iff_altPart {C : Tensor4} (hC : PairSkew C) :
    Bianchi1 C ↔ Interchange C ∧ ∀ a b c d, altPart C a b c d = 0 := by
  rw [CurvatureTensor.bianchi_iff hC]
  simp only [altPart_eq_alt4, mul_eq_zero, one_div, inv_eq_zero, OfNat.ofNat_ne_zero,
    false_or]

/-- For `C = [[E,B],[H,D]]`, the first Bianchi identity holds iff `E`, `D` are symmetric,
`H = Bᵀ` and `tr B + tr H = 0`. [QuennevilleBelair2015], Prop 3.3 -/
theorem bianchi_ofBlocks_iff (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    Bianchi1 (ofBlocks E B H D) ↔ (Eᵀ = E ∧ Dᵀ = D ∧ H = Bᵀ) ∧ trace B + trace H = 0 := by
  rw [bianchi_iff_altPart (C := ofBlocks E B H D) (pairSkew_ofMat _), interchange_iff,
    altPart_ofBlocks_iff]

/-- the Minkowski trace `C^a{}_{bac} = ∑_a η^{aa} C_{abac}`. -/
def mtr (C : Tensor4) (b c : Fin 4) : ℝ := ∑ a, Metric.minkowski4 ℝ a * C a b a c

theorem mtr_ofBlocks (E B H D : Matrix (Fin 3) (Fin 3) ℝ) (b c : Fin 4) : mtr (ofBlocks E B H D) b c = ![
    ![trace E, B 1 2 - B 2 1, B 2 0 - B 0 2, B 0 1 - B 1 0],
    ![H 2 1 - H 1 2, -E 0 0 - D 0 0 + trace D, -E 0 1 - D 1 0, -E 0 2 - D 2 0],
    ![H 0 2 - H 2 0, -E 1 0 - D 0 1, -E 1 1 - D 1 1 + trace D, -E 1 2 - D 2 1],
    ![H 1 0 - H 0 1, -E 2 0 - D 0 2, -E 2 1 - D 1 2, -E 2 2 - D 2 2 + trace D]] b c := by
  fin_cases b <;> fin_cases c <;>
    simp [mtr, ofBlocks, ofMat_apply, sgn, pidx, Metric.minkowski4, Fin.sum_univ_four, trace, Fin.sum_univ_three] <;> ring

/-- Trace-freeness `C^a{}_{bac} = 0` holds iff `tr E = 0`, `B`, `H` are symmetric and
`D = -Eᵀ`. [QuennevilleBelair2015], Prop 3.3(iii) -/
theorem tracefree_iff (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    (∀ b c, mtr (ofBlocks E B H D) b c = 0) ↔ trace E = 0 ∧ Bᵀ = B ∧ Hᵀ = H ∧ D = -Eᵀ := by
  simp only [mtr_ofBlocks]
  constructor
  · intro h
    have e : ∀ b c : Fin 4, _ := h
    simp only [Fin.forall_fin_succ] at e
    simp only [trace, Fin.sum_univ_three, diag] at e ⊢
    simp at e
    obtain ⟨⟨e00, e01, e02, e03⟩, ⟨e10, e11, e12, e13⟩, ⟨e20, e21, e22, e23⟩,
      ⟨e30, e31, e32, e33⟩⟩ := e
    have htrD : D 0 0 + D 1 1 + D 2 2 = 0 := by linarith
    refine ⟨e00, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp <;> linarith
  · rintro ⟨h1, h2, h3, rfl⟩ b c
    have hB := fun i j => congrFun (congrFun h2 i) j
    have hH := fun i j => congrFun (congrFun h3 i) j
    simp only [transpose_apply] at hB hH
    simp only [trace, Fin.sum_univ_three, diag, Matrix.neg_apply] at h1 ⊢
    fin_cases b <;> fin_cases c <;> simp <;>
      linarith [hB 0 1, hB 0 2, hB 1 2, hH 0 1, hH 0 2, hH 1 2]

end Feec.DoubleForm

end
