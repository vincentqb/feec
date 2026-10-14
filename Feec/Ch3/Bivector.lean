import Feec.Foundation

/-!
# Ch 3 §3.1–3.3: Hodge duality, the Bel decomposition, and the Weyl block structure

Everything is pointwise linear algebra in a Minkowski orthonormal frame (`η = diag(-1,1,1,1)`,
volume form `ω = ε = eps4`, `n = ∂_t` where a frame vector is needed). A double 2-form is a
`T4 (Fin 4)` that is `PairSkew`; it is parametrised by its bivector matrix in the basis
`(t∧x, t∧y, t∧z | y∧z, z∧x, x∧y)`, written in blocks `T E B H D = [[E, B], [H, D]]`.

Coverage (thesis numbering):
* §3.1, `** = -1` on 2-forms in signature `(-+++)`: `hodge2_hodge2`.
* §3.2, duals of a double 2-form: `rdual_rdual`, `ldual_ldual`, `ldual_eq_rdual_swap`
  (`*W_{abcd} = W*_{cdab}` under interchange), and the omitted classical fact `*W = W*` for Weyl
  tensors: `ldual_eq_rdual`.
* Prop 3.2 (block action of `C*`, `*C`, `*C*`): `prop_3_2`, `rdual_T`, `ldual_T`, `ldual_rdual_T`.
* The [10]-lemma used in Prop 3.3 (first Bianchi ⇔ interchange + `C_{[abcd]} = 0`):
  `bianchi_iff`, with `alt4` the honest antisymmetrisation over `Perm (Fin 4)`.
* Prop 3.3 (i)–(iii): `interchange_iff`, `alt_iff`, `tracefree_iff` (with the full 16-entry trace
  table `mtr_T`), and the corollary `weyl_iff`: Weyl ⇔ `[[E, B], [B, -E]]`, `E, B` symmetric
  trace-free.
* Prop 3.1 (electric/magnetic parts symmetric, trace-free, orthogonal to `n`): `prop_3_1`, for
  arbitrary `n`.
* Eq. (3.2) (reconstruction of `W` from `E, B`): `weyl_reconstruct`.
* "The Weyl tensor has 10 independent components" (n = 4): `finrank_weylSpace`.

Corrections and gaps filled (see the individual docstrings):
* the factor `½` missing in the thesis' `B_{ab} = C*_{0a0b}` and in the bivector dual;
* the trace entries `C^a{}_{iaj} = -E_{ij} - D_{ji} + δ_{ij} tr D` (thesis drops the spatial part);
* the [10]-lemma, `tr B = 0` in the corollary, (3.2), and dim = 10 are proved rather than cited;
* Prop 3.1's symmetry-of-`B` argument (which needs the spatial projector) is replaced by the
  block-form route (`W*` is again Weyl);
* the sign of the `B`-terms in (3.2) is tied to `ω_{bcd} = ω_{abcd} n^a`.

Scope: frame level only (no change of frame / general `g`); this is the pointwise content used
by Chs 3–4. The Lorentz covariance needed to pass from `n = ∂_t` to an arbitrary unit timelike
`n` in (3.2) is not formalised (Prop 3.1 itself is proved for arbitrary `n`).
-/

open Matrix Equiv

noncomputable section

namespace Feec
namespace Bivector

/-! ### The Levi-Civita symbol `eps4` in closed form -/

/-- Integer Levi-Civita symbol on `Fin 4` via the Vandermonde product
`∏_{i<j} (x_j - x_i) / 12` (computable, so finite tables are checked by `decide`). -/
def lcZ (a b c d : Fin 4) : ℤ :=
  ((b : ℤ) - a) * ((c : ℤ) - a) * ((d : ℤ) - a) * ((c : ℤ) - b) * ((d : ℤ) - b) * ((d : ℤ) - c) / 12

/-- `lcZ` is the sign on permutations. -/
private theorem lcZ_perm : ∀ σ : Perm (Fin 4),
    ((Perm.sign σ : ℤˣ) : ℤ) = lcZ (σ 0) (σ 1) (σ 2) (σ 3) := by decide

/-- `lcZ` vanishes on repeated indices. -/
private theorem lcZ_not_inj : ∀ a b c d : Fin 4,
    ¬ Function.Injective ![a, b, c, d] → lcZ a b c d = 0 := by decide

/-- The foundation's determinant definition of `eps4` agrees with the closed form `lcZ`. -/
theorem eps4_eq (a b c d : Fin 4) : eps4 a b c d = (lcZ a b c d : ℝ) := by
  have hM : Matrix.of ![Pi.single a (1 : ℝ), Pi.single b 1, Pi.single c 1, Pi.single d 1] =
      Matrix.of fun i j => if ![a, b, c, d] i = j then (1 : ℝ) else 0 := by
    ext i j; fin_cases i <;> simp [Pi.single_apply, eq_comm]
  unfold eps4; rw [hM]
  by_cases hinj : Function.Injective ![a, b, c, d]
  · set σ : Perm (Fin 4) := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj)
    have h1 : (Matrix.of fun i j => if ![a, b, c, d] i = j then (1 : ℝ) else 0) =
        σ.permMatrix ℝ := by
      ext i j; simp [σ, PEquiv.toMatrix_apply]
    rw [h1, Matrix.det_permutation, lcZ_perm σ]
    simp [σ]
  · rw [lcZ_not_inj a b c d hinj]
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, ![a, b, c, d] i = ![a, b, c, d] j ∧ i ≠ j := by
      by_contra h; push Not at h
      exact hinj fun i j hij => by_contra fun hne => hne (h i j hij)
    simp only [Int.cast_zero]
    exact Matrix.det_zero_of_row_eq hne (by ext k; simp [hij])

/-- `ε_{abcd} = ε_{cdab}` (swapping two pairs is an even permutation). -/
theorem eps4_swap_pairs (a b c d : Fin 4) : eps4 a b c d = eps4 c d a b := by
  rw [eps4_eq, eps4_eq]; congr 1; revert a b c d; decide

/-- `ε_{bacd} = -ε_{abcd}`. -/
theorem eps4_swap01 (a b c d : Fin 4) : eps4 b a c d = -eps4 a b c d := by
  rw [eps4_eq, eps4_eq, ← Int.cast_neg]; congr 1; revert a b c d; decide

/-- `ε_{0123} = 1`. -/
theorem eps4_0123 : eps4 0 1 2 3 = 1 := by simp [eps4_eq, lcZ]

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
def ofMat (M : Matrix Ix Ix ℝ) : T4 (Fin 4) :=
  fun a b c d => ∑ I, ∑ J, β I a b * β J c d * M I J

/-- the double 2-form whose bivector matrix is `[[E, B], [H, D]]`. -/
def T (E B H D : Matrix (Fin 3) (Fin 3) ℝ) : T4 (Fin 4) := ofMat (fromBlocks E B H D)

/-- the bivector matrix `M_{IJ} = C(e_I, e_J) = C_{p_I q_I p_J q_J}` of a (0,4)-tensor. -/
def toMat (C : T4 (Fin 4)) : Matrix Ix Ix ℝ := Matrix.of fun I J => C (p I) (q I) (p J) (q J)

/-- sign of the pair `(a, b)` relative to the basis bivector `pidx a b` (zero on the diagonal). -/
def sgn : Fin 4 → Fin 4 → ℝ :=
  ![![0, 1, 1, 1], ![-1, 0, 1, -1], ![-1, -1, 0, 1], ![-1, 1, -1, 0]]

/-- the basis bivector carrying the pair `(a, b)`. -/
def pidx : Fin 4 → Fin 4 → Ix :=
  ![![.inl 0, .inl 0, .inl 1, .inl 2], ![.inl 0, .inl 0, .inr 2, .inr 1],
    ![.inl 1, .inr 2, .inl 0, .inr 0], ![.inl 2, .inr 1, .inr 0, .inl 0]]

/-- the basis bivectors in table form. -/
theorem β_eq (I : Ix) (a b : Fin 4) : β I a b = if I = pidx a b then sgn a b else 0 := by
  rcases I with i | i <;> fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [β, p, q, pidx, sgn]

/-- components of `ofMat M` are signed entries of `M`. -/
theorem ofMat_apply (M : Matrix Ix Ix ℝ) (a b c d : Fin 4) :
    ofMat M a b c d = sgn a b * sgn c d * M (pidx a b) (pidx c d) := by
  simp only [ofMat, β_eq, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- `sgn` is skew. -/
theorem sgn_swap (a b : Fin 4) : sgn b a = -sgn a b := by
  fin_cases a <;> fin_cases b <;> simp [sgn]

/-- `pidx` is symmetric. -/
theorem pidx_swap (a b : Fin 4) : pidx b a = pidx a b := by
  fin_cases a <;> fin_cases b <;> rfl

/-- the legs `(p I, q I)` carry the bivector `I` with sign `+1`. -/
theorem sgn_pq (I : Ix) : sgn (p I) (q I) = 1 ∧ pidx (p I) (q I) = I := by
  rcases I with i | i <;> fin_cases i <;> simp [sgn, pidx, p, q]

/-- every skew 2-form is the combination of basis bivectors: `w_{ab} = ± w(e_{pidx a b})`. -/
theorem skew2_expand (w : Fin 4 → Fin 4 → ℝ) (hw : ∀ a b, w a b = -w b a) (a b : Fin 4) :
    w a b = sgn a b * w (p (pidx a b)) (q (pidx a b)) := by
  have h00 := hw 0 0; have h11 := hw 1 1; have h22 := hw 2 2; have h33 := hw 3 3
  fin_cases a <;> fin_cases b <;> simp [sgn, pidx, p, q] <;>
    linarith [hw 0 1, hw 0 2, hw 0 3, hw 1 2, hw 1 3, hw 2 3]

/-- the bivector matrix of `ofMat M` is `M`. -/
theorem toMat_ofMat (M : Matrix Ix Ix ℝ) : toMat (ofMat M) = M := by
  ext I J; simp [toMat, ofMat_apply, (sgn_pq I).1, (sgn_pq I).2, (sgn_pq J).1, (sgn_pq J).2]

/-- `ofMat` is injective. -/
theorem ofMat_injective : Function.Injective ofMat := fun M N h => by
  rw [← toMat_ofMat M, ← toMat_ofMat N, h]

/-- every `ofMat M` is a double 2-form. -/
theorem pairSkew_ofMat (M : Matrix Ix Ix ℝ) : PairSkew (ofMat M) := by
  intro a b c d
  rw [ofMat_apply, ofMat_apply, ofMat_apply, sgn_swap a b, sgn_swap c d, pidx_swap a b,
    pidx_swap c d]
  constructor <;> ring

/-- A double 2-form is determined by its bivector matrix. -/
theorem eq_ofMat_toMat {C : T4 (Fin 4)} (hC : PairSkew C) : C = ofMat (toMat C) := by
  funext a b c d
  rw [ofMat_apply]
  simp only [toMat, Matrix.of_apply]
  rw [skew2_expand (fun a b => C a b c d) (fun a b => (hC a b c d).1) a b,
    skew2_expand (fun c d => C (p (pidx a b)) (q (pidx a b)) c d)
      (fun c d => (hC _ _ c d).2) c d]
  ring

/-- the `E`-block of the bivector matrix (thesis: `[[E, B], [H, D]]`). -/
def blkE (C : T4 (Fin 4)) : Matrix (Fin 3) (Fin 3) ℝ := (toMat C).toBlocks₁₁
/-- the `B`-block. -/
def blkB (C : T4 (Fin 4)) : Matrix (Fin 3) (Fin 3) ℝ := (toMat C).toBlocks₁₂
/-- the `H`-block. -/
def blkH (C : T4 (Fin 4)) : Matrix (Fin 3) (Fin 3) ℝ := (toMat C).toBlocks₂₁
/-- the `D`-block. -/
def blkD (C : T4 (Fin 4)) : Matrix (Fin 3) (Fin 3) ℝ := (toMat C).toBlocks₂₂

/-- the `E`-block is literally the thesis' `E_{ab} = C_{0a0b}` (spatial `a, b`). -/
theorem blkE_apply (C : T4 (Fin 4)) (i j : Fin 3) : blkE C i j = C 0 i.succ 0 j.succ := by
  fin_cases i <;> fin_cases j <;> rfl

/-- a double 2-form is `T` of its four blocks. -/
theorem eq_T_blocks {C : T4 (Fin 4)} (hC : PairSkew C) :
    C = T (blkE C) (blkB C) (blkH C) (blkD C) := by
  rw [T, blkE, blkB, blkH, blkD, fromBlocks_toBlocks]; exact eq_ofMat_toMat hC

/-- the `E`-block of `T E B H D`. -/
@[simp] theorem blkE_T (E B H D : Matrix (Fin 3) (Fin 3) ℝ) : blkE (T E B H D) = E := by
  simp [blkE, T, toMat_ofMat]
/-- the `B`-block of `T E B H D`. -/
@[simp] theorem blkB_T (E B H D : Matrix (Fin 3) (Fin 3) ℝ) : blkB (T E B H D) = B := by
  simp [blkB, T, toMat_ofMat]
/-- the `H`-block of `T E B H D`. -/
@[simp] theorem blkH_T (E B H D : Matrix (Fin 3) (Fin 3) ℝ) : blkH (T E B H D) = H := by
  simp [blkH, T, toMat_ofMat]
/-- the `D`-block of `T E B H D`. -/
@[simp] theorem blkD_T (E B H D : Matrix (Fin 3) (Fin 3) ℝ) : blkD (T E B H D) = D := by
  simp [blkD, T, toMat_ofMat]

/-- `T` commutes with negation. -/
theorem T_neg (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    T (-E) (-B) (-H) (-D) = -T E B H D := by
  funext a b c d; simp [T, ofMat_apply, ← fromBlocks_neg]

/-- `T` is injective. -/
theorem T_inj {E B H D E' B' H' D' : Matrix (Fin 3) (Fin 3) ℝ} :
    T E B H D = T E' B' H' D' ↔ E = E' ∧ B = B' ∧ H = H' ∧ D = D' := by
  rw [T, T, ofMat_injective.eq_iff, fromBlocks_inj]

/-! ### Hodge duals of a double 2-form -/

/-- right dual `C*_{abcd} = ½ C_{abef} ω^{ef}{}_{cd}` (Minkowski frame, `ω = ε`). -/
def rdual (C : T4 (Fin 4)) : T4 (Fin 4) :=
  fun a b c d => (1 / 2) * ∑ e, ∑ f, C a b e f * η e * η f * eps4 e f c d

/-- left dual `*C_{abcd} = ½ ω_{ab}{}^{ef} C_{efcd}`. -/
def ldual (C : T4 (Fin 4)) : T4 (Fin 4) :=
  fun a b c d => (1 / 2) * ∑ e, ∑ f, eps4 a b e f * η e * η f * C e f c d

/-- the pair interchange `C_{abcd} ↦ C_{cdab}`. -/
def swapPairs (C : T4 (Fin 4)) : T4 (Fin 4) := fun a b c d => C c d a b

/-- the Hodge star on bivectors in the basis `(t∧x, t∧y, t∧z | y∧z, z∧x, x∧y)`. -/
def S : Matrix Ix Ix ℝ := fromBlocks 0 (-1) 1 0

/-- right dualisation multiplies the bivector matrix by the Hodge matrix `S` on the right
(`t∧x ↦ y∧z`, `y∧z ↦ -t∧x`, cyclically, as in the proof of Thesis Prop 3.2). -/
theorem rdual_ofMat (M : Matrix Ix Ix ℝ) : rdual (ofMat M) = ofMat (M * S) := by
  funext a b c d
  simp only [rdual, ofMat_apply]
  generalize pidx a b = I
  fin_cases c <;> fin_cases d <;>
    simp [Fin.sum_univ_four, eps4_eq, lcZ, sgn, pidx, η, S, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_three] <;> ring

/-- pair interchange transposes the bivector matrix. -/
theorem swapPairs_ofMat (M : Matrix Ix Ix ℝ) : swapPairs (ofMat M) = ofMat Mᵀ := by
  funext a b c d; simp only [swapPairs, ofMat_apply, transpose_apply]; ring

/-- the left dual is the right dual conjugated by the pair interchange. -/
theorem ldual_eq (C : T4 (Fin 4)) : ldual C = swapPairs (rdual (swapPairs C)) := by
  funext a b c d
  simp only [ldual, swapPairs, rdual]
  congr 1
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  rw [eps4_swap_pairs a b e f]; ring

/-- left dualisation multiplies the bivector matrix by `Sᵀ` on the left. -/
theorem ldual_ofMat (M : Matrix Ix Ix ℝ) : ldual (ofMat M) = ofMat (Sᵀ * M) := by
  rw [ldual_eq, swapPairs_ofMat, rdual_ofMat, swapPairs_ofMat, transpose_mul, transpose_transpose]

/-- **Thesis Prop 3.2 (right dual).** `C ↦ C*` acts on blocks as `[[E,B],[H,D]] ↦ [[B,-E],[D,-H]]`.

Correction: the thesis' formula `C*_{abcd} v^c w^d = C_{abef} (ε^{ef}{}_{cd} v^c w^d)` and
`B_{ab} = C_{0aef} ε^{ef}{}_{0b}` miss the factor `½` (without it `t∧x ↦ 2 y∧z`); `rdual`
includes it. -/
theorem rdual_T (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    rdual (T E B H D) = T B (-E) D (-H) := by
  rw [T, rdual_ofMat, S, fromBlocks_multiply, T]; simp

/-- **Thesis Prop 3.2 (left dual).** `C ↦ *C` acts as `[[E,B],[H,D]] ↦ [[H,D],[-E,-B]]`. -/
theorem ldual_T (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    ldual (T E B H D) = T H D (-E) (-B) := by
  rw [T, ldual_ofMat, S, fromBlocks_transpose, fromBlocks_multiply, T]; simp

/-- **Thesis Prop 3.2 (double dual).** `C ↦ *C*` acts as `[[E,B],[H,D]] ↦ [[D,-H],[-B,E]]`. -/
theorem ldual_rdual_T (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    ldual (rdual (T E B H D)) = T D (-H) (-B) E := by
  rw [rdual_T, ldual_T, neg_neg]


/-- **Thesis Prop 3.2.** For a double 2-form `C` (skew in each pair) set, as in the thesis,
`E_{ab} = C_{0a0b}`, `B_{ab} = C*_{0a0b}`, `H_{ab} = *C_{0a0b}`, `D_{ab} = *C*_{0a0b}`.
Then `C` has bivector block matrix `[[E,B],[H,D]]`, and the three duals act as stated.

Correction: `B, H, D` carry the factor `½` built into `rdual`/`ldual` (missing in the thesis'
formula for `B_{ab}`). -/
theorem prop_3_2 {C : T4 (Fin 4)} (hC : PairSkew C) :
    let E : Matrix (Fin 3) (Fin 3) ℝ := fun i j => C 0 i.succ 0 j.succ
    let B : Matrix (Fin 3) (Fin 3) ℝ := fun i j => rdual C 0 i.succ 0 j.succ
    let H : Matrix (Fin 3) (Fin 3) ℝ := fun i j => ldual C 0 i.succ 0 j.succ
    let D : Matrix (Fin 3) (Fin 3) ℝ := fun i j => ldual (rdual C) 0 i.succ 0 j.succ
    C = T E B H D ∧ rdual C = T B (-E) D (-H) ∧ ldual C = T H D (-E) (-B) ∧
      ldual (rdual C) = T D (-H) (-B) E := by
  intro E B H D
  have hT := eq_T_blocks hC
  have hE : E = blkE C := by ext i j; simp [E, blkE_apply]
  have hB : B = blkB C := by
    ext i j; simp only [B]; rw [← blkE_apply (rdual C), hT, rdual_T, blkE_T, blkB_T]
  have hH : H = blkH C := by
    ext i j; simp only [H]; rw [← blkE_apply (ldual C), hT, ldual_T, blkE_T, blkH_T]
  have hD : D = blkD C := by
    ext i j; simp only [D]; rw [← blkE_apply (ldual (rdual C)), hT, ldual_rdual_T, blkE_T, blkD_T]
  rw [hE, hB, hH, hD]
  refine ⟨hT, ?_, ?_, ?_⟩ <;> conv_lhs => rw [hT]
  · exact rdual_T _ _ _ _
  · exact ldual_T _ _ _ _
  · exact ldual_rdual_T _ _ _ _

/-- Thesis §3.2: `(W*)* = -W` for every double 2-form (`** = -1` on 2-forms, signature
`(-+++)`). -/
theorem rdual_rdual {C : T4 (Fin 4)} (hC : PairSkew C) : rdual (rdual C) = -C := by
  rw [eq_T_blocks hC, rdual_T, rdual_T, T_neg]

/-- `*(*W) = -W` for every double 2-form. -/
theorem ldual_ldual {C : T4 (Fin 4)} (hC : PairSkew C) : ldual (ldual C) = -C := by
  rw [eq_T_blocks hC, ldual_T, ldual_T, T_neg]

/-- left and right duals commute. -/
theorem ldual_rdual_comm {C : T4 (Fin 4)} (hC : PairSkew C) :
    ldual (rdual C) = rdual (ldual C) := by
  rw [eq_T_blocks hC, rdual_T, ldual_T, ldual_T, rdual_T]

/-- Thesis §3.2: for `W` with the interchange symmetry, `*W_{abcd} = W*_{cdab}`. -/
theorem ldual_eq_rdual_swap {C : T4 (Fin 4)} (hC : Interchange C) (a b c d : Fin 4) :
    ldual C a b c d = rdual C c d a b := by
  rw [ldual_eq]; simp only [swapPairs, rdual]
  congr 1
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  rw [hC]


/-! ### Prop 3.3: interchange, total antisymmetry, trace -/

/-- interchange symmetry as a fixed point of `swapPairs`. -/
theorem interchange_iff_swapPairs (C : T4 (Fin 4)) : Interchange C ↔ swapPairs C = C := by
  constructor
  · intro h; funext a b c d; exact (h a b c d).symm
  · intro h a b c d; exact (congrFun (congrFun (congrFun (congrFun h a) b) c) d).symm

/-- interchange symmetry is symmetry of the bivector matrix. -/
theorem interchange_ofMat_iff (M : Matrix Ix Ix ℝ) : Interchange (ofMat M) ↔ Mᵀ = M := by
  rw [interchange_iff_swapPairs, swapPairs_ofMat, ofMat_injective.eq_iff]

/-- **Thesis Prop 3.3(i).** The interchange symmetry `C_{abcd} = C_{cdab}` is equivalent to
`E, D` symmetric and `H = Bᵀ`. -/
theorem interchange_iff (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    Interchange (T E B H D) ↔ Eᵀ = E ∧ Dᵀ = D ∧ H = Bᵀ := by
  rw [T, interchange_ofMat_iff, fromBlocks_transpose, fromBlocks_inj]
  constructor
  · rintro ⟨h1, -, h3, h4⟩; exact ⟨h1, h4, h3.symm⟩
  · rintro ⟨h1, h4, h3⟩; exact ⟨h1, by rw [h3, transpose_transpose], h3.symm, h4⟩

/-- total antisymmetrisation `C_{[abcd]} = (1/4!) ∑_σ sgn σ C_{σ(abcd)}`. -/
def alt4 (C : T4 (Fin 4)) : T4 (Fin 4) := fun a b c d =>
  (1 / 24) * ∑ σ : Perm (Fin 4), (Perm.sign σ : ℝ) *
    C (![a, b, c, d] (σ 0)) (![a, b, c, d] (σ 1)) (![a, b, c, d] (σ 2)) (![a, b, c, d] (σ 3))

/-- sum over `Perm (Fin (n+1))` via `decomposeFin`. -/
private theorem sum_perm_succ {n : ℕ} (f : Perm (Fin (n + 1)) → ℝ) :
    ∑ σ, f σ = ∑ p, ∑ e : Perm (Fin n), f (Perm.decomposeFin.symm (p, e)) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv Perm.decomposeFin _ _ (fun σ => by simp)).trans rfl

/-- the 24-term expansion of `C_{[abcd]}`. -/
theorem alt4_expand (C : T4 (Fin 4)) (a b c d : Fin 4) : alt4 C a b c d = (1 / 24) *
    (C a b c d - C a b d c - C a c b d + C a c d b - C a d c b + C a d b c
     - C b a c d + C b a d c + C b c a d - C b c d a + C b d c a - C b d a c
     - C c b a d + C c b d a + C c a b d - C c a d b + C c d a b - C c d b a
     - C d b c a + C d b a c + C d c b a - C d c a b + C d a c b - C d a b c) := by
  simp only [alt4, sum_perm_succ, Fin.sum_univ_succ, Perm.decomposeFin.symm_sign,
    Fintype.sum_unique]
  simp only [show (2 : Fin 4) = Fin.succ 1 from rfl, show (3 : Fin 4) = Fin.succ 2 from rfl,
    show (1 : Fin 4) = Fin.succ 0 from rfl, show (2 : Fin 3) = Fin.succ 1 from rfl,
    show (1 : Fin 3) = Fin.succ 0 from rfl, show (1 : Fin 2) = Fin.succ 0 from rfl,
    Perm.decomposeFin_symm_apply_succ, Perm.decomposeFin_symm_apply_zero]
  simp [Equiv.swap_apply_def]
  ring

/-- `C_{[abcd]}` changes by `sgn τ` under a permutation of its slots. -/
private theorem alt4_comp (C : T4 (Fin 4)) (v : Fin 4 → Fin 4) (τ : Perm (Fin 4)) :
    alt4 C (v (τ 0)) (v (τ 1)) (v (τ 2)) (v (τ 3)) =
      (Perm.sign τ : ℝ) * alt4 C (v 0) (v 1) (v 2) (v 3) := by
  have hv : ∀ w : Fin 4 → Fin 4, ![w 0, w 1, w 2, w 3] = w := fun w => by
    ext i; fin_cases i <;> rfl
  simp only [alt4]
  have e1 : ![v (τ 0), v (τ 1), v (τ 2), v (τ 3)] = fun k => v (τ k) := hv (fun k => v (τ k))
  rw [e1, hv v, ← Equiv.sum_comp (Equiv.mulLeft τ⁻¹)]
  have hτ : ∀ x, τ (τ⁻¹ x) = x := fun x => by simp
  simp only [Equiv.coe_mulLeft, Perm.mul_apply, hτ, Perm.sign_mul, Perm.sign_inv,
    Units.val_mul, Int.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

/-- `C_{[abcd]} = ε_{abcd} C_{[0123]}` (in 4 dimensions `Λ⁴` is a line). -/
theorem alt4_eq_eps (C : T4 (Fin 4)) (a b c d : Fin 4) :
    alt4 C a b c d = eps4 a b c d * alt4 C 0 1 2 3 := by
  set v : Fin 4 → Fin 4 := ![a, b, c, d]
  by_cases hinj : Function.Injective v
  · set σ : Perm (Fin 4) := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj)
    have h := alt4_comp C id σ
    simp only [id] at h
    have he : eps4 a b c d = (Perm.sign σ : ℝ) := by
      rw [eps4_eq]
      have := lcZ_perm σ
      simp only [σ, Equiv.ofBijective_apply, v] at this
      exact_mod_cast this.symm
    rw [he]; simpa [σ, v] using h
  · obtain ⟨i, j, hij, hne⟩ : ∃ i j, v i = v j ∧ i ≠ j := by
      by_contra h; push Not at h
      exact hinj fun i j hij => by_contra fun hne => hne (h i j hij)
    have h := alt4_comp C v (Equiv.swap i j)
    have hvs : ∀ k, v (Equiv.swap i j k) = v k := fun k => by
      rcases eq_or_ne k i with rfl | hki
      · simp [hij]
      rcases eq_or_ne k j with rfl | hkj
      · simp [hij]
      rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
    rw [hvs, hvs, hvs, hvs, Perm.sign_swap hne] at h
    have h0 : alt4 C (v 0) (v 1) (v 2) (v 3) = 0 := by push_cast at h; linarith
    have h0' : alt4 C a b c d = 0 := h0
    rw [h0', eps4_eq, lcZ_not_inj _ _ _ _ hinj]; simp

/-- For a double 2-form, `C_{[0123]}` has the six-term form of the thesis' proof of Prop 3.3. -/
theorem alt4_0123 {C : T4 (Fin 4)} (hC : PairSkew C) : alt4 C 0 1 2 3 =
    (1 / 6) * (C 0 1 2 3 + C 0 2 3 1 + C 0 3 1 2 + C 2 3 0 1 + C 3 1 0 2 + C 1 2 0 3) := by
  rw [alt4_expand]
  have s1 := fun a b c d => (hC a b c d).1
  have s2 := fun a b c d => (hC a b c d).2
  linarith [s2 0 1 2 3, s1 1 0 2 3, s1 1 0 3 2, s2 0 2 1 3, s1 2 0 1 3, s1 2 0 3 1,
    s2 0 2 3 1, s2 0 3 2 1, s1 3 0 2 1, s1 3 0 1 2, s2 0 3 1 2, s2 1 2 0 3, s1 2 1 0 3,
    s1 2 1 3 0, s2 1 2 3 0, s2 1 3 2 0, s1 3 1 2 0, s1 3 1 0 2, s2 1 3 0 2, s1 1 3 0 2,
    s2 2 3 0 1, s1 3 2 0 1, s1 3 2 1 0, s2 2 3 1 0, s2 0 1 3 2, s1 0 2 1 3, s1 0 3 2 1,
    s1 1 2 3 0, s1 0 2 3 1]

/-- **Thesis Prop 3.3(ii).** `C_{[abcd]} = 0` is equivalent to `tr B + tr H = 0`. -/
theorem alt_iff (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    (∀ a b c d, alt4 (T E B H D) a b c d = 0) ↔ trace B + trace H = 0 := by
  have h6 : alt4 (T E B H D) 0 1 2 3 = (1 / 6) * (trace B + trace H) := by
    rw [T, alt4_0123 (pairSkew_ofMat _)]
    simp [ofMat_apply, sgn, pidx, trace, Fin.sum_univ_three]; ring
  constructor
  · intro h; have := h 0 1 2 3; rw [h6] at this; linarith
  · intro h a b c d; rw [alt4_eq_eps, h6, h]; ring


/-- First Bianchi `C_{a[bcd]} = 0` for a double 2-form is equivalent to the interchange symmetry
plus `C_{[abcd]} = 0` (thesis: "the 16 conditions ... break into 15 + 1", cited from [10]).

Thesis gap: the thesis cites this without proof; it is proved here. -/
theorem bianchi_iff {C : T4 (Fin 4)} (hC : PairSkew C) :
    Bianchi1 C ↔ Interchange C ∧ ∀ a b c d, alt4 C a b c d = 0 := by
  have s1 := fun a b c d => (hC a b c d).1
  have s2 := fun a b c d => (hC a b c d).2
  constructor
  · intro hB
    have hI : Interchange C := fun a b c d => by
      linarith [hB a b c d, hB a b d c, hB a c b d, hB a c d b, hB a d b c, hB a d c b, hB b a c d,
          hB b a d c, hB b c a d, hB b c d a, hB b d a c, hB b d c a, hB c a b d, hB c a d b,
          hB c b a d, hB c b d a, hB c d a b, hB c d b a, hB d a b c, hB d a c b, hB d b a c,
          hB d b c a, hB d c a b, hB d c b a, s1 a b c d, s1 a b d c, s1 a c b d, s1 a c d b,
          s1 a d b c, s1 a d c b, s1 b a c d, s1 b a d c, s1 b c a d, s1 b c d a, s1 b d a c,
          s1 b d c a, s1 c a b d, s1 c a d b, s1 c b a d, s1 c b d a, s1 c d a b, s1 c d b a,
          s1 d a b c, s1 d a c b, s1 d b a c, s1 d b c a, s1 d c a b, s1 d c b a, s2 a b c d,
          s2 a b d c, s2 a c b d, s2 a c d b, s2 a d b c, s2 a d c b, s2 b a c d, s2 b a d c,
          s2 b c a d, s2 b c d a, s2 b d a c, s2 b d c a, s2 c a b d, s2 c a d b, s2 c b a d,
          s2 c b d a, s2 c d a b, s2 c d b a, s2 d a b c, s2 d a c b, s2 d b a c, s2 d b c a,
          s2 d c a b, s2 d c b a]
    refine ⟨hI, fun a b c d => ?_⟩
    rw [alt4_eq_eps, alt4_0123 hC]
    have := hB 0 1 2 3
    rw [hI 2 3 0 1, hI 3 1 0 2, hI 1 2 0 3, s2 0 2 3 1, s2 0 3 1 2]
    rw [s2 0 2 3 1, s2 0 3 1 2] at this
    apply mul_eq_zero_of_right; linarith
  · rintro ⟨hI, hA⟩ a b c d
    have h := hA a b c d
    rw [alt4_expand] at h
    linarith [s1 a b c d, s1 a b d c, s1 a c b d, s1 a c d b, s1 a d b c, s1 a d c b, s1 b a c d,
        s1 b a d c, s1 b c a d, s1 b c d a, s1 b d a c, s1 b d c a, s1 c a b d, s1 c a d b,
        s1 c b a d, s1 c b d a, s1 c d a b, s1 c d b a, s1 d a b c, s1 d a c b, s1 d b a c,
        s1 d b c a, s1 d c a b, s1 d c b a, s2 a b c d, s2 a b d c, s2 a c b d, s2 a c d b,
        s2 a d b c, s2 a d c b, s2 b a c d, s2 b a d c, s2 b c a d, s2 b c d a, s2 b d a c,
        s2 b d c a, s2 c a b d, s2 c a d b, s2 c b a d, s2 c b d a, s2 c d a b, s2 c d b a,
        s2 d a b c, s2 d a c b, s2 d b a c, s2 d b c a, s2 d c a b, s2 d c b a, hI a b c d,
        hI a b d c, hI a c b d, hI a c d b, hI a d b c, hI a d c b, hI b a c d, hI b a d c,
        hI b c a d, hI b c d a, hI b d a c, hI b d c a, hI c a b d, hI c a d b, hI c b a d,
        hI c b d a, hI c d a b, hI c d b a, hI d a b c, hI d a c b, hI d b a c, hI d b c a,
        hI d c a b, hI d c b a]

/-- Thesis Prop 3.3, Bianchi part: for `C = [[E,B],[H,D]]`, first Bianchi holds iff
`E, D` are symmetric, `H = Bᵀ` and `tr B + tr H = 0`. -/
theorem bianchi_T_iff (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    Bianchi1 (T E B H D) ↔ (Eᵀ = E ∧ Dᵀ = D ∧ H = Bᵀ) ∧ trace B + trace H = 0 := by
  rw [bianchi_iff (C := T E B H D) (pairSkew_ofMat _), interchange_iff, alt_iff]

/-- the Minkowski trace `C^a{}_{bac} = ∑_a η^{aa} C_{abac}`. -/
def mtr (C : T4 (Fin 4)) (b c : Fin 4) : ℝ := ∑ a, η a * C a b a c

/-- The 16 Minkowski traces of `[[E,B],[H,D]]`.

Correction: the thesis' "6-tuple" step `C^a{}_{iaj} = -C_{0i0j}` drops the spatial terms;
the correct entry is `-E_{ij} - D_{ji} + δ_{ij} tr D`. -/
theorem mtr_T (E B H D : Matrix (Fin 3) (Fin 3) ℝ) (b c : Fin 4) : mtr (T E B H D) b c = ![
    ![trace E, B 1 2 - B 2 1, B 2 0 - B 0 2, B 0 1 - B 1 0],
    ![H 2 1 - H 1 2, -E 0 0 - D 0 0 + trace D, -E 0 1 - D 1 0, -E 0 2 - D 2 0],
    ![H 0 2 - H 2 0, -E 1 0 - D 0 1, -E 1 1 - D 1 1 + trace D, -E 1 2 - D 2 1],
    ![H 1 0 - H 0 1, -E 2 0 - D 0 2, -E 2 1 - D 1 2, -E 2 2 - D 2 2 + trace D]] b c := by
  fin_cases b <;> fin_cases c <;>
    simp [mtr, T, ofMat_apply, sgn, pidx, η, Fin.sum_univ_four, trace, Fin.sum_univ_three] <;> ring

/-- **Thesis Prop 3.3(iii).** `η`-trace-freeness `C^a{}_{bac} = 0` is equivalent to
`tr E = 0`, `B, H` symmetric and `D = -Eᵀ`.

Thesis gap: the final step `D = -Eᵀ + δ tr E/2` uses `tr E = 0` (from the singleton
condition) and the summed diagonal equations `tr D = tr E / 2`; both are made explicit. -/
theorem tracefree_iff (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    (∀ b c, mtr (T E B H D) b c = 0) ↔ trace E = 0 ∧ Bᵀ = B ∧ Hᵀ = H ∧ D = -Eᵀ := by
  simp only [mtr_T]
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

/-! ### Algebraic Weyl tensors: the block form -/

/-- An algebraic Weyl tensor in a Minkowski orthonormal frame: skew in each pair, first
Bianchi identity, and `η`-trace-free. -/
structure IsWeylLike (C : T4 (Fin 4)) : Prop where
  pairSkew : PairSkew C
  bianchi : Bianchi1 C
  traceFree : ∀ b c, mtr C b c = 0

/-- **Thesis Prop 3.3, corollary.** `C` is an algebraic Weyl tensor iff its bivector matrix is
`[[E, B], [B, -E]]` with `E, B` symmetric and trace-free.

Thesis gap: `tr B = 0` needs Prop 3.3(ii) together with `H = Bᵀ = B`; the thesis does not say
so. -/
theorem weyl_iff (C : T4 (Fin 4)) :
    IsWeylLike C ↔ ∃ E B : Matrix (Fin 3) (Fin 3) ℝ, Eᵀ = E ∧ trace E = 0 ∧ Bᵀ = B ∧
      trace B = 0 ∧ C = T E B B (-E) := by
  constructor
  · rintro ⟨hS, hB, hT⟩
    have hC := eq_T_blocks hS
    rw [hC] at hB hT
    obtain ⟨⟨hE, -, hH⟩, htr⟩ := (bianchi_T_iff _ _ _ _).1 hB
    obtain ⟨htrE, hBs, -, hD⟩ := (tracefree_iff _ _ _ _).1 hT
    have hHB : blkH C = blkB C := by rw [hH, hBs]
    refine ⟨blkE C, blkB C, hE, htrE, hBs, ?_, ?_⟩
    · rw [hHB] at htr; linarith
    · rw [hC, hHB, hD, hE]; simp
  · rintro ⟨E, B, hE, htrE, hB, htrB, rfl⟩
    refine ⟨pairSkew_ofMat _, (bianchi_T_iff _ _ _ _).2 ⟨⟨hE, ?_, hB.symm⟩, ?_⟩,
      (tracefree_iff _ _ _ _).2 ⟨htrE, hB, hB, by rw [hE]⟩⟩
    · rw [transpose_neg, hE]
    · rw [htrB]; ring

/-- **Thesis §3.2 (omitted classical fact).** For an algebraic Weyl tensor the left and right
duals coincide, `*W = W*`; both have block matrix `[[B, -E], [-E, -B]]`. -/
theorem ldual_eq_rdual {W : T4 (Fin 4)} (hW : IsWeylLike W) : ldual W = rdual W := by
  obtain ⟨E, B, -, -, -, -, rfl⟩ := (weyl_iff W).1 hW
  rw [ldual_T, rdual_T]

/-- The right dual of an algebraic Weyl tensor is again one (`E ↦ B`, `B ↦ -E`). -/
theorem IsWeylLike.rdual {W : T4 (Fin 4)} (hW : IsWeylLike W) : IsWeylLike (rdual W) := by
  obtain ⟨E, B, hE, htrE, hB, htrB, rfl⟩ := (weyl_iff W).1 hW
  rw [rdual_T, weyl_iff]
  exact ⟨B, -E, hB, htrB, by rw [transpose_neg, hE], by rw [trace_neg, htrE, neg_zero], rfl⟩

/-- A sum of a skew kernel against `n ⊗ n` vanishes. -/
private theorem sum_sym_skew (n : Fin 4 → ℝ) (X : Fin 4 → Fin 4 → ℝ)
    (hX : ∀ a c, X a c = -X c a) : ∑ a, ∑ c, n a * n c * X a c = 0 := by
  have h : ∑ a, ∑ c, n a * n c * X a c = -∑ a, ∑ c, n a * n c * X a c := by
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [hX]; ring
  linarith

/-- reorder a triple sum. -/
private theorem sum3_rot (f : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ a, ∑ c, ∑ d, f a c d = ∑ d, ∑ a, ∑ c, f a c d :=
  (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm

/-- The electric part `E_{ab} = n^c n^d W_{cadb}` of an algebraic Weyl tensor is symmetric,
`η`-trace-free and orthogonal to `n`, for every vector `n`. -/
theorem electric_props {W : T4 (Fin 4)} (hW : IsWeylLike W) (n : Fin 4 → ℝ) :
    let E : Fin 4 → Fin 4 → ℝ := fun a b => ∑ c, ∑ d, n c * n d * W c a d b
    (∀ a b, E a b = E b a) ∧ ∑ a, η a * E a a = 0 ∧
      (∀ b, ∑ a, n a * E a b = 0) ∧ ∀ a, ∑ b, E a b * n b = 0 := by
  intro E
  have hI := ((bianchi_iff hW.pairSkew).1 hW.bianchi).1
  have s1 := fun a b c d => (hW.pairSkew a b c d).1
  have s2 := fun a b c d => (hW.pairSkew a b c d).2
  have hsym : ∀ a b, E a b = E b a := fun a b => by
    simp only [E]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [hI d a c b]; ring
  have horth : ∀ b, ∑ a, n a * E a b = 0 := fun b => by
    calc ∑ a, n a * E a b = ∑ a, ∑ c, ∑ d, n d * (n a * n c * W c a d b) := by
          simp only [E, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
            Finset.sum_congr rfl fun d _ => ?_
          ring
      _ = ∑ d, ∑ a, ∑ c, n d * (n a * n c * W c a d b) := sum3_rot _
      _ = ∑ d, n d * ∑ a, ∑ c, n a * n c * W c a d b := by simp only [Finset.mul_sum]
      _ = 0 := Finset.sum_eq_zero fun d _ => by
          rw [sum_sym_skew n _ (fun a c => s1 c a d b), mul_zero]
  refine ⟨hsym, ?_, horth, fun a => ?_⟩
  · calc ∑ a, η a * E a a = ∑ a, ∑ c, ∑ d, n c * n d * (η a * W a c a d) := by
          simp only [E, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
            Finset.sum_congr rfl fun d _ => ?_
          rw [s1 c a d a, s2 a c d a]; ring
      _ = ∑ c, ∑ d, ∑ a, n c * n d * (η a * W a c a d) := (sum3_rot _).trans (sum3_rot _)
      _ = ∑ c, ∑ d, n c * n d * mtr W c d := by simp only [mtr, Finset.mul_sum]
      _ = 0 := by simp [hW.traceFree]
  · rw [← horth a]
    exact Finset.sum_congr rfl fun b _ => by rw [hsym]; ring

/-- **Thesis Prop 3.1.** For an algebraic Weyl tensor `W` and a vector `n`, the electric and
magnetic tensors `E_{ab} = n^c n^d W_{cadb}`, `B_{ab} = n^c n^d W*_{cadb}` are symmetric,
trace-free and orthogonal to `n`.

Thesis gap: the thesis' proof of the symmetry of `B` uses the 3D contraction
`ω^{baq} ω_{bef} = δ^a_e δ^q_f - δ^a_f δ^q_e`, which only holds with the spatial projector, and
uses orthogonality before proving it. Here the proof instead goes through the block form
(Prop 3.3): `W*` is again an algebraic Weyl tensor (`IsWeylLike.rdual`, using `*W = W*`), so `B`
is the electric part of `W*` and inherits its properties. Stated in a Minkowski orthonormal
frame; `n` need not be unit timelike for these algebraic conclusions. -/
theorem prop_3_1 {W : T4 (Fin 4)} (hW : IsWeylLike W) (n : Fin 4 → ℝ) :
    let E : Fin 4 → Fin 4 → ℝ := fun a b => ∑ c, ∑ d, n c * n d * W c a d b
    let B : Fin 4 → Fin 4 → ℝ := fun a b => ∑ c, ∑ d, n c * n d * rdual W c a d b
    ((∀ a b, E a b = E b a) ∧ ∑ a, η a * E a a = 0 ∧
      (∀ b, ∑ a, n a * E a b = 0) ∧ ∀ a, ∑ b, E a b * n b = 0) ∧
    ((∀ a b, B a b = B b a) ∧ ∑ a, η a * B a a = 0 ∧
      (∀ b, ∑ a, n a * B a b = 0) ∧ ∀ a, ∑ b, B a b * n b = 0) :=
  ⟨electric_props hW n, electric_props hW.rdual n⟩

/-! ### The reconstruction formula (3.2) -/

/-- `ε_{abdc} = -ε_{abcd}`. -/
theorem eps4_swap23 (a b c d : Fin 4) : eps4 a b d c = -eps4 a b c d := by
  rw [eps4_eq, eps4_eq, ← Int.cast_neg]; congr 1; revert a b c d; decide

/-- the frame metric `g_{ab} = η_{ab}`. -/
def gη (a b : Fin 4) : ℝ := if a = b then η a else 0

/-- `n_a` for `n = ∂_t`. -/
def nL : Fin 4 → ℝ := ![-1, 0, 0, 0]

/-- `l_{ab} = g_{ab} + 2 n_a n_b`. -/
def lmet (a b : Fin 4) : ℝ := gη a b + 2 * nL a * nL b

/-- `ω^e{}_{ab}` for the spatial volume form `ω_{bcd} = ω_{abcd} n^a`, `n = ∂_t`. -/
def ωU (e a b : Fin 4) : ℝ := η e * eps4 0 e a b

/-- explicit table of `ω^e{}_{ab}`. -/
theorem ωU_eq (e a b : Fin 4) : ωU e a b = (
    ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, -1, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, 0, 0], ![0, 1, 0, 0]],
    ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, -1, 0, 0], ![0, 0, 0, 0]]]
      : Fin 4 → Fin 4 → Fin 4 → ℝ) e a b := by
  fin_cases e <;> fin_cases a <;> fin_cases b <;> simp [ωU, η, eps4_eq, lcZ]

/-- the spatial embedding of a `3 × 3` matrix as a 4-tensor with vanishing `0`-row/column. -/
def emb (E : Matrix (Fin 3) (Fin 3) ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![0, 0, 0, 0], ![0, E 0 0, E 0 1, E 0 2], ![0, E 1 0, E 1 1, E 1 2], ![0, E 2 0, E 2 1, E 2 2]]

/-- `C_{0a0b}` for `C = T E B H D` is the embedded `E`. -/
theorem T_0a0b (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    (fun a b => T E B H D 0 a 0 b) = emb E := by
  funext a b; fin_cases a <;> fin_cases b <;> simp [T, ofMat_apply, sgn, pidx, emb]

/-- `n_{[c} B_{d]e} ω^e{}_{ab}`. -/
def nBω (B : Fin 4 → Fin 4 → ℝ) (c d a b : Fin 4) : ℝ :=
  ∑ e, (nL c * B d e - nL d * B c e) / 2 * ωU e a b

/-- right-hand side of (3.2):
`2 [l_{a[c} E_{d]b} - l_{b[c} E_{d]a} - n_{[c} B_{d]e} ω^e{}_{ab} - n_{[a} B_{b]e} ω^e{}_{cd}]`. -/
def recon (E B : Fin 4 → Fin 4 → ℝ) : T4 (Fin 4) := fun a b c d =>
  2 * ((lmet a c * E d b - lmet a d * E c b) / 2 - (lmet b c * E d a - lmet b d * E c a) / 2
    - nBω B c d a b - nBω B a b c d)

/-- `n_{[c} B_{d]e} ω^e{}_{ab}` is skew in `(c, d)`. -/
theorem nBω_swap_left (B : Fin 4 → Fin 4 → ℝ) (c d a b : Fin 4) :
    nBω B d c a b = -nBω B c d a b := by
  rw [nBω, nBω, ← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun e _ => by ring

/-- `n_{[c} B_{d]e} ω^e{}_{ab}` is skew in `(a, b)`. -/
theorem nBω_swap_right (B : Fin 4 → Fin 4 → ℝ) (c d a b : Fin 4) :
    nBω B c d b a = -nBω B c d a b := by
  rw [nBω, nBω, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun e _ => by rw [ωU, ωU, eps4_swap23]; ring

/-- the right-hand side of (3.2) is a double 2-form. -/
theorem pairSkew_recon (E B : Fin 4 → Fin 4 → ℝ) : PairSkew (recon E B) := by
  intro a b c d
  simp only [recon, nBω_swap_left B b a, nBω_swap_right B _ _ b a, nBω_swap_left B d c,
    nBω_swap_right B _ _ d c]
  constructor <;> ring

private theorem recon_inl_inl {E B : Matrix (Fin 3) (Fin 3) ℝ} (hE : Eᵀ = E)
    (hB : Bᵀ = B) (i j : Fin 3) :
    toMat (recon (emb E) (emb B)) (.inl i) (.inl j) = E i j := by
  have hE' := fun i j => congrFun (congrFun hE i) j
  have hB' := fun i j => congrFun (congrFun hB i) j
  simp only [transpose_apply] at hE' hB'
  fin_cases i <;> fin_cases j <;>
    simp [toMat, recon, nBω, p, q, ωU_eq, emb, Fin.sum_univ_four, lmet, gη, nL, η] <;>
    linarith [hE' 0 1, hE' 0 2, hE' 1 2, hB' 0 1, hB' 0 2, hB' 1 2]

private theorem recon_inl_inr {E B : Matrix (Fin 3) (Fin 3) ℝ} (hE : Eᵀ = E)
    (hB : Bᵀ = B) (i j : Fin 3) :
    toMat (recon (emb E) (emb B)) (.inl i) (.inr j) = B i j := by
  have hE' := fun i j => congrFun (congrFun hE i) j
  have hB' := fun i j => congrFun (congrFun hB i) j
  simp only [transpose_apply] at hE' hB'
  fin_cases i <;> fin_cases j <;>
    simp [toMat, recon, nBω, p, q, ωU_eq, emb, Fin.sum_univ_four, lmet, gη, nL, η] <;>
    linarith [hE' 0 1, hE' 0 2, hE' 1 2, hB' 0 1, hB' 0 2, hB' 1 2]

private theorem recon_inr_inl {E B : Matrix (Fin 3) (Fin 3) ℝ} (hE : Eᵀ = E)
    (hB : Bᵀ = B) (i j : Fin 3) :
    toMat (recon (emb E) (emb B)) (.inr i) (.inl j) = B i j := by
  have hE' := fun i j => congrFun (congrFun hE i) j
  have hB' := fun i j => congrFun (congrFun hB i) j
  simp only [transpose_apply] at hE' hB'
  fin_cases i <;> fin_cases j <;>
    simp [toMat, recon, nBω, p, q, ωU_eq, emb, Fin.sum_univ_four, lmet, gη, nL, η] <;>
    linarith [hE' 0 1, hE' 0 2, hE' 1 2, hB' 0 1, hB' 0 2, hB' 1 2]

private theorem recon_inr_inr {E B : Matrix (Fin 3) (Fin 3) ℝ} (hE : Eᵀ = E)
    (hB : Bᵀ = B) (htrE : trace E = 0) (i j : Fin 3) :
    toMat (recon (emb E) (emb B)) (.inr i) (.inr j) = (-E) i j := by
  have hE' := fun i j => congrFun (congrFun hE i) j
  have hB' := fun i j => congrFun (congrFun hB i) j
  simp only [transpose_apply] at hE' hB'
  simp only [trace, Fin.sum_univ_three, diag] at htrE
  fin_cases i <;> fin_cases j <;>
    simp [toMat, recon, nBω, p, q, ωU_eq, emb, Fin.sum_univ_four, lmet, gη, nL, η] <;>
    linarith [hE' 0 1, hE' 0 2, hE' 1 2, hB' 0 1, hB' 0 2, hB' 1 2]

/-- **Thesis eq. (3.2)** (Bel reconstruction), in the frame `n = ∂_t`: an algebraic Weyl tensor
is recovered from its electric and magnetic parts `E_{ab} = W_{0a0b}`, `B_{ab} = W*_{0a0b}`.

Thesis gap: "a straightforward calculation" in the thesis; here it is checked on the 36
bivector components. The sign of the `B`-terms requires the spatial volume form
`ω_{bcd} = ω_{abcd} n^a` (as stated after (3.2)); the `n^d` convention used in the proof of
Prop 3.1 has the opposite sign. -/
theorem weyl_reconstruct {W : T4 (Fin 4)} (hW : IsWeylLike W) :
    W = recon (fun a b => W 0 a 0 b) (fun a b => rdual W 0 a 0 b) := by
  obtain ⟨E, B, hE, htrE, hB, -, rfl⟩ := (weyl_iff W).1 hW
  rw [rdual_T, T_0a0b, T_0a0b, eq_ofMat_toMat (pairSkew_recon _ _), T]
  congr 1
  ext I J
  rcases I with i | i <;> rcases J with j | j
  · exact (recon_inl_inl hE hB i j).symm
  · exact (recon_inl_inr hE hB i j).symm
  · exact (recon_inr_inl hE hB i j).symm
  · exact (recon_inr_inr hE hB htrE i j).symm

/-! ### `** = -1` on 2-forms -/

/-- Hodge star of a 2-form in Minkowski space, `(*w)_{cd} = ½ w_{ef} ω^{ef}{}_{cd}`. -/
def hodge2 (w : Fin 4 → Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun c d => (1 / 2) * ∑ e, ∑ f, w e f * η e * η f * eps4 e f c d

/-- right dual of a product `u_{ab} w_{cd}`. -/
theorem rdual_prod (u w : Fin 4 → Fin 4 → ℝ) :
    rdual (fun a b c d => u a b * w c d) = fun a b c d => u a b * hodge2 w c d := by
  funext a b c d
  simp only [rdual, hodge2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  ring

/-- Thesis §3.1, `** = (-1)^{kl+t}` for `k = l = 2`, `t = 1`: `** = -1` on 2-forms in
signature `(-+++)`. -/
theorem hodge2_hodge2 (w : Fin 4 → Fin 4 → ℝ) (hw : ∀ a b, w a b = -w b a) :
    hodge2 (hodge2 w) = -w := by
  have hβ : ∀ a b, β (.inl 0) a b = -β (.inl 0) b a := fun a b => by
    rw [β_eq, β_eq, pidx_swap, sgn_swap b a]; split_ifs <;> simp
  have hS : PairSkew (fun a b c d => β (.inl 0) a b * w c d) := fun a b c d =>
    ⟨by dsimp only; rw [hβ a b]; ring, by dsimp only; rw [hw c d]; ring⟩
  have h := congrFun (congrFun (rdual_rdual hS) 0) 1
  rw [rdual_prod, rdual_prod] at h
  have h01 : β (.inl 0) 0 1 = 1 := by simp [β, p, q]
  funext c d
  have := congrFun (congrFun h c) d
  simp only [h01, one_mul, Pi.neg_apply] at this
  simpa using this

/-! ### The space of algebraic Weyl tensors has dimension 10 -/

/-- symmetric trace-free `3 × 3` matrices. -/
def STF : Submodule ℝ (Matrix (Fin 3) (Fin 3) ℝ) where
  carrier := {E | Eᵀ = E ∧ trace E = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro E E' ⟨h1, h2⟩ ⟨h1', h2'⟩
    exact ⟨by rw [transpose_add, h1, h1'], by rw [trace_add, h2, h2', add_zero]⟩
  smul_mem' := by
    rintro c E ⟨h1, h2⟩
    exact ⟨by rw [transpose_smul, h1], by rw [trace_smul, h2, smul_zero]⟩

/-- coordinates `(E₀₀, E₁₁, E₀₁, E₀₂, E₁₂)` on `STF`. -/
def stfEquiv : STF ≃ₗ[ℝ] (Fin 5 → ℝ) where
  toFun E := ![E.1 0 0, E.1 1 1, E.1 0 1, E.1 0 2, E.1 1 2]
  invFun x := ⟨!![x 0, x 2, x 3; x 2, x 1, x 4; x 3, x 4, -x 0 - x 1], by
    refine ⟨?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> rfl
    · simp [trace, Fin.sum_univ_three]⟩
  map_add' E E' := by funext k; fin_cases k <;> rfl
  map_smul' c E := by funext k; fin_cases k <;> rfl
  left_inv := by
    rintro ⟨E, h1, h2⟩
    have hE := fun i j => congrFun (congrFun h1 i) j
    simp only [transpose_apply] at hE
    simp only [trace, Fin.sum_univ_three, diag] at h2
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> linarith [hE 0 1, hE 0 2, hE 1 2]
  right_inv x := by funext k; fin_cases k <;> rfl

/-- `dim STF = 5`. -/
theorem finrank_STF : Module.finrank ℝ STF = 5 := by
  rw [stfEquiv.finrank_eq, Module.finrank_fin_fun]

/-- algebraic Weyl tensors (Minkowski frame) as a subspace. -/
def weylSpace : Submodule ℝ (T4 (Fin 4)) where
  carrier := {C | IsWeylLike C}
  zero_mem' := ⟨fun _ _ _ _ => by simp, fun _ _ _ _ => by simp, fun _ _ => by simp [mtr]⟩
  add_mem' := by
    rintro C C' ⟨hS, hB, hT⟩ ⟨hS', hB', hT'⟩
    refine ⟨fun a b c d => ?_, fun a b c d => ?_, fun b c => ?_⟩
    · obtain ⟨h1, h2⟩ := hS a b c d; obtain ⟨h1', h2'⟩ := hS' a b c d
      simp only [Pi.add_apply]; constructor <;> linarith
    · have := hB a b c d; have := hB' a b c d; simp only [Pi.add_apply]; linarith
    · have := hT b c; have := hT' b c
      simp only [mtr, Pi.add_apply, mul_add, Finset.sum_add_distrib] at *; linarith
  smul_mem' := by
    rintro r C ⟨hS, hB, hT⟩
    refine ⟨fun a b c d => ?_, fun a b c d => ?_, fun b c => ?_⟩
    · obtain ⟨h1, h2⟩ := hS a b c d
      simp only [Pi.smul_apply, smul_eq_mul]
      constructor
      · rw [h1]; ring
      · rw [h2]; ring
    · have := hB a b c d; simp only [Pi.smul_apply, smul_eq_mul]
      linear_combination r * this
    · have := hT b c
      simp only [mtr, Pi.smul_apply, smul_eq_mul] at *
      calc ∑ a, η a * (r * C a b a c) = r * ∑ a, η a * C a b a c := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
        _ = 0 := by rw [this, mul_zero]

/-- the `E`-block of a Weyl tensor is symmetric trace-free. -/
theorem blkE_mem_STF {C : T4 (Fin 4)} (hC : IsWeylLike C) : blkE C ∈ STF := by
  obtain ⟨E, B, hE, htrE, -, -, rfl⟩ := (weyl_iff C).1 hC
  rw [blkE_T]; exact ⟨hE, htrE⟩

/-- the `B`-block of a Weyl tensor is symmetric trace-free. -/
theorem blkB_mem_STF {C : T4 (Fin 4)} (hC : IsWeylLike C) : blkB C ∈ STF := by
  obtain ⟨E, B, -, -, hB, htrB, rfl⟩ := (weyl_iff C).1 hC
  rw [blkB_T]; exact ⟨hB, htrB⟩

/-- membership in `STF`. -/
theorem mem_STF {E : Matrix (Fin 3) (Fin 3) ℝ} : E ∈ STF ↔ Eᵀ = E ∧ trace E = 0 := Iff.rfl

/-- `[[E, B], [B, -E]]` with `E, B ∈ STF` is a Weyl tensor. -/
theorem T_mem_weylSpace {E B : Matrix (Fin 3) (Fin 3) ℝ} (hE : E ∈ STF) (hB : B ∈ STF) :
    T E B B (-E) ∈ weylSpace :=
  (weyl_iff _).2 ⟨E, B, (mem_STF.1 hE).1, (mem_STF.1 hE).2, (mem_STF.1 hB).1,
    (mem_STF.1 hB).2, rfl⟩

/-- `blkE` is additive. -/
theorem blkE_add (C C' : T4 (Fin 4)) : blkE (C + C') = blkE C + blkE C' := by ext i j; rfl
/-- `blkB` is additive. -/
theorem blkB_add (C C' : T4 (Fin 4)) : blkB (C + C') = blkB C + blkB C' := by ext i j; rfl
/-- `blkE` is homogeneous. -/
theorem blkE_smul (r : ℝ) (C : T4 (Fin 4)) : blkE (r • C) = r • blkE C := by ext i j; rfl
/-- `blkB` is homogeneous. -/
theorem blkB_smul (r : ℝ) (C : T4 (Fin 4)) : blkB (r • C) = r • blkB C := by ext i j; rfl

/-- Weyl tensors are parametrised linearly by their electric and magnetic blocks. -/
def weylEquiv : weylSpace ≃ₗ[ℝ] STF × STF where
  toFun C := (⟨blkE C, blkE_mem_STF C.2⟩, ⟨blkB C, blkB_mem_STF C.2⟩)
  invFun EB := ⟨T EB.1.1 EB.2.1 EB.2.1 (-EB.1.1), T_mem_weylSpace EB.1.2 EB.2.2⟩
  map_add' C C' := Prod.ext (Subtype.ext (blkE_add _ _)) (Subtype.ext (blkB_add _ _))
  map_smul' r C := Prod.ext (Subtype.ext (blkE_smul _ _)) (Subtype.ext (blkB_smul _ _))
  left_inv := by
    rintro ⟨C, hC⟩
    obtain ⟨E, B, -, -, -, -, rfl⟩ := (weyl_iff C).1 hC
    simp
  right_inv := by rintro ⟨E, B⟩; simp

/-- Thesis §3.2: in 4 dimensions the Weyl tensor has `n(n+1)(n+2)(n-3)/12 = 10` independent
components (here: the space of algebraic Weyl tensors w.r.t. `η` has dimension 10).

Thesis gap: stated without proof ("it can be shown"); proved here for `n = 4` via the block
form `[[E, B], [B, -E]]` with `E, B` symmetric trace-free (5 + 5). -/
theorem finrank_weylSpace : Module.finrank ℝ weylSpace = 10 := by
  rw [LinearEquiv.finrank_eq weylEquiv, Module.finrank_prod, finrank_STF]

end Bivector
end Feec
