module

public import Feec.Geometry.Hodge2

/-!
# Algebraic Weyl tensors: block form, electric and magnetic parts, reconstruction

In a four-dimensional Minkowski orthonormal frame.

## Main definitions

* `DoubleForm.IsWeyl C`: pair skew, first Bianchi, `η`-trace-free.
* `DoubleForm.elec n C = (n^c n^d C_cadb)_ab` (electric part relative to `n`); the magnetic part
  is `elec n (rdual C)`.
* `DoubleForm.STF` (symmetric trace-free `3 × 3`), `DoubleForm.weylSpace`.

## Main results

* `weyl_iff` (Prop 3.3, corollary): Weyl ⇔ block matrix `[[E, B], [B, -E]]` with `E, B`
  symmetric trace-free; `ldual_eq_rdual`: `*W = W*`; `IsWeyl.rdual`.
* `electric_magnetic_props` (**Prop 3.1**): the electric and magnetic parts are symmetric,
  trace-free and orthogonal to `n`, for every `n`.
* `weyl_reconstruct`, `weyl_reconstruct_unit` (**(3.2)**): `W` is recovered from `E, B` for every
  unit timelike `n` (via the homogenised identity `recon_hom`).
* `finrank_weylSpace`: algebraic Weyl tensors in four dimensions form a 10-dimensional space.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §3.2–3.3 (Props 3.1, 3.3, (3.2))
* [L. Bel, *Définition d'une densité d'énergie et d'un état de radiation totale généralisée*][Bel1958]
* [M. Alcubierre, *Introduction to 3+1 Numerical Relativity*][Alcubierre2008]
* [H. Friedrich, *Hyperbolic reductions for Einstein's equations*][Friedrich1996]
* [A. Anderson, Y. Choquet-Bruhat, J. W. York, Jr., *Einstein–Bianchi hyperbolic system for general relativity*][ACBY1997]
* [R. M. Wald, *General Relativity*][Wald1984]
-/

@[expose] public section

open Matrix Equiv Feec.CurvatureTensor

noncomputable section

namespace Feec.DoubleForm

/-! ### Algebraic Weyl tensors: the block form -/

/-- An algebraic Weyl tensor in a Minkowski orthonormal frame: skew in each pair, first
Bianchi identity, and `η`-trace-free. See [QuennevilleBelair2015], §3.2; cf. [Wald1984]. -/
structure IsWeyl (C : Tensor4) : Prop where
  pairSkew : PairSkew C
  bianchi : Bianchi1 C
  traceFree : ∀ b c, mtr C b c = 0

/-- **Thesis Prop 3.3, corollary.** `C` is an algebraic Weyl tensor iff its bivector matrix is
`[[E, B], [B, -E]]` with `E, B` symmetric and trace-free.

Thesis gap: `tr B = 0` needs Prop 3.3(ii) together with `H = Bᵀ = B`; the thesis does not say
so. Correction: the thesis introduces this matrix form with "Proposition 3.2 thus leads to";
it follows from Prop 3.3. See [QuennevilleBelair2015], Prop 3.3 and the display after it;
cf. [ACBY1997] for the nonlinear case. -/
theorem weyl_iff (C : Tensor4) :
    IsWeyl C ↔ ∃ E B : Matrix (Fin 3) (Fin 3) ℝ, Eᵀ = E ∧ trace E = 0 ∧ Bᵀ = B ∧
      trace B = 0 ∧ C = ofBlocks E B B (-E) := by
  constructor
  · rintro ⟨hS, hB, hT⟩
    have hC := eq_ofBlocks_blocks hS
    rw [hC] at hB hT
    obtain ⟨⟨hE, -, hH⟩, htr⟩ := (bianchi_ofBlocks_iff _ _ _ _).1 hB
    obtain ⟨htrE, hBs, -, hD⟩ := (tracefree_iff _ _ _ _).1 hT
    have hHB : blkH C = blkB C := by rw [hH, hBs]
    refine ⟨blkE C, blkB C, hE, htrE, hBs, ?_, ?_⟩
    · rw [hHB] at htr; linarith
    · rw [hC, hHB, hD, hE]; simp
  · rintro ⟨E, B, hE, htrE, hB, htrB, rfl⟩
    refine ⟨pairSkew_ofMat _, (bianchi_ofBlocks_iff _ _ _ _).2 ⟨⟨hE, ?_, hB.symm⟩, ?_⟩,
      (tracefree_iff _ _ _ _).2 ⟨htrE, hB, hB, by rw [hE]⟩⟩
    · rw [transpose_neg, hE]
    · rw [htrB]; ring

/-- **Thesis §3.2 (omitted classical fact).** For an algebraic Weyl tensor the left and right
duals coincide, `*W = W*`; both have block matrix `[[B, -E], [-E, -B]]`.
See [QuennevilleBelair2015], §3.2. -/
theorem ldual_eq_rdual {W : Tensor4} (hW : IsWeyl W) : ldual W = rdual W := by
  obtain ⟨E, B, -, -, -, -, rfl⟩ := (weyl_iff W).1 hW
  rw [ldual_ofBlocks, rdual_ofBlocks]

/-- The right dual of an algebraic Weyl tensor is again one (`E ↦ B`, `B ↦ -E`). -/
theorem IsWeyl.rdual {W : Tensor4} (hW : IsWeyl W) : IsWeyl (rdual W) := by
  obtain ⟨E, B, hE, htrE, hB, htrB, rfl⟩ := (weyl_iff W).1 hW
  rw [rdual_ofBlocks, weyl_iff]
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
theorem electric_props {W : Tensor4} (hW : IsWeyl W) (n : Fin 4 → ℝ) :
    let E : Fin 4 → Fin 4 → ℝ := fun a b => ∑ c, ∑ d, n c * n d * W c a d b
    (∀ a b, E a b = E b a) ∧ ∑ a, Metric.minkowski4 ℝ a * E a a = 0 ∧
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
  · calc ∑ a, Metric.minkowski4 ℝ a * E a a = ∑ a, ∑ c, ∑ d, n c * n d * (Metric.minkowski4 ℝ a * W a c a d) := by
          simp only [E, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
            Finset.sum_congr rfl fun d _ => ?_
          rw [s1 c a d a, s2 a c d a]; ring
      _ = ∑ c, ∑ d, ∑ a, n c * n d * (Metric.minkowski4 ℝ a * W a c a d) := (sum3_rot _).trans (sum3_rot _)
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
(Prop 3.3): `W*` is again an algebraic Weyl tensor (`IsWeyl.rdual`, using `*W = W*`), so `B`
is the electric part of `W*` and inherits its properties. Stated in a Minkowski orthonormal
frame; `n` need not be unit timelike for these algebraic conclusions.

See [QuennevilleBelair2015], Prop 3.1; the decomposition is due to [Bel1958]; cf.
[Alcubierre2008] and [Friedrich1996]. -/
theorem electric_magnetic_props {W : Tensor4} (hW : IsWeyl W) (n : Fin 4 → ℝ) :
    let E : Fin 4 → Fin 4 → ℝ := fun a b => ∑ c, ∑ d, n c * n d * W c a d b
    let B : Fin 4 → Fin 4 → ℝ := fun a b => ∑ c, ∑ d, n c * n d * rdual W c a d b
    ((∀ a b, E a b = E b a) ∧ ∑ a, Metric.minkowski4 ℝ a * E a a = 0 ∧
      (∀ b, ∑ a, n a * E a b = 0) ∧ ∀ a, ∑ b, E a b * n b = 0) ∧
    ((∀ a b, B a b = B b a) ∧ ∑ a, Metric.minkowski4 ℝ a * B a a = 0 ∧
      (∀ b, ∑ a, n a * B a b = 0) ∧ ∀ a, ∑ b, B a b * n b = 0) :=
  ⟨electric_props hW n, electric_props hW.rdual n⟩

/-! ### The reconstruction formula (3.2) -/

/-- `ε_{abdc} = -ε_{abcd}`. -/
theorem leviCivita4_swap34 (a b c d : Fin 4) : leviCivita4 ℝ a b d c = -leviCivita4 ℝ a b c d := by
  rw [leviCivita4_eq_int, leviCivita4_eq_int, ← Int.cast_neg]; congr 1; revert a b c d; decide

/-- the frame metric `g_{ab} = η_{ab}`. -/
def gη (a b : Fin 4) : ℝ := if a = b then Metric.minkowski4 ℝ a else 0

/-- `n_a` for `n = ∂_t`. -/
def nL : Fin 4 → ℝ := ![-1, 0, 0, 0]

/-- `l_{ab} = g_{ab} + 2 n_a n_b`. -/
def lmet (a b : Fin 4) : ℝ := gη a b + 2 * nL a * nL b

/-- `ω^e{}_{ab}` for the spatial volume form `ω_{bcd} = ω_{abcd} n^a`, `n = ∂_t`. -/
def ωU (e a b : Fin 4) : ℝ := Metric.minkowski4 ℝ e * leviCivita4 ℝ 0 e a b

/-- explicit table of `ω^e{}_{ab}`. -/
theorem ωU_eq (e a b : Fin 4) : ωU e a b = (
    ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, -1, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, 0, 0], ![0, 1, 0, 0]],
    ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, -1, 0, 0], ![0, 0, 0, 0]]]
      : Fin 4 → Fin 4 → Fin 4 → ℝ) e a b := by
  fin_cases e <;> fin_cases a <;> fin_cases b <;> simp [ωU, Metric.minkowski4, leviCivita4_eq_int, leviCivita4Int]

/-- the spatial embedding of a `3 × 3` matrix as a 4-tensor with vanishing `0`-row/column. -/
def emb (E : Matrix (Fin 3) (Fin 3) ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![0, 0, 0, 0], ![0, E 0 0, E 0 1, E 0 2], ![0, E 1 0, E 1 1, E 1 2], ![0, E 2 0, E 2 1, E 2 2]]

/-- `C_{0a0b}` for `C = ofBlocks E B H D` is the embedded `E`. -/
theorem ofBlocks_0a0b (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    (fun a b => ofBlocks E B H D 0 a 0 b) = emb E := by
  funext a b; fin_cases a <;> fin_cases b <;> simp [ofBlocks, ofMat_apply, sgn, pidx, emb]

/-- `n_{[c} B_{d]e} ω^e{}_{ab}`. -/
def nBω (B : Fin 4 → Fin 4 → ℝ) (c d a b : Fin 4) : ℝ :=
  ∑ e, (nL c * B d e - nL d * B c e) / 2 * ωU e a b

/-- right-hand side of (3.2):
`2 [l_{a[c} E_{d]b} - l_{b[c} E_{d]a} - n_{[c} B_{d]e} ω^e{}_{ab} - n_{[a} B_{b]e} ω^e{}_{cd}]`. -/
def recon (E B : Fin 4 → Fin 4 → ℝ) : Tensor4 := fun a b c d =>
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
  exact Finset.sum_congr rfl fun e _ => by rw [ωU, ωU, leviCivita4_swap34]; ring

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
    simp [toMat, recon, nBω, p, q, ωU_eq, emb, Fin.sum_univ_four, lmet, gη, nL, Metric.minkowski4] <;>
    linarith [hE' 0 1, hE' 0 2, hE' 1 2, hB' 0 1, hB' 0 2, hB' 1 2]

private theorem recon_inl_inr {E B : Matrix (Fin 3) (Fin 3) ℝ} (hE : Eᵀ = E)
    (hB : Bᵀ = B) (i j : Fin 3) :
    toMat (recon (emb E) (emb B)) (.inl i) (.inr j) = B i j := by
  have hE' := fun i j => congrFun (congrFun hE i) j
  have hB' := fun i j => congrFun (congrFun hB i) j
  simp only [transpose_apply] at hE' hB'
  fin_cases i <;> fin_cases j <;>
    simp [toMat, recon, nBω, p, q, ωU_eq, emb, Fin.sum_univ_four, lmet, gη, nL, Metric.minkowski4] <;>
    linarith [hE' 0 1, hE' 0 2, hE' 1 2, hB' 0 1, hB' 0 2, hB' 1 2]

private theorem recon_inr_inl {E B : Matrix (Fin 3) (Fin 3) ℝ} (hE : Eᵀ = E)
    (hB : Bᵀ = B) (i j : Fin 3) :
    toMat (recon (emb E) (emb B)) (.inr i) (.inl j) = B i j := by
  have hE' := fun i j => congrFun (congrFun hE i) j
  have hB' := fun i j => congrFun (congrFun hB i) j
  simp only [transpose_apply] at hE' hB'
  fin_cases i <;> fin_cases j <;>
    simp [toMat, recon, nBω, p, q, ωU_eq, emb, Fin.sum_univ_four, lmet, gη, nL, Metric.minkowski4] <;>
    linarith [hE' 0 1, hE' 0 2, hE' 1 2, hB' 0 1, hB' 0 2, hB' 1 2]

private theorem recon_inr_inr {E B : Matrix (Fin 3) (Fin 3) ℝ} (hE : Eᵀ = E)
    (hB : Bᵀ = B) (htrE : trace E = 0) (i j : Fin 3) :
    toMat (recon (emb E) (emb B)) (.inr i) (.inr j) = (-E) i j := by
  have hE' := fun i j => congrFun (congrFun hE i) j
  have hB' := fun i j => congrFun (congrFun hB i) j
  simp only [transpose_apply] at hE' hB'
  simp only [trace, Fin.sum_univ_three, diag] at htrE
  fin_cases i <;> fin_cases j <;>
    simp [toMat, recon, nBω, p, q, ωU_eq, emb, Fin.sum_univ_four, lmet, gη, nL, Metric.minkowski4] <;>
    linarith [hE' 0 1, hE' 0 2, hE' 1 2, hB' 0 1, hB' 0 2, hB' 1 2]

/-- **Thesis eq. (3.2), special case `n = ∂_t`** (Bel reconstruction): an algebraic Weyl tensor
is recovered from its electric and magnetic parts `E_{ab} = W_{0a0b}`, `B_{ab} = W*_{0a0b}`.

Thesis gap: "a straightforward calculation" in the thesis; here it is checked on the 36
bivector components. The sign of the `B`-terms requires the spatial volume form
`ω_{bcd} = ω_{abcd} n^a` (as stated after (3.2)); the `n^d` convention used in the proof of
Prop 3.1 has the opposite sign. The general unit timelike `n` is `weyl_reconstruct_unit`.
See [QuennevilleBelair2015], eq. (3.2); cf. [Bel1958]. -/
theorem weyl_reconstruct {W : Tensor4} (hW : IsWeyl W) :
    W = recon (fun a b => W 0 a 0 b) (fun a b => rdual W 0 a 0 b) := by
  obtain ⟨E, B, hE, htrE, hB, -, rfl⟩ := (weyl_iff W).1 hW
  rw [rdual_ofBlocks, ofBlocks_0a0b, ofBlocks_0a0b, eq_ofMat_toMat (pairSkew_recon _ _), ofBlocks]
  congr 1
  ext I J
  rcases I with i | i <;> rcases J with j | j
  · exact (recon_inl_inl hE hB i j).symm
  · exact (recon_inl_inr hE hB i j).symm
  · exact (recon_inr_inl hE hB i j).symm
  · exact (recon_inr_inr hE hB htrE i j).symm

/-! ### (3.2) for a general unit timelike `n` -/
/-- index lowering `n_a = η_{ab} n^b`. -/
def lowr (n : Fin 4 → ℝ) (a : Fin 4) : ℝ := Metric.minkowski4 ℝ a * n a

/-- `η(n, n) = n_a n^a`. -/
def nsq (n : Fin 4 → ℝ) : ℝ := ∑ a, Metric.minkowski4 ℝ a * n a ^ 2

/-- the electric part `X_{ab} = n^c n^d C_{cadb}` of a (0,4)-tensor relative to `n`. -/
def elec (n : Fin 4 → ℝ) (C : Tensor4) (a b : Fin 4) : ℝ :=
  ∑ c, ∑ d, n c * n d * C c a d b

/-- `ω^e{}_{ab}` for the spatial volume form `ω_{bcd} = ω_{abcd} n^a`. -/
def ωUn (n : Fin 4 → ℝ) (e a b : Fin 4) : ℝ := Metric.minkowski4 ℝ e * ∑ f, n f * leviCivita4 ℝ f e a b

/-- `n_{[c} B_{d]e} ω^e{}_{ab}` for a general `n`. -/
def nBωn (n : Fin 4 → ℝ) (B : Fin 4 → Fin 4 → ℝ) (c d a b : Fin 4) : ℝ :=
  ∑ e, (lowr n c * B d e - lowr n d * B c e) / 2 * ωUn n e a b

/-- the `g`-part of (3.2): `2 [g_{a[c} E_{d]b} - g_{b[c} E_{d]a}]`. -/
def reconG (E : Fin 4 → Fin 4 → ℝ) : Tensor4 := fun a b c d =>
  2 * ((gη a c * E d b - gη a d * E c b) / 2 - (gη b c * E d a - gη b d * E c a) / 2)

/-- the `n`-part of (3.2): `2 [2 n_a n_{[c} E_{d]b} - 2 n_b n_{[c} E_{d]a}`
`- n_{[c} B_{d]e} ω^e{}_{ab} - n_{[a} B_{b]e} ω^e{}_{cd}]`. -/
def reconR (n : Fin 4 → ℝ) (E B : Fin 4 → Fin 4 → ℝ) : Tensor4 := fun a b c d =>
  2 * ((2 * lowr n a * lowr n c * E d b - 2 * lowr n a * lowr n d * E c b) / 2
    - (2 * lowr n b * lowr n c * E d a - 2 * lowr n b * lowr n d * E c a) / 2
    - nBωn n B c d a b - nBωn n B a b c d)

/-- a symmetric trace-free `3 × 3` matrix in five free parameters. -/
def stf (x₁ x₂ x₃ x₄ x₅ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![x₁, x₂, x₃; x₂, x₄, x₅; x₃, x₅, -x₁ - x₄]

/-- explicit table of `n^c n^d C_{cadb}` for `C = [[E, B], [H, D]]`. -/
def elecT (n : Fin 4 → ℝ) (E B H D : Matrix (Fin 3) (Fin 3) ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![
    ![
      E 0 0 * n 1 ^ 2 + E 1 1 * n 2 ^ 2 + E 2 2 * n 3 ^ 2 + E 0 1 * n 1 * n 2
        + E 0 2 * n 1 * n 3 + E 1 0 * n 1 * n 2 + E 1 2 * n 2 * n 3 + E 2 0 * n 1 * n 3
        + E 2 1 * n 2 * n 3,
      B 1 2 * n 2 ^ 2 - B 2 1 * n 3 ^ 2 - B 0 1 * n 1 * n 3 + B 0 2 * n 1 * n 2
        - B 1 1 * n 2 * n 3 + B 2 2 * n 2 * n 3 - E 0 0 * n 0 * n 1 - E 1 0 * n 0 * n 2
        - E 2 0 * n 0 * n 3,
      -B 0 2 * n 1 ^ 2 + B 2 0 * n 3 ^ 2 + B 0 0 * n 1 * n 3 + B 1 0 * n 2 * n 3
        - B 1 2 * n 1 * n 2 - B 2 2 * n 1 * n 3 - E 0 1 * n 0 * n 1 - E 1 1 * n 0 * n 2
        - E 2 1 * n 0 * n 3,
      B 0 1 * n 1 ^ 2 - B 1 0 * n 2 ^ 2 - B 0 0 * n 1 * n 2 + B 1 1 * n 1 * n 2
        - B 2 0 * n 2 * n 3 + B 2 1 * n 1 * n 3 - E 0 2 * n 0 * n 1 - E 1 2 * n 0 * n 2
        - E 2 2 * n 0 * n 3],
    ![
      -H 1 2 * n 3 ^ 2 + H 2 1 * n 2 ^ 2 - E 0 0 * n 0 * n 1 - E 0 1 * n 0 * n 2
        - E 0 2 * n 0 * n 3 - H 1 0 * n 1 * n 3 - H 1 1 * n 2 * n 3 + H 2 0 * n 1 * n 2
        + H 2 2 * n 2 * n 3,
      D 1 1 * n 3 ^ 2 + D 2 2 * n 2 ^ 2 + E 0 0 * n 0 ^ 2 + B 0 1 * n 0 * n 3
        - B 0 2 * n 0 * n 2 - D 1 2 * n 2 * n 3 - D 2 1 * n 2 * n 3 + H 1 0 * n 0 * n 3
        - H 2 0 * n 0 * n 2,
      -D 1 0 * n 3 ^ 2 + E 0 1 * n 0 ^ 2 - B 0 0 * n 0 * n 3 + B 0 2 * n 0 * n 1
        + D 1 2 * n 1 * n 3 + D 2 0 * n 2 * n 3 - D 2 2 * n 1 * n 2 + H 1 1 * n 0 * n 3
        - H 2 1 * n 0 * n 2,
      -D 2 0 * n 2 ^ 2 + E 0 2 * n 0 ^ 2 + B 0 0 * n 0 * n 2 - B 0 1 * n 0 * n 1
        + D 1 0 * n 2 * n 3 - D 1 1 * n 1 * n 3 + D 2 1 * n 1 * n 2 + H 1 2 * n 0 * n 3
        - H 2 2 * n 0 * n 2],
    ![
      H 0 2 * n 3 ^ 2 - H 2 0 * n 1 ^ 2 - E 1 0 * n 0 * n 1 - E 1 1 * n 0 * n 2
        - E 1 2 * n 0 * n 3 + H 0 0 * n 1 * n 3 + H 0 1 * n 2 * n 3 - H 2 1 * n 1 * n 2
        - H 2 2 * n 1 * n 3,
      -D 0 1 * n 3 ^ 2 + E 1 0 * n 0 ^ 2 + B 1 1 * n 0 * n 3 - B 1 2 * n 0 * n 2
        + D 0 2 * n 2 * n 3 + D 2 1 * n 1 * n 3 - D 2 2 * n 1 * n 2 - H 0 0 * n 0 * n 3
        + H 2 0 * n 0 * n 1,
      D 0 0 * n 3 ^ 2 + D 2 2 * n 1 ^ 2 + E 1 1 * n 0 ^ 2 - B 1 0 * n 0 * n 3
        + B 1 2 * n 0 * n 1 - D 0 2 * n 1 * n 3 - D 2 0 * n 1 * n 3 - H 0 1 * n 0 * n 3
        + H 2 1 * n 0 * n 1,
      -D 2 1 * n 1 ^ 2 + E 1 2 * n 0 ^ 2 + B 1 0 * n 0 * n 2 - B 1 1 * n 0 * n 1
        - D 0 0 * n 2 * n 3 + D 0 1 * n 1 * n 3 + D 2 0 * n 1 * n 2 - H 0 2 * n 0 * n 3
        + H 2 2 * n 0 * n 1],
    ![
      -H 0 1 * n 2 ^ 2 + H 1 0 * n 1 ^ 2 - E 2 0 * n 0 * n 1 - E 2 1 * n 0 * n 2
        - E 2 2 * n 0 * n 3 - H 0 0 * n 1 * n 2 - H 0 2 * n 2 * n 3 + H 1 1 * n 1 * n 2
        + H 1 2 * n 1 * n 3,
      -D 0 2 * n 2 ^ 2 + E 2 0 * n 0 ^ 2 + B 2 1 * n 0 * n 3 - B 2 2 * n 0 * n 2
        + D 0 1 * n 2 * n 3 - D 1 1 * n 1 * n 3 + D 1 2 * n 1 * n 2 + H 0 0 * n 0 * n 2
        - H 1 0 * n 0 * n 1,
      -D 1 2 * n 1 ^ 2 + E 2 1 * n 0 ^ 2 - B 2 0 * n 0 * n 3 + B 2 2 * n 0 * n 1
        - D 0 0 * n 2 * n 3 + D 0 2 * n 1 * n 2 + D 1 0 * n 1 * n 3 + H 0 1 * n 0 * n 2
        - H 1 1 * n 0 * n 1,
      D 0 0 * n 2 ^ 2 + D 1 1 * n 1 ^ 2 + E 2 2 * n 0 ^ 2 + B 2 0 * n 0 * n 2
        - B 2 1 * n 0 * n 1 - D 0 1 * n 1 * n 2 - D 1 0 * n 1 * n 2 + H 0 2 * n 0 * n 2
        - H 1 2 * n 0 * n 1]]

/-- `elec` of a block tensor is the explicit table `elecT`. -/
theorem elec_ofBlocks (n : Fin 4 → ℝ) (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    elec n (ofBlocks E B H D) = elecT n E B H D := by
  funext a b
  fin_cases a <;> fin_cases b <;>
  · simp [elec, elecT, Fin.sum_univ_four, ofBlocks, ofMat_apply, sgn, pidx]
    ring

/-- explicit table of `ω^e{}_{ab}`. -/
theorem ωUn_eq (n : Fin 4 → ℝ) (e a b : Fin 4) : ωUn n e a b = (
    ![![![0, 0, 0, 0], ![0, 0, n 3, -n 2], ![0, -n 3, 0, n 1], ![0, n 2, -n 1, 0]],
      ![![0, 0, n 3, -n 2], ![0, 0, 0, 0], ![-n 3, 0, 0, n 0], ![n 2, 0, -n 0, 0]],
      ![![0, -n 3, 0, n 1], ![n 3, 0, 0, -n 0], ![0, 0, 0, 0], ![-n 1, n 0, 0, 0]],
      ![![0, n 2, -n 1, 0], ![-n 2, 0, n 0, 0], ![n 1, -n 0, 0, 0], ![0, 0, 0, 0]]]
      : Fin 4 → Fin 4 → Fin 4 → ℝ) e a b := by
  fin_cases e <;> fin_cases a <;> fin_cases b <;>
    simp [ωUn, Metric.minkowski4, leviCivita4_eq_int, leviCivita4Int, Fin.sum_univ_four]

/-- Homogenised form of (3.2) on the 36 bivector components: for every `n` (no normalisation),
`η(n,n)² W = R_n - η(n,n) G_n`, where `G_n`, `R_n` are the `g`- and `n`-parts of the right-hand
side of (3.2) built from `E_n = elec n W`, `B_n = elec n W*`. Both sides are homogeneous of
degree 4 in `n`, so this is the polynomial identity behind (3.2). -/
theorem recon_hom (e₁ e₂ e₃ e₄ e₅ b₁ b₂ b₃ b₄ b₅ : ℝ) (n : Fin 4 → ℝ) (I J : Ix) :
    let E := stf e₁ e₂ e₃ e₄ e₅
    let B := stf b₁ b₂ b₃ b₄ b₅
    nsq n ^ 2 * toMat (ofBlocks E B B (-E)) I J =
      toMat (reconR n (elec n (ofBlocks E B B (-E))) (elec n (ofBlocks B (-E) (-E) (-B)))) I J
        - nsq n * toMat (reconG (elec n (ofBlocks E B B (-E)))) I J := by
  intro E B
  rw [elec_ofBlocks, elec_ofBlocks, ofBlocks, toMat_ofMat]
  rcases I with i | i <;> rcases J with j | j <;> fin_cases i <;> fin_cases j <;>
  · simp only [toMat, reconR, reconG, nBωn, ωUn_eq, Fin.sum_univ_four, nsq, lowr, gη, p, q,
      of_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
    simp only [E, B, elecT, stf, Metric.minkowski4, Matrix.cons_val, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, Fin.isValue, of_apply, Matrix.neg_apply]
    simp only [Fin.reduceEq, ite_false, ite_true]
    ring


/-- `l_{ab} = g_{ab} + 2 n_a n_b` for a general `n`. -/
def lmetN (n : Fin 4 → ℝ) (a b : Fin 4) : ℝ := gη a b + 2 * lowr n a * lowr n b

/-- right-hand side of (3.2) for a general `n`:
`2 [l_{a[c} E_{d]b} - l_{b[c} E_{d]a} - n_{[c} B_{d]e} ω^e{}_{ab} - n_{[a} B_{b]e} ω^e{}_{cd}]`. -/
def reconN (n : Fin 4 → ℝ) (E B : Fin 4 → Fin 4 → ℝ) : Tensor4 := fun a b c d =>
  2 * ((lmetN n a c * E d b - lmetN n a d * E c b) / 2
    - (lmetN n b c * E d a - lmetN n b d * E c a) / 2 - nBωn n B c d a b - nBωn n B a b c d)

/-- `n_{[c} B_{d]e} ω^e{}_{ab}` is skew in `(c, d)`. -/
theorem nBωn_swap_left (n : Fin 4 → ℝ) (B : Fin 4 → Fin 4 → ℝ) (c d a b : Fin 4) :
    nBωn n B d c a b = -nBωn n B c d a b := by
  rw [nBωn, nBωn, ← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun e _ => by ring

/-- `n_{[c} B_{d]e} ω^e{}_{ab}` is skew in `(a, b)`. -/
theorem nBωn_swap_right (n : Fin 4 → ℝ) (B : Fin 4 → Fin 4 → ℝ) (c d a b : Fin 4) :
    nBωn n B c d b a = -nBωn n B c d a b := by
  rw [nBωn, nBωn, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  have : ωUn n e b a = -ωUn n e a b := by
    unfold ωUn
    rw [← mul_neg, ← Finset.sum_neg_distrib]
    exact congrArg _ (Finset.sum_congr rfl fun f _ => by rw [leviCivita4_swap34]; ring)
  rw [this]; ring

/-- the general-`n` right-hand side of (3.2) is a double 2-form. -/
theorem pairSkew_reconN (n : Fin 4 → ℝ) (E B : Fin 4 → Fin 4 → ℝ) :
    PairSkew (reconN n E B) := by
  intro a b c d
  simp only [reconN, nBωn_swap_left n B b a, nBωn_swap_right n B _ _ b a,
    nBωn_swap_left n B d c, nBωn_swap_right n B _ _ d c]
  constructor <;> ring

/-- a symmetric trace-free `3 × 3` matrix is an `stf`. -/
theorem eq_stf {E : Matrix (Fin 3) (Fin 3) ℝ} (hE : Eᵀ = E) (htr : trace E = 0) :
    E = stf (E 0 0) (E 0 1) (E 0 2) (E 1 1) (E 1 2) := by
  have hE' := fun i j => congrFun (congrFun hE i) j
  simp only [transpose_apply] at hE'
  simp only [trace, Fin.sum_univ_three, diag] at htr
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stf] <;> linarith [hE' 0 1, hE' 0 2, hE' 1 2]

/-- **Thesis eq. (3.2)** (Bel reconstruction) for an arbitrary unit timelike `n`
(`η(n, n) = -1`, either time orientation), in a fixed Minkowski orthonormal frame:
`W_{abcd} = 4 l_{[a[c} E_{d]b]} - 2 n_{[c} B_{d]e} ω^e{}_{ab} - 2 n_{[a} B_{b]e} ω^e{}_{cd}` with
`E_{ab} = n^c n^d W_{cadb}`, `B_{ab} = n^c n^d W*_{cadb}` (the tensors of Prop 3.1),
`l_{ab} = η_{ab} + 2 n_a n_b` and `ω_{bcd} = ω_{abcd} n^a`.

Thesis gap: the thesis states (3.2) for a general `n` as "a straightforward calculation". Here it is
proved without any frame change: `recon_hom` is the homogenised polynomial identity, valid for all
`n`, and `η(n,n) = -1` specialises it. See [QuennevilleBelair2015], eq. (3.2); cf. [Bel1958]. -/
theorem weyl_reconstruct_unit {W : Tensor4} (hW : IsWeyl W) {n : Fin 4 → ℝ}
    (hn : nsq n = -1) : W = reconN n (elec n W) (elec n (rdual W)) := by
  obtain ⟨E, B, hE, htrE, hB, htrB, rfl⟩ := (weyl_iff W).1 hW
  obtain ⟨x₁, x₂, x₃, x₄, x₅, rfl⟩ : ∃ x₁ x₂ x₃ x₄ x₅, E = stf x₁ x₂ x₃ x₄ x₅ :=
    ⟨_, _, _, _, _, eq_stf hE htrE⟩
  obtain ⟨y₁, y₂, y₃, y₄, y₅, rfl⟩ : ∃ y₁ y₂ y₃ y₄ y₅, B = stf y₁ y₂ y₃ y₄ y₅ :=
    ⟨_, _, _, _, _, eq_stf hB htrB⟩
  rw [rdual_ofBlocks]
  refine (eq_ofMat_toMat (pairSkew_ofMat _)).trans ?_
  rw [eq_ofMat_toMat (pairSkew_reconN _ _ _)]
  congr 1
  ext I J
  have h := recon_hom x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ n I J
  simp only [hn] at h
  have hsplit : ∀ X Y : Fin 4 → Fin 4 → ℝ,
      toMat (reconN n X Y) I J = toMat (reconR n X Y) I J + toMat (reconG X) I J := by
    intro X Y; simp only [toMat, of_apply, reconN, reconR, reconG, lmetN]; ring
  rw [hsplit, ← ofBlocks]
  linear_combination h

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
def weylSpace : Submodule ℝ (Tensor4) where
  carrier := {C | IsWeyl C}
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
      calc ∑ a, Metric.minkowski4 ℝ a * (r * C a b a c) = r * ∑ a, Metric.minkowski4 ℝ a * C a b a c := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
        _ = 0 := by rw [this, mul_zero]

/-- the `E`-block of a Weyl tensor is symmetric trace-free. -/
theorem blkE_mem_STF {C : Tensor4} (hC : IsWeyl C) : blkE C ∈ STF := by
  obtain ⟨E, B, hE, htrE, -, -, rfl⟩ := (weyl_iff C).1 hC
  rw [blkE_ofBlocks]; exact ⟨hE, htrE⟩

/-- the `B`-block of a Weyl tensor is symmetric trace-free. -/
theorem blkB_mem_STF {C : Tensor4} (hC : IsWeyl C) : blkB C ∈ STF := by
  obtain ⟨E, B, -, -, hB, htrB, rfl⟩ := (weyl_iff C).1 hC
  rw [blkB_ofBlocks]; exact ⟨hB, htrB⟩

/-- membership in `STF`. -/
theorem mem_STF {E : Matrix (Fin 3) (Fin 3) ℝ} : E ∈ STF ↔ Eᵀ = E ∧ trace E = 0 := Iff.rfl

/-- `[[E, B], [B, -E]]` with `E, B ∈ STF` is a Weyl tensor. -/
theorem ofBlocks_mem_weylSpace {E B : Matrix (Fin 3) (Fin 3) ℝ} (hE : E ∈ STF) (hB : B ∈ STF) :
    ofBlocks E B B (-E) ∈ weylSpace :=
  (weyl_iff _).2 ⟨E, B, (mem_STF.1 hE).1, (mem_STF.1 hE).2, (mem_STF.1 hB).1,
    (mem_STF.1 hB).2, rfl⟩

/-- `blkE` is additive. -/
theorem blkE_add (C C' : Tensor4) : blkE (C + C') = blkE C + blkE C' := by ext i j; rfl
/-- `blkB` is additive. -/
theorem blkB_add (C C' : Tensor4) : blkB (C + C') = blkB C + blkB C' := by ext i j; rfl
/-- `blkE` is homogeneous. -/
theorem blkE_smul (r : ℝ) (C : Tensor4) : blkE (r • C) = r • blkE C := by ext i j; rfl
/-- `blkB` is homogeneous. -/
theorem blkB_smul (r : ℝ) (C : Tensor4) : blkB (r • C) = r • blkB C := by ext i j; rfl

/-- Weyl tensors are parametrised linearly by their electric and magnetic blocks. -/
def weylEquiv : weylSpace ≃ₗ[ℝ] STF × STF where
  toFun C := (⟨blkE C, blkE_mem_STF C.2⟩, ⟨blkB C, blkB_mem_STF C.2⟩)
  invFun EB := ⟨ofBlocks EB.1.1 EB.2.1 EB.2.1 (-EB.1.1), ofBlocks_mem_weylSpace EB.1.2 EB.2.2⟩
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
form `[[E, B], [B, -E]]` with `E, B` symmetric trace-free (5 + 5).
See [QuennevilleBelair2015], §3.2 (which cites [Alcubierre2008], p. 288 and [Friedrich1996] for
the Riemann/Weyl splitting). -/
theorem finrank_weylSpace : Module.finrank ℝ weylSpace = 10 := by
  rw [LinearEquiv.finrank_eq weylEquiv, Module.finrank_prod, finrank_STF]

end Feec.DoubleForm

end
