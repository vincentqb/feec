module

public import Feec.Foundation.Tensor
public import Feec.Geometry.WeylDecomposition
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Ch 3 §3.1–3.3: Hodge duality, the Bel decomposition, and the Weyl block structure (shim)

Strangler shim over `Feec.Geometry.Bivector` (bivector blocks, Prop 3.3),
`Feec.Geometry.Hodge2` (duals, Prop 3.2, `** = -1`) and `Feec.Geometry.WeylDecomposition`
(Weyl tensors, Prop 3.1, (3.2), dimension 10), namespace `Feec.DoubleForm`; the Levi-Civita
symbol is `Feec.leviCivita4` (`Feec.Algebra.LeviCivita`), and the Bianchi characterisation is
`Feec.CurvatureTensor.bianchi_iff` (any commutative ring). Each declaration keeps its old
statement and is proved by the new one.

## References

* [QuennevilleBelair2015], Ch. 3, §§3.1–3.3 (Props 3.1–3.3, eq. (3.2))
* [Bel1958], [Alcubierre2008], [Friedrich1996], [ACBY1997], [Wald1984]
-/

@[expose] public section

open Matrix Equiv

noncomputable section

namespace Feec

/-- Bridge: the determinant definition `eps4` is the Levi-Civita symbol `leviCivita4 ℝ`. -/
theorem eps4_eq_leviCivita4 (a b c d : Fin 4) : eps4 a b c d = leviCivita4 ℝ a b c d := by
  unfold eps4 leviCivita4 leviCivita
  congr 1
  ext r s
  fin_cases r <;> simp [Pi.single_apply, Matrix.one_apply, eq_comm] <;> congr

namespace Bivector

/-- Integer Levi-Civita symbol on `Fin 4` via the Vandermonde product
`∏_{i<j} (x_j - x_i) / 12` (computable, so finite tables are checked by `decide`). -/
abbrev lcZ (a b c d : Fin 4) : ℤ :=
  leviCivita4Int a b c d

/-- The foundation's determinant definition of `eps4` agrees with the closed form `lcZ`. -/
theorem eps4_eq (a b c d : Fin 4) : eps4 a b c d = (lcZ a b c d : ℝ) :=
  by rw [eps4_eq_leviCivita4, leviCivita4_eq_int]

/-- `ε_{abcd} = ε_{cdab}` (swapping two pairs is an even permutation). -/
theorem eps4_swap_pairs (a b c d : Fin 4) : eps4 a b c d = eps4 c d a b :=
  by simp only [eps4_eq_leviCivita4]; exact leviCivita4_swap_pairs a b c d

/-- `ε_{bacd} = -ε_{abcd}`. -/
theorem eps4_swap01 (a b c d : Fin 4) : eps4 b a c d = -eps4 a b c d :=
  by simp only [eps4_eq_leviCivita4]; exact leviCivita4_swap12 a b c d

/-- `ε_{0123} = 1`. -/
theorem eps4_0123 : eps4 0 1 2 3 = 1 :=
  by rw [eps4_eq_leviCivita4, leviCivita4_0123]

/-- index set of the bivector basis `(t∧x, t∧y, t∧z | y∧z, z∧x, x∧y)`. -/
abbrev Ix :=
  DoubleForm.Ix

/-- first leg of the basis bivector `I`. -/
abbrev p : Ix → Fin 4 :=
  DoubleForm.p

/-- second leg of the basis bivector `I`. -/
abbrev q : Ix → Fin 4 :=
  DoubleForm.q

/-- components of the basis bivector `I`: `β I a b = δ_{a p}δ_{b q} - δ_{a q}δ_{b p}`. -/
abbrev β (I : Ix) (a b : Fin 4) : ℝ :=
  DoubleForm.β I a b

/-- the double 2-form with bivector matrix `M`: `C_{abcd} = ∑_{I,J} M_{IJ} β^I_{ab} β^J_{cd}`. -/
abbrev ofMat (M : Matrix Ix Ix ℝ) : T4 (Fin 4) :=
  DoubleForm.ofMat M

/-- the double 2-form whose bivector matrix is `[[E, B], [H, D]]`. -/
abbrev T (E B H D : Matrix (Fin 3) (Fin 3) ℝ) : T4 (Fin 4) :=
  DoubleForm.ofBlocks E B H D

/-- the bivector matrix `M_{IJ} = C(e_I, e_J) = C_{p_I q_I p_J q_J}` of a (0,4)-tensor. -/
abbrev toMat (C : T4 (Fin 4)) : Matrix Ix Ix ℝ :=
  DoubleForm.toMat C

/-- sign of the pair `(a, b)` relative to the basis bivector `pidx a b` (zero on the diagonal). -/
abbrev sgn : Fin 4 → Fin 4 → ℝ :=
  DoubleForm.sgn

/-- the basis bivector carrying the pair `(a, b)`. -/
abbrev pidx : Fin 4 → Fin 4 → Ix :=
  DoubleForm.pidx

/-- the basis bivectors in table form. -/
theorem β_eq (I : Ix) (a b : Fin 4) : β I a b = if I = pidx a b then sgn a b else 0 :=
  DoubleForm.β_eq I a b

/-- components of `ofMat M` are signed entries of `M`. -/
theorem ofMat_apply (M : Matrix Ix Ix ℝ) (a b c d : Fin 4) :
    ofMat M a b c d = sgn a b * sgn c d * M (pidx a b) (pidx c d) :=
  DoubleForm.ofMat_apply M a b c d

/-- `sgn` is skew. -/
theorem sgn_swap (a b : Fin 4) : sgn b a = -sgn a b :=
  DoubleForm.sgn_swap a b

/-- `pidx` is symmetric. -/
theorem pidx_swap (a b : Fin 4) : pidx b a = pidx a b :=
  DoubleForm.pidx_swap a b

/-- the legs `(p I, q I)` carry the bivector `I` with sign `+1`. -/
theorem sgn_pq (I : Ix) : sgn (p I) (q I) = 1 ∧ pidx (p I) (q I) = I :=
  DoubleForm.sgn_pq I

/-- every skew 2-form is the combination of basis bivectors: `w_{ab} = ± w(e_{pidx a b})`. -/
theorem skew2_expand (w : Fin 4 → Fin 4 → ℝ) (hw : ∀ a b, w a b = -w b a) (a b : Fin 4) :
    w a b = sgn a b * w (p (pidx a b)) (q (pidx a b)) :=
  DoubleForm.skew2_expand w hw a b

/-- the bivector matrix of `ofMat M` is `M`. -/
theorem toMat_ofMat (M : Matrix Ix Ix ℝ) : toMat (ofMat M) = M :=
  DoubleForm.toMat_ofMat M

/-- `ofMat` is injective. -/
theorem ofMat_injective : Function.Injective ofMat :=
  DoubleForm.ofMat_injective

/-- every `ofMat M` is a double 2-form. -/
theorem pairSkew_ofMat (M : Matrix Ix Ix ℝ) : PairSkew (ofMat M) :=
  DoubleForm.pairSkew_ofMat M

/-- A double 2-form is determined by its bivector matrix. -/
theorem eq_ofMat_toMat {C : T4 (Fin 4)} (hC : PairSkew C) : C = ofMat (toMat C) :=
  DoubleForm.eq_ofMat_toMat hC

/-- the `E`-block of the bivector matrix (thesis: `[[E, B], [H, D]]`). -/
abbrev blkE (C : T4 (Fin 4)) : Matrix (Fin 3) (Fin 3) ℝ :=
  DoubleForm.blkE C

/-- the `B`-block. -/
abbrev blkB (C : T4 (Fin 4)) : Matrix (Fin 3) (Fin 3) ℝ :=
  DoubleForm.blkB C

/-- the `H`-block. -/
abbrev blkH (C : T4 (Fin 4)) : Matrix (Fin 3) (Fin 3) ℝ :=
  DoubleForm.blkH C

/-- the `D`-block. -/
abbrev blkD (C : T4 (Fin 4)) : Matrix (Fin 3) (Fin 3) ℝ :=
  DoubleForm.blkD C

/-- the `E`-block is literally the thesis' `E_{ab} = C_{0a0b}` (spatial `a, b`). -/
theorem blkE_apply (C : T4 (Fin 4)) (i j : Fin 3) : blkE C i j = C 0 i.succ 0 j.succ :=
  DoubleForm.blkE_apply C i j

/-- a double 2-form is `T` of its four blocks. -/
theorem eq_T_blocks {C : T4 (Fin 4)} (hC : PairSkew C) :
    C = T (blkE C) (blkB C) (blkH C) (blkD C) :=
  DoubleForm.eq_ofBlocks_blocks hC

/-- the `E`-block of `T E B H D`. -/
theorem blkE_T (E B H D : Matrix (Fin 3) (Fin 3) ℝ) : blkE (T E B H D) = E :=
  DoubleForm.blkE_ofBlocks E B H D

/-- the `B`-block of `T E B H D`. -/
theorem blkB_T (E B H D : Matrix (Fin 3) (Fin 3) ℝ) : blkB (T E B H D) = B :=
  DoubleForm.blkB_ofBlocks E B H D

/-- the `H`-block of `T E B H D`. -/
theorem blkH_T (E B H D : Matrix (Fin 3) (Fin 3) ℝ) : blkH (T E B H D) = H :=
  DoubleForm.blkH_ofBlocks E B H D

/-- the `D`-block of `T E B H D`. -/
theorem blkD_T (E B H D : Matrix (Fin 3) (Fin 3) ℝ) : blkD (T E B H D) = D :=
  DoubleForm.blkD_ofBlocks E B H D

/-- `T` commutes with negation. -/
theorem T_neg (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    T (-E) (-B) (-H) (-D) = -T E B H D :=
  DoubleForm.ofBlocks_neg E B H D

/-- `T` is injective. -/
theorem T_inj {E B H D E' B' H' D' : Matrix (Fin 3) (Fin 3) ℝ} :
    T E B H D = T E' B' H' D' ↔ E = E' ∧ B = B' ∧ H = H' ∧ D = D' :=
  DoubleForm.ofBlocks_inj

/-- right dual `C*_{abcd} = ½ C_{abef} ω^{ef}{}_{cd}` (Minkowski frame, `ω = ε`). -/
abbrev rdual (C : T4 (Fin 4)) : T4 (Fin 4) :=
  DoubleForm.rdual C

/-- left dual `*C_{abcd} = ½ ω_{ab}{}^{ef} C_{efcd}`. -/
abbrev ldual (C : T4 (Fin 4)) : T4 (Fin 4) :=
  DoubleForm.ldual C

/-- the pair interchange `C_{abcd} ↦ C_{cdab}`. -/
abbrev swapPairs (C : T4 (Fin 4)) : T4 (Fin 4) :=
  DoubleForm.swapPairs C

/-- the Hodge star on bivectors in the basis `(t∧x, t∧y, t∧z | y∧z, z∧x, x∧y)`. -/
abbrev S : Matrix Ix Ix ℝ :=
  DoubleForm.S

/-- right dualisation multiplies the bivector matrix by the Hodge matrix `S` on the right
(`t∧x ↦ y∧z`, `y∧z ↦ -t∧x`, cyclically, as in the proof of Thesis Prop 3.2). -/
theorem rdual_ofMat (M : Matrix Ix Ix ℝ) : rdual (ofMat M) = ofMat (M * S) :=
  DoubleForm.rdual_ofMat M

/-- pair interchange transposes the bivector matrix. -/
theorem swapPairs_ofMat (M : Matrix Ix Ix ℝ) : swapPairs (ofMat M) = ofMat Mᵀ :=
  DoubleForm.swapPairs_ofMat M

/-- the left dual is the right dual conjugated by the pair interchange. -/
theorem ldual_eq (C : T4 (Fin 4)) : ldual C = swapPairs (rdual (swapPairs C)) :=
  DoubleForm.ldual_eq C

/-- left dualisation multiplies the bivector matrix by `Sᵀ` on the left. -/
theorem ldual_ofMat (M : Matrix Ix Ix ℝ) : ldual (ofMat M) = ofMat (Sᵀ * M) :=
  DoubleForm.ldual_ofMat M

/-- **Thesis Prop 3.2 (right dual).** `C ↦ C*` acts on blocks as `[[E,B],[H,D]] ↦ [[B,-E],[D,-H]]`.
See [QuennevilleBelair2015, Prop 3.2].

Correction: the thesis' formula `C*_{abcd} v^c w^d = C_{abef} (ε^{ef}{}_{cd} v^c w^d)` and
`B_{ab} = C_{0aef} ε^{ef}{}_{0b}` miss the factor `½` (without it `t∧x ↦ 2 y∧z`); `rdual`
includes it. -/
theorem rdual_T (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    rdual (T E B H D) = T B (-E) D (-H) :=
  DoubleForm.rdual_ofBlocks E B H D

/-- **Thesis Prop 3.2 (left dual).** `C ↦ *C` acts as `[[E,B],[H,D]] ↦ [[H,D],[-E,-B]]`.
See [QuennevilleBelair2015, Prop 3.2]. -/
theorem ldual_T (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    ldual (T E B H D) = T H D (-E) (-B) :=
  DoubleForm.ldual_ofBlocks E B H D

/-- **Thesis Prop 3.2 (double dual).** `C ↦ *C*` acts as `[[E,B],[H,D]] ↦ [[D,-H],[-B,E]]`.
See [QuennevilleBelair2015, Prop 3.2]. -/
theorem ldual_rdual_T (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    ldual (rdual (T E B H D)) = T D (-H) (-B) E :=
  DoubleForm.ldual_rdual_ofBlocks E B H D

/-- **Thesis Prop 3.2.** For a double 2-form `C` (skew in each pair) set, as in the thesis,
`E_{ab} = C_{0a0b}`, `B_{ab} = C*_{0a0b}`, `H_{ab} = *C_{0a0b}`, `D_{ab} = *C*_{0a0b}`.
Then `C` has bivector block matrix `[[E,B],[H,D]]`, and the three duals act as stated.
See [QuennevilleBelair2015, Prop 3.2] (block layout following thesis ref. [10], Frauendiener,
not in `references.bib`).

Correction: `B, H, D` carry the factor `½` built into `rdual`/`ldual` (missing in the thesis'
formula for `B_{ab}`). -/
theorem prop_3_2 {C : T4 (Fin 4)} (hC : PairSkew C) :
    let E : Matrix (Fin 3) (Fin 3) ℝ := fun i j => C 0 i.succ 0 j.succ
    let B : Matrix (Fin 3) (Fin 3) ℝ := fun i j => rdual C 0 i.succ 0 j.succ
    let H : Matrix (Fin 3) (Fin 3) ℝ := fun i j => ldual C 0 i.succ 0 j.succ
    let D : Matrix (Fin 3) (Fin 3) ℝ := fun i j => ldual (rdual C) 0 i.succ 0 j.succ
    C = T E B H D ∧ rdual C = T B (-E) D (-H) ∧ ldual C = T H D (-E) (-B) ∧
      ldual (rdual C) = T D (-H) (-B) E :=
  DoubleForm.blocks_eq_and_duals hC

/-- Thesis §3.2: `(W*)* = -W` for every double 2-form (`** = -1` on 2-forms, signature
`(-+++)`). See [QuennevilleBelair2015, §3.2]. -/
theorem rdual_rdual {C : T4 (Fin 4)} (hC : PairSkew C) : rdual (rdual C) = -C :=
  DoubleForm.rdual_rdual hC

/-- `*(*W) = -W` for every double 2-form. -/
theorem ldual_ldual {C : T4 (Fin 4)} (hC : PairSkew C) : ldual (ldual C) = -C :=
  DoubleForm.ldual_ldual hC

/-- left and right duals commute. -/
theorem ldual_rdual_comm {C : T4 (Fin 4)} (hC : PairSkew C) :
    ldual (rdual C) = rdual (ldual C) :=
  DoubleForm.ldual_rdual_comm hC

/-- Thesis §3.2: for `W` with the interchange symmetry, `*W_{abcd} = W*_{cdab}`.
See [QuennevilleBelair2015, §3.2]. -/
theorem ldual_eq_rdual_swap {C : T4 (Fin 4)} (hC : Interchange C) (a b c d : Fin 4) :
    ldual C a b c d = rdual C c d a b :=
  DoubleForm.ldual_eq_rdual_swap hC a b c d

/-- interchange symmetry as a fixed point of `swapPairs`. -/
theorem interchange_iff_swapPairs (C : T4 (Fin 4)) : Interchange C ↔ swapPairs C = C :=
  DoubleForm.interchange_iff_swapPairs C

/-- interchange symmetry is symmetry of the bivector matrix. -/
theorem interchange_ofMat_iff (M : Matrix Ix Ix ℝ) : Interchange (ofMat M) ↔ Mᵀ = M :=
  DoubleForm.interchange_ofMat_iff M

/-- **Thesis Prop 3.3(i).** The interchange symmetry `C_{abcd} = C_{cdab}` is equivalent to
`E, D` symmetric and `H = Bᵀ`. See [QuennevilleBelair2015, Prop 3.3]; cf. [ACBY1997] for the
nonlinear analogue. -/
theorem interchange_iff (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    Interchange (T E B H D) ↔ Eᵀ = E ∧ Dᵀ = D ∧ H = Bᵀ :=
  DoubleForm.interchange_iff E B H D

/-- total antisymmetrisation `C_{[abcd]} = (1/4!) ∑_σ sgn σ C_{σ(abcd)}`. -/
abbrev alt4 (C : T4 (Fin 4)) : T4 (Fin 4) :=
  DoubleForm.altPart C

/-- the 24-term expansion of `C_{[abcd]}`. -/
theorem alt4_expand (C : T4 (Fin 4)) (a b c d : Fin 4) : alt4 C a b c d = (1 / 24) *
    (C a b c d - C a b d c - C a c b d + C a c d b - C a d c b + C a d b c
     - C b a c d + C b a d c + C b c a d - C b c d a + C b d c a - C b d a c
     - C c b a d + C c b d a + C c a b d - C c a d b + C c d a b - C c d b a
     - C d b c a + C d b a c + C d c b a - C d c a b + C d a c b - C d a b c) :=
  DoubleForm.altPart_expand C a b c d

/-- `C_{[abcd]} = ε_{abcd} C_{[0123]}` (in 4 dimensions `Λ⁴` is a line). -/
theorem alt4_eq_eps (C : T4 (Fin 4)) (a b c d : Fin 4) :
    alt4 C a b c d = eps4 a b c d * alt4 C 0 1 2 3 :=
  by rw [eps4_eq_leviCivita4]; exact DoubleForm.altPart_eq_eps C a b c d

/-- For a double 2-form, `C_{[0123]}` has the six-term form of the thesis' proof of Prop 3.3. -/
theorem alt4_0123 {C : T4 (Fin 4)} (hC : PairSkew C) : alt4 C 0 1 2 3 =
    (1 / 6) * (C 0 1 2 3 + C 0 2 3 1 + C 0 3 1 2 + C 2 3 0 1 + C 3 1 0 2 + C 1 2 0 3) :=
  DoubleForm.altPart_0123 hC

/-- **Thesis Prop 3.3(ii).** `C_{[abcd]} = 0` is equivalent to `tr B + tr H = 0`.
See [QuennevilleBelair2015, Prop 3.3]. -/
theorem alt_iff (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    (∀ a b c d, alt4 (T E B H D) a b c d = 0) ↔ trace B + trace H = 0 :=
  DoubleForm.altPart_ofBlocks_iff E B H D

/-- First Bianchi `C_{a[bcd]} = 0` for a double 2-form is equivalent to the interchange symmetry
plus `C_{[abcd]} = 0` (thesis: "the 16 conditions ... break into 15 + 1", cited from [10]).

Thesis gap: the thesis cites this without proof; it is proved here. See
[QuennevilleBelair2015, §2 (after Prop 2.1) and proof of Prop 3.3]; the source cited there is
thesis ref. [10] (Frauendiener), not in `references.bib`. -/
theorem bianchi_iff {C : T4 (Fin 4)} (hC : PairSkew C) :
    Bianchi1 C ↔ Interchange C ∧ ∀ a b c d, alt4 C a b c d = 0 :=
  DoubleForm.bianchi_iff_altPart hC

/-- Thesis Prop 3.3, Bianchi part: for `C = [[E,B],[H,D]]`, first Bianchi holds iff
`E, D` are symmetric, `H = Bᵀ` and `tr B + tr H = 0`. See [QuennevilleBelair2015, Prop 3.3]. -/
theorem bianchi_T_iff (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    Bianchi1 (T E B H D) ↔ (Eᵀ = E ∧ Dᵀ = D ∧ H = Bᵀ) ∧ trace B + trace H = 0 :=
  DoubleForm.bianchi_ofBlocks_iff E B H D

/-- the Minkowski trace `C^a{}_{bac} = ∑_a η^{aa} C_{abac}`. -/
abbrev mtr (C : T4 (Fin 4)) (b c : Fin 4) : ℝ :=
  DoubleForm.mtr C b c

/-- The 16 Minkowski traces of `[[E,B],[H,D]]`.

Correction: the thesis' "6-tuple" step `C^a{}_{iaj} = -C_{0i0j}` drops the spatial terms;
the correct entry is `-E_{ij} - D_{ji} + δ_{ij} tr D`. -/
theorem mtr_T (E B H D : Matrix (Fin 3) (Fin 3) ℝ) (b c : Fin 4) : mtr (T E B H D) b c = ![
    ![trace E, B 1 2 - B 2 1, B 2 0 - B 0 2, B 0 1 - B 1 0],
    ![H 2 1 - H 1 2, -E 0 0 - D 0 0 + trace D, -E 0 1 - D 1 0, -E 0 2 - D 2 0],
    ![H 0 2 - H 2 0, -E 1 0 - D 0 1, -E 1 1 - D 1 1 + trace D, -E 1 2 - D 2 1],
    ![H 1 0 - H 0 1, -E 2 0 - D 0 2, -E 2 1 - D 1 2, -E 2 2 - D 2 2 + trace D]] b c :=
  DoubleForm.mtr_ofBlocks E B H D b c

/-- **Thesis Prop 3.3(iii).** `η`-trace-freeness `C^a{}_{bac} = 0` is equivalent to
`tr E = 0`, `B, H` symmetric and `D = -Eᵀ`.

Thesis gap: the final step `D = -Eᵀ + δ tr E/2` uses `tr E = 0` (from the singleton
condition) and the summed diagonal equations `tr D = tr E / 2`; both are made explicit.
See [QuennevilleBelair2015, Prop 3.3]. -/
theorem tracefree_iff (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    (∀ b c, mtr (T E B H D) b c = 0) ↔ trace E = 0 ∧ Bᵀ = B ∧ Hᵀ = H ∧ D = -Eᵀ :=
  DoubleForm.tracefree_iff E B H D

/-- An algebraic Weyl tensor in a Minkowski orthonormal frame: skew in each pair, first
Bianchi identity, and `η`-trace-free. See [QuennevilleBelair2015, §3.2]; cf. [Wald1984]. -/
abbrev IsWeylLike (C : T4 (Fin 4)) : Prop :=
  DoubleForm.IsWeyl C

/-- **Thesis Prop 3.3, corollary.** `C` is an algebraic Weyl tensor iff its bivector matrix is
`[[E, B], [B, -E]]` with `E, B` symmetric and trace-free.

Thesis gap: `tr B = 0` needs Prop 3.3(ii) together with `H = Bᵀ = B`; the thesis does not say
so. Correction: the thesis introduces this matrix form with "Proposition 3.2 thus leads to";
it follows from Prop 3.3. See [QuennevilleBelair2015, Prop 3.3 and the display after it];
cf. [ACBY1997] for the nonlinear case. -/
theorem weyl_iff (C : T4 (Fin 4)) :
    IsWeylLike C ↔ ∃ E B : Matrix (Fin 3) (Fin 3) ℝ, Eᵀ = E ∧ trace E = 0 ∧ Bᵀ = B ∧
      trace B = 0 ∧ C = T E B B (-E) :=
  DoubleForm.weyl_iff C

/-- **Thesis §3.2 (omitted classical fact).** For an algebraic Weyl tensor the left and right
duals coincide, `*W = W*`; both have block matrix `[[B, -E], [-E, -B]]`.
See [QuennevilleBelair2015, §3.2]. -/
theorem ldual_eq_rdual {W : T4 (Fin 4)} (hW : IsWeylLike W) : ldual W = rdual W :=
  DoubleForm.ldual_eq_rdual hW

/-- The right dual of an algebraic Weyl tensor is again one (`E ↦ B`, `B ↦ -E`). -/
theorem IsWeylLike.rdual {W : T4 (Fin 4)} (hW : IsWeylLike W) : IsWeylLike (rdual W) :=
  DoubleForm.IsWeyl.rdual hW

/-- The electric part `E_{ab} = n^c n^d W_{cadb}` of an algebraic Weyl tensor is symmetric,
`η`-trace-free and orthogonal to `n`, for every vector `n`. -/
theorem electric_props {W : T4 (Fin 4)} (hW : IsWeylLike W) (n : Fin 4 → ℝ) :
    let E : Fin 4 → Fin 4 → ℝ := fun a b => ∑ c, ∑ d, n c * n d * W c a d b
    (∀ a b, E a b = E b a) ∧ ∑ a, η a * E a a = 0 ∧
      (∀ b, ∑ a, n a * E a b = 0) ∧ ∀ a, ∑ b, E a b * n b = 0 :=
  DoubleForm.electric_props hW n

/-- **Thesis Prop 3.1.** For an algebraic Weyl tensor `W` and a vector `n`, the electric and
magnetic tensors `E_{ab} = n^c n^d W_{cadb}`, `B_{ab} = n^c n^d W*_{cadb}` are symmetric,
trace-free and orthogonal to `n`.

Thesis gap: the thesis' proof of the symmetry of `B` uses the 3D contraction
`ω^{baq} ω_{bef} = δ^a_e δ^q_f - δ^a_f δ^q_e`, which only holds with the spatial projector, and
uses orthogonality before proving it. Here the proof instead goes through the block form
(Prop 3.3): `W*` is again an algebraic Weyl tensor (`IsWeylLike.rdual`, using `*W = W*`), so `B`
is the electric part of `W*` and inherits its properties. Stated in a Minkowski orthonormal
frame; `n` need not be unit timelike for these algebraic conclusions.

See [QuennevilleBelair2015, Prop 3.1]; the decomposition is due to [Bel1958]; cf.
[Alcubierre2008] and [Friedrich1996]. -/
theorem prop_3_1 {W : T4 (Fin 4)} (hW : IsWeylLike W) (n : Fin 4 → ℝ) :
    let E : Fin 4 → Fin 4 → ℝ := fun a b => ∑ c, ∑ d, n c * n d * W c a d b
    let B : Fin 4 → Fin 4 → ℝ := fun a b => ∑ c, ∑ d, n c * n d * rdual W c a d b
    ((∀ a b, E a b = E b a) ∧ ∑ a, η a * E a a = 0 ∧
      (∀ b, ∑ a, n a * E a b = 0) ∧ ∀ a, ∑ b, E a b * n b = 0) ∧
    ((∀ a b, B a b = B b a) ∧ ∑ a, η a * B a a = 0 ∧
      (∀ b, ∑ a, n a * B a b = 0) ∧ ∀ a, ∑ b, B a b * n b = 0) :=
  DoubleForm.electric_magnetic_props hW n

/-- `ε_{abdc} = -ε_{abcd}`. -/
theorem eps4_swap23 (a b c d : Fin 4) : eps4 a b d c = -eps4 a b c d :=
  by simp only [eps4_eq_leviCivita4]; exact leviCivita4_swap34 a b c d

/-- the frame metric `g_{ab} = η_{ab}`. -/
abbrev gη (a b : Fin 4) : ℝ :=
  DoubleForm.gη a b

/-- `n_a` for `n = ∂_t`. -/
abbrev nL : Fin 4 → ℝ :=
  DoubleForm.nL

/-- `l_{ab} = g_{ab} + 2 n_a n_b`. -/
abbrev lmet (a b : Fin 4) : ℝ :=
  DoubleForm.lmet a b

/-- `ω^e{}_{ab}` for the spatial volume form `ω_{bcd} = ω_{abcd} n^a`, `n = ∂_t`. -/
abbrev ωU (e a b : Fin 4) : ℝ :=
  DoubleForm.ωU e a b

/-- explicit table of `ω^e{}_{ab}`. -/
theorem ωU_eq (e a b : Fin 4) : ωU e a b = (
    ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, -1, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, 0, 0], ![0, 1, 0, 0]],
    ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, -1, 0, 0], ![0, 0, 0, 0]]]
      : Fin 4 → Fin 4 → Fin 4 → ℝ) e a b :=
  DoubleForm.ωU_eq e a b

/-- the spatial embedding of a `3 × 3` matrix as a 4-tensor with vanishing `0`-row/column. -/
abbrev emb (E : Matrix (Fin 3) (Fin 3) ℝ) : Fin 4 → Fin 4 → ℝ :=
  DoubleForm.emb E

/-- `C_{0a0b}` for `C = T E B H D` is the embedded `E`. -/
theorem T_0a0b (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    (fun a b => T E B H D 0 a 0 b) = emb E :=
  DoubleForm.ofBlocks_0a0b E B H D

/-- `n_{[c} B_{d]e} ω^e{}_{ab}`. -/
abbrev nBω (B : Fin 4 → Fin 4 → ℝ) (c d a b : Fin 4) : ℝ :=
  DoubleForm.nBω B c d a b

/-- right-hand side of (3.2):
`2 [l_{a[c} E_{d]b} - l_{b[c} E_{d]a} - n_{[c} B_{d]e} ω^e{}_{ab} - n_{[a} B_{b]e} ω^e{}_{cd}]`. -/
abbrev recon (E B : Fin 4 → Fin 4 → ℝ) : T4 (Fin 4) :=
  DoubleForm.recon E B

/-- `n_{[c} B_{d]e} ω^e{}_{ab}` is skew in `(c, d)`. -/
theorem nBω_swap_left (B : Fin 4 → Fin 4 → ℝ) (c d a b : Fin 4) :
    nBω B d c a b = -nBω B c d a b :=
  DoubleForm.nBω_swap_left B c d a b

/-- `n_{[c} B_{d]e} ω^e{}_{ab}` is skew in `(a, b)`. -/
theorem nBω_swap_right (B : Fin 4 → Fin 4 → ℝ) (c d a b : Fin 4) :
    nBω B c d b a = -nBω B c d a b :=
  DoubleForm.nBω_swap_right B c d a b

/-- the right-hand side of (3.2) is a double 2-form. -/
theorem pairSkew_recon (E B : Fin 4 → Fin 4 → ℝ) : PairSkew (recon E B) :=
  DoubleForm.pairSkew_recon E B

/-- **Thesis eq. (3.2), special case `n = ∂_t`** (Bel reconstruction): an algebraic Weyl tensor
is recovered from its electric and magnetic parts `E_{ab} = W_{0a0b}`, `B_{ab} = W*_{0a0b}`.

Thesis gap: "a straightforward calculation" in the thesis; here it is checked on the 36
bivector components. The sign of the `B`-terms requires the spatial volume form
`ω_{bcd} = ω_{abcd} n^a` (as stated after (3.2)); the `n^d` convention used in the proof of
Prop 3.1 has the opposite sign. The general unit timelike `n` is `weyl_reconstruct_unit`.
See [QuennevilleBelair2015, eq. (3.2)]; cf. [Bel1958]. -/
theorem weyl_reconstruct {W : T4 (Fin 4)} (hW : IsWeylLike W) :
    W = recon (fun a b => W 0 a 0 b) (fun a b => rdual W 0 a 0 b) :=
  DoubleForm.weyl_reconstruct hW

/-- index lowering `n_a = η_{ab} n^b`. -/
abbrev lowr (n : Fin 4 → ℝ) (a : Fin 4) : ℝ :=
  DoubleForm.lowr n a

/-- `η(n, n) = n_a n^a`. -/
abbrev nsq (n : Fin 4 → ℝ) : ℝ :=
  DoubleForm.nsq n

/-- the electric part `X_{ab} = n^c n^d C_{cadb}` of a (0,4)-tensor relative to `n`. -/
abbrev elec (n : Fin 4 → ℝ) (C : T4 (Fin 4)) (a b : Fin 4) : ℝ :=
  DoubleForm.elec n C a b

/-- `ω^e{}_{ab}` for the spatial volume form `ω_{bcd} = ω_{abcd} n^a`. -/
abbrev ωUn (n : Fin 4 → ℝ) (e a b : Fin 4) : ℝ :=
  DoubleForm.ωUn n e a b

/-- `n_{[c} B_{d]e} ω^e{}_{ab}` for a general `n`. -/
abbrev nBωn (n : Fin 4 → ℝ) (B : Fin 4 → Fin 4 → ℝ) (c d a b : Fin 4) : ℝ :=
  DoubleForm.nBωn n B c d a b

/-- the `g`-part of (3.2): `2 [g_{a[c} E_{d]b} - g_{b[c} E_{d]a}]`. -/
abbrev reconG (E : Fin 4 → Fin 4 → ℝ) : T4 (Fin 4) :=
  DoubleForm.reconG E

/-- the `n`-part of (3.2): `2 [2 n_a n_{[c} E_{d]b} - 2 n_b n_{[c} E_{d]a}`
`- n_{[c} B_{d]e} ω^e{}_{ab} - n_{[a} B_{b]e} ω^e{}_{cd}]`. -/
abbrev reconR (n : Fin 4 → ℝ) (E B : Fin 4 → Fin 4 → ℝ) : T4 (Fin 4) :=
  DoubleForm.reconR n E B

/-- a symmetric trace-free `3 × 3` matrix in five free parameters. -/
abbrev stf (x₁ x₂ x₃ x₄ x₅ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  DoubleForm.stf x₁ x₂ x₃ x₄ x₅

/-- explicit table of `n^c n^d C_{cadb}` for `C = [[E, B], [H, D]]`. -/
abbrev elecT (n : Fin 4 → ℝ) (E B H D : Matrix (Fin 3) (Fin 3) ℝ) : Fin 4 → Fin 4 → ℝ :=
  DoubleForm.elecT n E B H D

/-- `elec` of a block tensor is the explicit table `elecT`. -/
theorem elec_T (n : Fin 4 → ℝ) (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    elec n (T E B H D) = elecT n E B H D :=
  DoubleForm.elec_ofBlocks n E B H D

/-- explicit table of `ω^e{}_{ab}`. -/
theorem ωUn_eq (n : Fin 4 → ℝ) (e a b : Fin 4) : ωUn n e a b = (
    ![![![0, 0, 0, 0], ![0, 0, n 3, -n 2], ![0, -n 3, 0, n 1], ![0, n 2, -n 1, 0]],
      ![![0, 0, n 3, -n 2], ![0, 0, 0, 0], ![-n 3, 0, 0, n 0], ![n 2, 0, -n 0, 0]],
      ![![0, -n 3, 0, n 1], ![n 3, 0, 0, -n 0], ![0, 0, 0, 0], ![-n 1, n 0, 0, 0]],
      ![![0, n 2, -n 1, 0], ![-n 2, 0, n 0, 0], ![n 1, -n 0, 0, 0], ![0, 0, 0, 0]]]
      : Fin 4 → Fin 4 → Fin 4 → ℝ) e a b :=
  DoubleForm.ωUn_eq n e a b

/-- Homogenised form of (3.2) on the 36 bivector components: for every `n` (no normalisation),
`η(n,n)² W = R_n - η(n,n) G_n`, where `G_n`, `R_n` are the `g`- and `n`-parts of the right-hand
side of (3.2) built from `E_n = elec n W`, `B_n = elec n W*`. Both sides are homogeneous of
degree 4 in `n`, so this is the polynomial identity behind (3.2). -/
theorem recon_hom (e₁ e₂ e₃ e₄ e₅ b₁ b₂ b₃ b₄ b₅ : ℝ) (n : Fin 4 → ℝ) (I J : Ix) :
    let E := stf e₁ e₂ e₃ e₄ e₅
    let B := stf b₁ b₂ b₃ b₄ b₅
    nsq n ^ 2 * toMat (T E B B (-E)) I J =
      toMat (reconR n (elec n (T E B B (-E))) (elec n (T B (-E) (-E) (-B)))) I J
        - nsq n * toMat (reconG (elec n (T E B B (-E)))) I J :=
  DoubleForm.recon_hom e₁ e₂ e₃ e₄ e₅ b₁ b₂ b₃ b₄ b₅ n I J

/-- `l_{ab} = g_{ab} + 2 n_a n_b` for a general `n`. -/
abbrev lmetN (n : Fin 4 → ℝ) (a b : Fin 4) : ℝ :=
  DoubleForm.lmetN n a b

/-- right-hand side of (3.2) for a general `n`:
`2 [l_{a[c} E_{d]b} - l_{b[c} E_{d]a} - n_{[c} B_{d]e} ω^e{}_{ab} - n_{[a} B_{b]e} ω^e{}_{cd}]`. -/
abbrev reconN (n : Fin 4 → ℝ) (E B : Fin 4 → Fin 4 → ℝ) : T4 (Fin 4) :=
  DoubleForm.reconN n E B

/-- `n_{[c} B_{d]e} ω^e{}_{ab}` is skew in `(c, d)`. -/
theorem nBωn_swap_left (n : Fin 4 → ℝ) (B : Fin 4 → Fin 4 → ℝ) (c d a b : Fin 4) :
    nBωn n B d c a b = -nBωn n B c d a b :=
  DoubleForm.nBωn_swap_left n B c d a b

/-- `n_{[c} B_{d]e} ω^e{}_{ab}` is skew in `(a, b)`. -/
theorem nBωn_swap_right (n : Fin 4 → ℝ) (B : Fin 4 → Fin 4 → ℝ) (c d a b : Fin 4) :
    nBωn n B c d b a = -nBωn n B c d a b :=
  DoubleForm.nBωn_swap_right n B c d a b

/-- the general-`n` right-hand side of (3.2) is a double 2-form. -/
theorem pairSkew_reconN (n : Fin 4 → ℝ) (E B : Fin 4 → Fin 4 → ℝ) :
    PairSkew (reconN n E B) :=
  DoubleForm.pairSkew_reconN n E B

/-- a symmetric trace-free `3 × 3` matrix is an `stf`. -/
theorem eq_stf {E : Matrix (Fin 3) (Fin 3) ℝ} (hE : Eᵀ = E) (htr : trace E = 0) :
    E = stf (E 0 0) (E 0 1) (E 0 2) (E 1 1) (E 1 2) :=
  DoubleForm.eq_stf hE htr

/-- **Thesis eq. (3.2)** (Bel reconstruction) for an arbitrary unit timelike `n`
(`η(n, n) = -1`, either time orientation), in a fixed Minkowski orthonormal frame:
`W_{abcd} = 4 l_{[a[c} E_{d]b]} - 2 n_{[c} B_{d]e} ω^e{}_{ab} - 2 n_{[a} B_{b]e} ω^e{}_{cd}` with
`E_{ab} = n^c n^d W_{cadb}`, `B_{ab} = n^c n^d W*_{cadb}` (the tensors of Prop 3.1),
`l_{ab} = η_{ab} + 2 n_a n_b` and `ω_{bcd} = ω_{abcd} n^a`.

Thesis gap: the thesis states (3.2) for a general `n` as "a straightforward calculation". Here it is
proved without any frame change: `recon_hom` is the homogenised polynomial identity, valid for all
`n`, and `η(n,n) = -1` specialises it. See [QuennevilleBelair2015, eq. (3.2)]; cf. [Bel1958]. -/
theorem weyl_reconstruct_unit {W : T4 (Fin 4)} (hW : IsWeylLike W) {n : Fin 4 → ℝ}
    (hn : nsq n = -1) : W = reconN n (elec n W) (elec n (rdual W)) :=
  DoubleForm.weyl_reconstruct_unit hW hn

/-- Hodge star of a 2-form in Minkowski space, `(*w)_{cd} = ½ w_{ef} ω^{ef}{}_{cd}`. -/
abbrev hodge2 (w : Fin 4 → Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  DoubleForm.hodge2 w

/-- right dual of a product `u_{ab} w_{cd}`. -/
theorem rdual_prod (u w : Fin 4 → Fin 4 → ℝ) :
    rdual (fun a b c d => u a b * w c d) = fun a b c d => u a b * hodge2 w c d :=
  DoubleForm.rdual_prod u w

/-- Thesis §3.1, `** = (-1)^{kl+t}` for `k = l = 2`, `t = 1`: `** = -1` on 2-forms in
signature `(-+++)`. See [QuennevilleBelair2015, §3.1]; cf. [Wald1984]. -/
theorem hodge2_hodge2 (w : Fin 4 → Fin 4 → ℝ) (hw : ∀ a b, w a b = -w b a) :
    hodge2 (hodge2 w) = -w :=
  DoubleForm.hodge2_hodge2 w hw

/-- symmetric trace-free `3 × 3` matrices. -/
abbrev STF : Submodule ℝ (Matrix (Fin 3) (Fin 3) ℝ) :=
  DoubleForm.STF

/-- coordinates `(E₀₀, E₁₁, E₀₁, E₀₂, E₁₂)` on `STF`. -/
abbrev stfEquiv : STF ≃ₗ[ℝ] (Fin 5 → ℝ) :=
  DoubleForm.stfEquiv

/-- `dim STF = 5`. -/
theorem finrank_STF : Module.finrank ℝ STF = 5 :=
  DoubleForm.finrank_STF

/-- algebraic Weyl tensors (Minkowski frame) as a subspace. -/
abbrev weylSpace : Submodule ℝ (T4 (Fin 4)) :=
  DoubleForm.weylSpace

/-- the `E`-block of a Weyl tensor is symmetric trace-free. -/
theorem blkE_mem_STF {C : T4 (Fin 4)} (hC : IsWeylLike C) : blkE C ∈ STF :=
  DoubleForm.blkE_mem_STF hC

/-- the `B`-block of a Weyl tensor is symmetric trace-free. -/
theorem blkB_mem_STF {C : T4 (Fin 4)} (hC : IsWeylLike C) : blkB C ∈ STF :=
  DoubleForm.blkB_mem_STF hC

/-- membership in `STF`. -/
theorem mem_STF {E : Matrix (Fin 3) (Fin 3) ℝ} : E ∈ STF ↔ Eᵀ = E ∧ trace E = 0 :=
  DoubleForm.mem_STF

/-- `[[E, B], [B, -E]]` with `E, B ∈ STF` is a Weyl tensor. -/
theorem T_mem_weylSpace {E B : Matrix (Fin 3) (Fin 3) ℝ} (hE : E ∈ STF) (hB : B ∈ STF) :
    T E B B (-E) ∈ weylSpace :=
  DoubleForm.ofBlocks_mem_weylSpace hE hB

/-- `blkE` is additive. -/
theorem blkE_add (C C' : T4 (Fin 4)) : blkE (C + C') = blkE C + blkE C' :=
  DoubleForm.blkE_add C C'

/-- `blkB` is additive. -/
theorem blkB_add (C C' : T4 (Fin 4)) : blkB (C + C') = blkB C + blkB C' :=
  DoubleForm.blkB_add C C'

/-- `blkE` is homogeneous. -/
theorem blkE_smul (r : ℝ) (C : T4 (Fin 4)) : blkE (r • C) = r • blkE C :=
  DoubleForm.blkE_smul r C

/-- `blkB` is homogeneous. -/
theorem blkB_smul (r : ℝ) (C : T4 (Fin 4)) : blkB (r • C) = r • blkB C :=
  DoubleForm.blkB_smul r C

/-- Weyl tensors are parametrised linearly by their electric and magnetic blocks. -/
abbrev weylEquiv : weylSpace ≃ₗ[ℝ] STF × STF :=
  DoubleForm.weylEquiv

/-- Thesis §3.2: in 4 dimensions the Weyl tensor has `n(n+1)(n+2)(n-3)/12 = 10` independent
components (here: the space of algebraic Weyl tensors w.r.t. `η` has dimension 10).

Thesis gap: stated without proof ("it can be shown"); proved here for `n = 4` via the block
form `[[E, B], [B, -E]]` with `E, B` symmetric trace-free (5 + 5).
See [QuennevilleBelair2015, §3.2] (which cites [Alcubierre2008, p. 288] and [Friedrich1996] for
the Riemann/Weyl splitting). -/
theorem finrank_weylSpace : Module.finrank ℝ weylSpace = 10 :=
  DoubleForm.finrank_weylSpace

/-- The structure field `pairSkew` (`Feec.DoubleForm.IsWeyl.pairSkew`). -/
theorem IsWeylLike.pairSkew {C : T4 (Fin 4)} (h : IsWeylLike C) : PairSkew C :=
  DoubleForm.IsWeyl.pairSkew h

/-- The structure field `bianchi` (`Feec.DoubleForm.IsWeyl.bianchi`). -/
theorem IsWeylLike.bianchi {C : T4 (Fin 4)} (h : IsWeylLike C) : Bianchi1 C :=
  DoubleForm.IsWeyl.bianchi h

/-- The structure field `traceFree` (`Feec.DoubleForm.IsWeyl.traceFree`). -/
theorem IsWeylLike.traceFree {C : T4 (Fin 4)} (h : IsWeylLike C) : ∀ b c, mtr C b c = 0 :=
  DoubleForm.IsWeyl.traceFree h

end Bivector
end Feec

end
