module

public import Feec.Geometry.Bivector

/-!
# Hodge duality on 2-forms and double 2-forms (four-dimensional Minkowski frame)

## Main definitions

* `DoubleForm.rdual C` (`C*`), `DoubleForm.ldual C` (`*C`), the Hodge matrix `S` on bivectors,
  and `DoubleForm.hodge2 w` (`*w` on 2-forms).

## Main results

* `rdual_ofMat`, `ldual_ofMat`: right/left dualisation multiply the bivector matrix by `S`.
* **Prop 3.2**: `rdual_ofBlocks`, `ldual_ofBlocks`, `ldual_rdual_ofBlocks` and
  `blocks_eq_and_duals` (the block action of `C*`, `*C`, `*C*`, with the `½` the thesis drops).
* `rdual_rdual`, `ldual_ldual`, `ldual_rdual_comm`, `ldual_eq_rdual_swap`.
* `hodge2_hodge2`: `** = -1` on 2-forms in signature `(-+++)`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §3.1–3.2 (Prop 3.2)
* [R. M. Wald, *General Relativity*][Wald1984]
-/

@[expose] public section

open Matrix Equiv Feec.CurvatureTensor

noncomputable section

namespace Feec.DoubleForm

/-! ### Hodge duals of a double 2-form -/

/-- right dual `C*_{abcd} = ½ C_{abef} ω^{ef}{}_{cd}` (Minkowski frame, `ω = ε`). -/
def rdual (C : Tensor4) : Tensor4 :=
  fun a b c d => (1 / 2) * ∑ e, ∑ f, C a b e f * Metric.minkowski4 ℝ e * Metric.minkowski4 ℝ f * leviCivita4 ℝ e f c d

/-- left dual `*C_{abcd} = ½ ω_{ab}{}^{ef} C_{efcd}`. -/
def ldual (C : Tensor4) : Tensor4 :=
  fun a b c d => (1 / 2) * ∑ e, ∑ f, leviCivita4 ℝ a b e f * Metric.minkowski4 ℝ e * Metric.minkowski4 ℝ f * C e f c d

/-- the Hodge star on bivectors in the basis `(t∧x, t∧y, t∧z | y∧z, z∧x, x∧y)`. -/
def S : Matrix Ix Ix ℝ := fromBlocks 0 (-1) 1 0

/-- right dualisation multiplies the bivector matrix by the Hodge matrix `S` on the right
(`t∧x ↦ y∧z`, `y∧z ↦ -t∧x`, cyclically, as in the proof of Thesis Prop 3.2). -/
theorem rdual_ofMat (M : Matrix Ix Ix ℝ) : rdual (ofMat M) = ofMat (M * S) := by
  funext a b c d
  simp only [rdual, ofMat_apply]
  generalize pidx a b = I
  fin_cases c <;> fin_cases d <;>
    simp [Fin.sum_univ_four, leviCivita4_eq_int, leviCivita4Int, sgn, pidx, Metric.minkowski4, S, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_three] <;> ring

/-- the left dual is the right dual conjugated by the pair interchange. -/
theorem ldual_eq (C : Tensor4) : ldual C = swapPairs (rdual (swapPairs C)) := by
  funext a b c d
  simp only [ldual, swapPairs, rdual]
  congr 1
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  rw [leviCivita4_swap_pairs a b e f]; ring

/-- left dualisation multiplies the bivector matrix by `Sᵀ` on the left. -/
theorem ldual_ofMat (M : Matrix Ix Ix ℝ) : ldual (ofMat M) = ofMat (Sᵀ * M) := by
  rw [ldual_eq, swapPairs_ofMat, rdual_ofMat, swapPairs_ofMat, transpose_mul, transpose_transpose]

/-- **Thesis Prop 3.2 (right dual).** `C ↦ C*` acts on blocks as `[[E,B],[H,D]] ↦ [[B,-E],[D,-H]]`.
See [QuennevilleBelair2015], Prop 3.2.

Correction: the thesis' formula `C*_{abcd} v^c w^d = C_{abef} (ε^{ef}{}_{cd} v^c w^d)` and
`B_{ab} = C_{0aef} ε^{ef}{}_{0b}` miss the factor `½` (without it `t∧x ↦ 2 y∧z`); `rdual`
includes it. -/
theorem rdual_ofBlocks (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    rdual (ofBlocks E B H D) = ofBlocks B (-E) D (-H) := by
  rw [ofBlocks, rdual_ofMat, S, fromBlocks_multiply, ofBlocks]; simp

/-- **Thesis Prop 3.2 (left dual).** `C ↦ *C` acts as `[[E,B],[H,D]] ↦ [[H,D],[-E,-B]]`.
See [QuennevilleBelair2015], Prop 3.2. -/
theorem ldual_ofBlocks (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    ldual (ofBlocks E B H D) = ofBlocks H D (-E) (-B) := by
  rw [ofBlocks, ldual_ofMat, S, fromBlocks_transpose, fromBlocks_multiply, ofBlocks]; simp

/-- **Thesis Prop 3.2 (double dual).** `C ↦ *C*` acts as `[[E,B],[H,D]] ↦ [[D,-H],[-B,E]]`.
See [QuennevilleBelair2015], Prop 3.2. -/
theorem ldual_rdual_ofBlocks (E B H D : Matrix (Fin 3) (Fin 3) ℝ) :
    ldual (rdual (ofBlocks E B H D)) = ofBlocks D (-H) (-B) E := by
  rw [rdual_ofBlocks, ldual_ofBlocks, neg_neg]


/-- **Thesis Prop 3.2.** For a double 2-form `C` (skew in each pair) set, as in the thesis,
`E_{ab} = C_{0a0b}`, `B_{ab} = C*_{0a0b}`, `H_{ab} = *C_{0a0b}`, `D_{ab} = *C*_{0a0b}`.
Then `C` has bivector block matrix `[[E,B],[H,D]]`, and the three duals act as stated.
See [QuennevilleBelair2015], Prop 3.2 (block layout following thesis ref. [10], Frauendiener,
not in `references.bib`).

Correction: `B, H, D` carry the factor `½` built into `rdual`/`ldual` (missing in the thesis'
formula for `B_{ab}`). -/
theorem blocks_eq_and_duals {C : Tensor4} (hC : PairSkew C) :
    let E : Matrix (Fin 3) (Fin 3) ℝ := fun i j => C 0 i.succ 0 j.succ
    let B : Matrix (Fin 3) (Fin 3) ℝ := fun i j => rdual C 0 i.succ 0 j.succ
    let H : Matrix (Fin 3) (Fin 3) ℝ := fun i j => ldual C 0 i.succ 0 j.succ
    let D : Matrix (Fin 3) (Fin 3) ℝ := fun i j => ldual (rdual C) 0 i.succ 0 j.succ
    C = ofBlocks E B H D ∧ rdual C = ofBlocks B (-E) D (-H) ∧ ldual C = ofBlocks H D (-E) (-B) ∧
      ldual (rdual C) = ofBlocks D (-H) (-B) E := by
  intro E B H D
  have hT := eq_ofBlocks_blocks hC
  have hE : E = blkE C := by ext i j; simp [E, blkE_apply]
  have hB : B = blkB C := by
    ext i j; simp only [B]; rw [← blkE_apply (rdual C), hT, rdual_ofBlocks, blkE_ofBlocks, blkB_ofBlocks]
  have hH : H = blkH C := by
    ext i j; simp only [H]; rw [← blkE_apply (ldual C), hT, ldual_ofBlocks, blkE_ofBlocks, blkH_ofBlocks]
  have hD : D = blkD C := by
    ext i j; simp only [D]; rw [← blkE_apply (ldual (rdual C)), hT, ldual_rdual_ofBlocks, blkE_ofBlocks, blkD_ofBlocks]
  rw [hE, hB, hH, hD]
  refine ⟨hT, ?_, ?_, ?_⟩ <;> conv_lhs => rw [hT]
  · exact rdual_ofBlocks _ _ _ _
  · exact ldual_ofBlocks _ _ _ _
  · exact ldual_rdual_ofBlocks _ _ _ _

/-- Thesis §3.2: `(W*)* = -W` for every double 2-form (`** = -1` on 2-forms, signature
`(-+++)`). See [QuennevilleBelair2015], §3.2. -/
theorem rdual_rdual {C : Tensor4} (hC : PairSkew C) : rdual (rdual C) = -C := by
  rw [eq_ofBlocks_blocks hC, rdual_ofBlocks, rdual_ofBlocks, ofBlocks_neg]

/-- `*(*W) = -W` for every double 2-form. -/
theorem ldual_ldual {C : Tensor4} (hC : PairSkew C) : ldual (ldual C) = -C := by
  rw [eq_ofBlocks_blocks hC, ldual_ofBlocks, ldual_ofBlocks, ofBlocks_neg]

/-- left and right duals commute. -/
theorem ldual_rdual_comm {C : Tensor4} (hC : PairSkew C) :
    ldual (rdual C) = rdual (ldual C) := by
  rw [eq_ofBlocks_blocks hC, rdual_ofBlocks, ldual_ofBlocks, ldual_ofBlocks, rdual_ofBlocks]

/-- Thesis §3.2: for `W` with the interchange symmetry, `*W_{abcd} = W*_{cdab}`.
See [QuennevilleBelair2015], §3.2. -/
theorem ldual_eq_rdual_swap {C : Tensor4} (hC : Interchange C) (a b c d : Fin 4) :
    ldual C a b c d = rdual C c d a b := by
  rw [ldual_eq]; simp only [swapPairs, rdual]
  congr 1
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  rw [hC]


/-! ### `** = -1` on 2-forms -/

/-- Hodge star of a 2-form in Minkowski space, `(*w)_{cd} = ½ w_{ef} ω^{ef}{}_{cd}`. -/
def hodge2 (w : Fin 4 → Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun c d => (1 / 2) * ∑ e, ∑ f, w e f * Metric.minkowski4 ℝ e * Metric.minkowski4 ℝ f * leviCivita4 ℝ e f c d

/-- right dual of a product `u_{ab} w_{cd}`. -/
theorem rdual_prod (u w : Fin 4 → Fin 4 → ℝ) :
    rdual (fun a b c d => u a b * w c d) = fun a b c d => u a b * hodge2 w c d := by
  funext a b c d
  simp only [rdual, hodge2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  ring

/-- Thesis §3.1, `** = (-1)^{kl+t}` for `k = l = 2`, `t = 1`: `** = -1` on 2-forms in
signature `(-+++)`. See [QuennevilleBelair2015], §3.1; cf. [Wald1984]. -/
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

end Feec.DoubleForm

end
