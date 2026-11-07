module

public import Solution.CrankNicolson
public import Feec.Models.Cube.InhomogeneousLeapfrog

/-!
# `FEEC.leapfrog_cube` and `FEEC.inverse_estimate`

The challenge's leapfrog step is `Feec`'s `TimeStepping.IsDirichletLeapfrogStep` on the Whitney
row (`isLeapfrogStep_ofD_iff`, as `isCNStep_ofD_iff`), the norm of a row is the norm of the
Whitney state (`rowNorm_ofD`), and the challenge's `𝐝ₕ v = (0, dσ, dE)` is `Feec`'s `discreteD`
(`norm_discreteD_eq`). `FEEC.leapfrog_cube` is then
`Feec.Models.Cube.Inhomogeneous.exists_mul_norm_discreteD_whitneyRow_le` (the inverse estimate),
`TimeStepping.existsUnique_isDirichletLeapfrogStep`, `whitney_leapfrog_stable` and
`RowSolution.whitney_leapfrog_error_le_row`. `FEEC.inverse_estimate` is
`Feec.FiniteElement.PolySeq.exists_mul_norm_d_le` on the `Feec` meshes `M.toFeec Ω` (shape
regularity from the inscribed balls, `isShapeRegular_toFeec`), whose spaces are the challenge's
(`mem_V_iff`).

## References

* [P. Joly, *Variational Methods for Time-Dependent Wave Propagation Problems*][Joly2003]
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.2

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set MeasureTheory

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.Inhomogeneous
  Feec.HilbertComplex

variable (N : ℕ)

/-- The norm of a Whitney state is the norm of its row. -/
theorem rowNorm_ofD (a : DState (whitneyRow N)) : rowNorm (ofD N a) = ‖a‖ := by
  rw [rowNorm, ofD, norm_toRow, norm_emb (inner_dEmb (whitneyRow N))]

/-- **`Feec`'s `𝐝ₕ` on the Whitney row is `(0, dσ, dE)`.** -/
theorem norm_discreteD_eq (a : DState (whitneyRow N)) :
    ‖discreteD (whitneyRow N) a‖ = √(‖wd 0 (ofD N a).1‖ ^ 2 + ‖wd 1 (ofD N a).2.1‖ ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg _), PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  have hD : ∀ (c : DState (whitneyRow N)) (j : Fin 3),
      discreteD (whitneyRow N) c j = ∑ i, (whitneyRow N).dLin i j (c i) := fun c j => rfl
  have z : ∀ i j : Fin 3, ¬ (i.val + 1 = j.val) → ∀ x, (whitneyRow N).dLin i j x = 0 :=
    fun i j h x => by rw [Subcomplex.dLin_eq_zero_of_not_rel _ h]; rfl
  simp only [hD, Fin.sum_univ_three, z 0 0 (by decide), z 1 0 (by decide), z 2 0 (by decide),
    z 1 1 (by decide), z 2 1 (by decide), z 0 2 (by decide), z 2 2 (by decide), zero_add,
    add_zero, norm_zero]
  have e01 : ((whitneyRow N).dLin 0 1 (a 0)).val = wd 0 (a 0).val :=
    (wd_eq 0 ⟨_, (whitneyRow N).le_domain 0 1 (a 0).2⟩).symm
  have e12 : ((whitneyRow N).dLin 1 2 (a 1)).val = wd 1 (a 1).val :=
    (wd_eq 1 ⟨_, (whitneyRow N).le_domain 1 2 (a 1).2⟩).symm
  have n01 : ‖(whitneyRow N).dLin 0 1 (a 0)‖ = ‖wd 0 (a 0).val‖ := by rw [← e01]; rfl
  have n12 : ‖(whitneyRow N).dLin 1 2 (a 1)‖ = ‖wd 1 (a 1).val‖ := by rw [← e12]; rfl
  rw [n01, n12]
  norm_num
  rfl

/-- **The challenge's leapfrog step is `Feec`'s** `IsDirichletLeapfrogStep`. -/
theorem isLeapfrogStep_ofD_iff (Δt : ℝ) (g u u' : DState (whitneyRow N)) (x : Row) :
    IsLeapfrogStep (cubeMesh N) Δt (ofD N g) (ofD N u) (ofD N u') x ↔ ∃ u'', x = ofD N u'' ∧
      Feec.TimeStepping.IsDirichletLeapfrogStep (whitneyInterior N)
        (discreteWave (whitneyRow N)) Δt g u u' u'' := by
  constructor
  · rintro ⟨hx, hb, hv⟩
    obtain ⟨u'', rfl⟩ := (rowMem_false_iff N x).1 hx
    refine ⟨u'', rfl, ?_, fun v hv' => ?_⟩
    · rw [← ofD_sub] at hb
      exact (rowMem_true_ofD_iff N _).1 hb
    · have := hv (ofD N v) ((rowMem_true_ofD_iff N v).2 hv')
      rwa [← ofD_sub, rowInner_ofD, waveForm_ofD] at this
  · rintro ⟨u'', rfl, hb, hv⟩
    refine ⟨(rowMem_false_iff N _).2 ⟨u'', rfl⟩, ?_, fun v hv' => ?_⟩
    · rw [← ofD_sub]; exact (rowMem_true_ofD_iff N _).2 hb
    · obtain ⟨v', hv'', rfl⟩ := (rowMem_true_iff N v).1 hv'
      rw [← ofD_sub, rowInner_ofD, waveForm_ofD, hv v' hv'']

/-- Rows of `Vₕ` up to step `m` are the rows of Whitney states. -/
theorem exists_seq_ofD {u : ℕ → Row} {m : ℕ} (h : ∀ k ≤ m, RowMem (cubeMesh N) false (u k)) :
    ∃ a : ℕ → DState (whitneyRow N), ∀ k ≤ m, u k = ofD N (a k) := by
  classical
  refine ⟨fun k => if hk : RowMem (cubeMesh N) false (u k) then
    ((rowMem_false_iff N _).1 hk).choose else 0, fun k hk => ?_⟩
  dsimp only
  rw [dite_eq_left (h k hk)]
  exact ((rowMem_false_iff N _).1 (h k hk)).choose_spec

theorem rowMem_false_of_true {x : Row} (h : RowMem (cubeMesh N) true x) :
    RowMem (cubeMesh N) false x := by
  obtain ⟨a, -, rfl⟩ := (rowMem_true_iff N x).1 h
  exact (rowMem_false_iff N _).2 ⟨a, rfl⟩

theorem ofD_zero : ofD N 0 = 0 := by
  rw [ofD, map_zero]; rfl

/-! ### The inverse estimate on general meshes -/

variable {n : ℕ}

/-- The shape-regularity constant of a mesh with a simplex is positive. -/
theorem pos_of_isShapeRegular [NeZero n] {M : SimplicialMesh n} {σ : ℝ} (hM : IsShapeRegular M σ)
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ M.simplices) : 0 < σ := by
  obtain ⟨-, ρ, hρ, -, hd⟩ := hM T hT
  exact pos_of_mul_pos_left ((Feec.Mesh.diam_pos T).trans_le hd) hρ.le

/-- A mesh of positive mesh size has a simplex. -/
theorem exists_mem_simplices {M : SimplicialMesh n} (hM : 0 < meshSize M) :
    ∃ T, T ∈ M.simplices := by
  by_contra h
  have : IsEmpty M.simplices := ⟨fun T => h ⟨T, T.2⟩⟩
  simp [meshSize] at hM

end FEEC
