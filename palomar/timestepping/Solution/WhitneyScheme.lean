module

public import Solution.WhitneyInterp
public import Solution.Forms

/-!
# The Crank–Nicolson Whitney scheme of the challenge is `Feec`'s

A row of the challenge, `L²Λ⁰(Q) × L²Λ¹(Q) × L²Λ²(Q)`, is a point of `Feec`'s `RowSpace`
(`toRow`), and the Whitney row `DState (whitneyRow N)` embeds in it (`ofD`): its image is the
challenge's `Vₕ` (`rowMem_false_iff`), and `whitneyInterior N` is sent onto `V̊ₕ`
(`rowMem_true_iff`). The inner products agree (`rowInner_ofD`), the challenge's `waveForm` is the
form of `Feec.Models.Cube.Inhomogeneous.discreteWave` (`waveForm_ofD`), so the challenge's
`IsCNStep` is `Feec.TimeStepping.IsDirichletCNStep` with zero load (`isCNStep_ofD_iff`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 7

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set

@[expose] public noncomputable section

namespace TimeStepping

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.Inhomogeneous
  Feec.HilbertComplex

/-- A point of `Feec`'s `RowSpace` as a row of the challenge. -/
def toRow (z : RowSpace) : Row := (z 0, z 1, z 2)

theorem toRow_sub (z z' : RowSpace) : toRow (z - z') = toRow z - toRow z' := rfl

theorem toRow_add (z z' : RowSpace) : toRow (z + z') = toRow z + toRow z' := rfl

theorem toRow_injective : Function.Injective toRow := fun z z' h => by
  have h0 : z 0 = z' 0 := congrArg Prod.fst h
  have h1 : z 1 = z' 1 := congrArg (fun r : Row => r.2.1) h
  have h2 : z 2 = z' 2 := congrArg (fun r : Row => r.2.2) h
  refine PiLp.ext fun i => ?_
  fin_cases i
  exacts [h0, h1, h2]

theorem norm_toRow (z : RowSpace) :
    √(‖(toRow z).1‖ ^ 2 + ‖(toRow z).2.1‖ ^ 2 + ‖(toRow z).2.2‖ ^ 2) = ‖z‖ := by
  rw [PiLp.norm_eq_of_L2 z, Fin.sum_univ_three]
  rfl

/-- A row of the challenge as a point of `Feec`'s `RowSpace`. -/
def ofRow (x : Row) : RowSpace := WithLp.toLp 2 fun i => match i with
  | 0 => x.1
  | 1 => x.2.1
  | 2 => x.2.2

theorem inner_toRow (z z' : RowSpace) : rowInner (toRow z) (toRow z') = ⟪z, z'⟫ := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  rfl

variable (N : ℕ)

/-- The Whitney row in the challenge's rows. -/
def ofD (a : DState (whitneyRow N)) : Row := toRow (dEmb (whitneyRow N) a)

theorem ofD_sub (a b : DState (whitneyRow N)) : ofD N (a - b) = ofD N a - ofD N b := by
  rw [ofD, ofD, ofD, map_sub, toRow_sub]

theorem ofD_add (a b : DState (whitneyRow N)) : ofD N (a + b) = ofD N a + ofD N b := by
  rw [ofD, ofD, ofD, map_add, toRow_add]

theorem ofD_injective : Function.Injective (ofD N) := fun a b h => by
  have h' := toRow_injective h
  refine PiLp.ext fun i => Subtype.ext ?_
  exact congrArg (fun z : RowSpace => z i) h'

theorem rowInner_ofD (a b : DState (whitneyRow N)) : rowInner (ofD N a) (ofD N b) = ⟪a, b⟫ := by
  rw [ofD, ofD, inner_toRow, inner_dEmb]

theorem mem_whitney (k : ℤ) {x : L2Form (cube 3) k} :
    x ∈ (whitney 3 N).V k ↔ x ∈ femSpace (cube 3) (cubeMesh N) topSeq ∅ k := by
  rw [← whitney_V_eq N k]; rfl

theorem mem_whitneyMin (k : ℤ) {x : L2Form (cube 3) k} :
    x ∈ (whitneyMin 3 N).V k ↔
      x ∈ femSpace (cube 3) (cubeMesh N) topSeq (cubeMesh N).boundaryFacets k := by
  rw [← whitneyMin_V_eq N k]; rfl

theorem rowMem_iff (M : SimplicialMesh 3) (b : Bool) (x : Row) : RowMem M b x ↔
    x.1 ∈ femSpace (cube 3) M topSeq (if b then M.boundaryFacets else ∅) 0 ∧
      x.2.1 ∈ femSpace (cube 3) M topSeq (if b then M.boundaryFacets else ∅) 1 ∧
      x.2.2 ∈ femSpace (cube 3) M topSeq (if b then M.boundaryFacets else ∅) 2 :=
  Iff.rfl

/-- **The challenge's `Vₕ` is the image of the Whitney row.** -/
theorem rowMem_false_iff (x : Row) : RowMem (cubeMesh N) false x ↔ ∃ a, x = ofD N a := by
  rw [rowMem_iff]
  simp only [Bool.false_eq_true, ↓reduceIte]
  constructor
  · rintro ⟨h0, h1, h2⟩
    have hm : ∀ i, ofRow x i ∈ (whitneyRow N).V i := by
      intro i
      fin_cases i
      · exact (mem_whitney N 0).2 h0
      · exact (mem_whitney N 1).2 h1
      · exact (mem_whitney N 2).2 h2
    exact ⟨WithLp.toLp 2 fun i => ⟨ofRow x i, hm i⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨(mem_whitney N 0).1 (a 0).2, (mem_whitney N 1).1 (a 1).2, (mem_whitney N 2).1 (a 2).2⟩

/-- **`V̊ₕ` is the image of `whitneyInterior N`.** -/
theorem rowMem_true_ofD_iff (a : DState (whitneyRow N)) :
    RowMem (cubeMesh N) true (ofD N a) ↔ a ∈ whitneyInterior N := by
  rw [rowMem_iff]
  simp only [↓reduceIte]
  constructor
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · exact (mem_whitneyMin N 0).2 h0
    · exact (mem_whitneyMin N 1).2 h1
    · exact (mem_whitneyMin N 2).2 h2
  · intro h
    exact ⟨(mem_whitneyMin N 0).1 (h 0), (mem_whitneyMin N 1).1 (h 1), (mem_whitneyMin N 2).1 (h 2)⟩

theorem rowMem_true_iff (x : Row) :
    RowMem (cubeMesh N) true x ↔ ∃ a ∈ whitneyInterior N, x = ofD N a := by
  constructor
  · intro h
    obtain ⟨h0, h1, h2⟩ := (rowMem_iff _ _ _).1 h
    have hf : RowMem (cubeMesh N) false x := (rowMem_iff _ _ _).2
      ⟨(mem_whitney N 0).1 (whitneyMin_le_whitney N 0 ((mem_whitneyMin N 0).2 h0)),
        (mem_whitney N 1).1 (whitneyMin_le_whitney N 1 ((mem_whitneyMin N 1).2 h1)),
        (mem_whitney N 2).1 (whitneyMin_le_whitney N 2 ((mem_whitneyMin N 2).2 h2))⟩
    obtain ⟨a, rfl⟩ := (rowMem_false_iff N x).1 hf
    exact ⟨a, (rowMem_true_ofD_iff N a).1 h, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact (rowMem_true_ofD_iff N a).2 ha

/-- The challenge's `wd` is the weak `d` of `Feec`'s complex on its domain. -/
theorem wd_eq (k : ℤ) (x : ((complex 3).d k (k + 1)).domain) :
    wd k (x : L2F ℝ (cubeDomain 3) (formIdx 3 k)) = (complex 3).d k (k + 1) x := by
  have hd : (complex 3).d k (k + 1) = dMax (cube 3) k := by
    rw [dMax_eq]; exact deRham_maximalComplex_d _ k
  have hx : (x : L2F ℝ (cubeDomain 3) (formIdx 3 k)) ∈ (dMax (cube 3) k).domain := hd ▸ x.2
  exact (dite_eq_left hx).trans (LinearPMap.apply_of_eq' hd.symm ⟨_, hx⟩)

/-- **The challenge's `waveForm` is the form of `Feec`'s `discreteWave`.** -/
theorem waveForm_ofD (a b : DState (whitneyRow N)) :
    waveForm (ofD N a) (ofD N b) = ⟪discreteWave (whitneyRow N) a, b⟫ := by
  rw [inner_discreteWave, PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_three,
    Fin.sum_univ_three]
  have hD : ∀ (c : DState (whitneyRow N)) (j : Fin 3),
      discreteD (whitneyRow N) c j = ∑ i, (whitneyRow N).dLin i j (c i) := fun c j => rfl
  have z : ∀ i j : Fin 3, ¬ (i.val + 1 = j.val) → ∀ x, (whitneyRow N).dLin i j x = 0 :=
    fun i j h x => by rw [Subcomplex.dLin_eq_zero_of_not_rel _ h]; rfl
  simp only [hD, Fin.sum_univ_three, z 0 0 (by decide), z 1 0 (by decide), z 2 0 (by decide),
    z 1 1 (by decide), z 2 1 (by decide), z 0 2 (by decide), z 2 2 (by decide), zero_add,
    add_zero, inner_zero_left, inner_zero_right]
  have e01 : ∀ c : DState (whitneyRow N),
      ((whitneyRow N).dLin 0 1 (c 0)).val = wd 0 (c 0).val :=
    fun c => (wd_eq 0 ⟨_, (whitneyRow N).le_domain 0 1 (c 0).2⟩).symm
  have e12 : ∀ c : DState (whitneyRow N),
      ((whitneyRow N).dLin 1 2 (c 1)).val = wd 1 (c 1).val :=
    fun c => (wd_eq 1 ⟨_, (whitneyRow N).le_domain 1 2 (c 1).2⟩).symm
  simp only [waveForm, ofD, toRow, dEmb_apply, Submodule.coe_inner]
  rw [e01 a, e01 b, e12 a, e12 b, sub_sub]
  rfl

/-- **The challenge's Crank–Nicolson step is `Feec`'s** `IsDirichletCNStep` with zero load. -/
theorem isCNStep_ofD_iff (Δt : ℝ) (g u : DState (whitneyRow N)) (x : Row) :
    IsCNStep (cubeMesh N) Δt (ofD N g) (ofD N u) x ↔ ∃ u', x = ofD N u' ∧
      Feec.TimeStepping.IsDirichletCNStep (whitneyInterior N) (discreteWave (whitneyRow N))
        (Δt / 2) 0 g u u' := by
  constructor
  · rintro ⟨hx, hb, hv⟩
    obtain ⟨u', rfl⟩ := (rowMem_false_iff N x).1 hx
    refine ⟨u', rfl, ?_, fun v hv' => ?_⟩
    · rw [← ofD_sub] at hb
      exact (rowMem_true_ofD_iff N _).1 hb
    · have := hv (ofD N v) ((rowMem_true_ofD_iff N v).2 hv')
      rw [← ofD_sub, ← ofD_add, rowInner_ofD, waveForm_ofD] at this
      rw [this, inner_zero_left, add_zero]
  · rintro ⟨u', rfl, hb, hv⟩
    refine ⟨(rowMem_false_iff N _).2 ⟨u', rfl⟩, ?_, fun v hv' => ?_⟩
    · rw [← ofD_sub]; exact (rowMem_true_ofD_iff N _).2 hb
    · obtain ⟨v', hv'', rfl⟩ := (rowMem_true_iff N v).1 hv'
      rw [← ofD_sub, ← ofD_add, rowInner_ofD, waveForm_ofD, hv v' hv'', inner_zero_left, add_zero]

end TimeStepping
