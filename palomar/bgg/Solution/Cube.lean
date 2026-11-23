module

public import Solution.Bridge
public import Solution.Wedge
public import Feec.Models.Cube.BGGCohomology

/-!
# The Hessian, elasticity and div–div diagrams of the challenge on the cube

The stacked diagrams of the challenge on the cube are `Feec`'s BGG diagrams of forms
(`Feec.FiniteElement.hessianFormData`, `divDivFormData` and `elasticityFormData` on
`Feec.Models.Cube.FEM.cubeDomain 3`): `dMax` is `Feec`'s maximal exterior derivative (`dMax_eq`),
`vecOp` of it is the product complex `Feec.HilbertComplex.pi` (`vecOp_eq_piD`), and `wedge`,
`dxVec`, `crossWedge` are `Feec.FiniteElement.wsL2`, `dxVecL2`, `crossL2` (`wedge_eq`,
`dxWedge_eq`, `dxVec_eq`, `crossWedge_eq`).

For analytic BGG data `D` of `Feec` on `ℤ`, the graph spaces of the rows carry the bounded maps
`graphD` (`(u, du) ↦ (du, 0)`) and `graphS` (`(φ, d̃φ) ↦ (Sφ, -S d̃φ)`), a stacked diagram of
the domain complexes of the challenge (`toDomainDiagram`), whose rows have the cohomology of the
rows of `D` (`graphHomologyEquiv`, from `Feec.HilbertComplex.cohomologyEquivOfIso`); `s` is bounded
below where `S` is in two consecutive degrees (`antilipschitz_graphS`, as
`Feec.BGG.HilbertData.antilipschitz_domainS`) and onto modulo `d` where the rows split
(`sup_range_eq_top_of_exists`, as `Feec.BGG.HilbertData.regularDecomposition_of_forall_exists`).

## References

* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021], §3, §4.1, Theorem 6

Bibliography: [references.bib](../../../docs/references.bib)
-/

open CategoryTheory
open scoped InnerProductSpace

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.FiniteElement LinearPMap

/-! ### Graph spaces -/

section Graph

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

theorem graph2_eq (A : E →ₗ.[ℝ] F) : graph2 A = A.graphL2 := rfl

/-- `D(A) ≃ Γ(A)`, `x ↦ (x, A x)`. -/
def graphEquiv (A : E →ₗ.[ℝ] F) : A.domain ≃ₗ[ℝ] graph2 A where
  toFun x := A.toGraphSpace x
  invFun v := ⟨A.graphFst v, by
    obtain ⟨x, rfl, -, -⟩ := A.exists_toGraphSpace_eq v
    exact x.2⟩
  map_add' x y := Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext rfl (A.map_add x y)))
  map_smul' c x := Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext rfl (A.map_smul c x)))
  left_inv _ := rfl
  right_inv v := A.graphFst_injective rfl

@[simp] theorem graphEquiv_fst (A : E →ₗ.[ℝ] F) (x : A.domain) :
    ((graphEquiv A x : WithLp 2 (E × F)).ofLp).1 = x := rfl

@[simp] theorem graphEquiv_snd (A : E →ₗ.[ℝ] F) (x : A.domain) :
    ((graphEquiv A x : WithLp 2 (E × F)).ofLp).2 = A x := rfl

/-- A point of a graph is determined by its first component. -/
theorem graph2_ext {A : E →ₗ.[ℝ] F} {v w : graph2 A}
    (h : ((v : WithLp 2 (E × F)).ofLp).1 = ((w : WithLp 2 (E × F)).ofLp).1) : v = w :=
  A.graphFst_injective h

end Graph

/-! ### The stacked diagram of the domain complexes of analytic BGG data -/

section Domain

variable {E Et : ℤ → Type} [∀ k, NormedAddCommGroup (E k)] [∀ k, InnerProductSpace ℝ (E k)]
  [∀ k, CompleteSpace (E k)] [∀ k, NormedAddCommGroup (Et k)] [∀ k, InnerProductSpace ℝ (Et k)]
  [∀ k, CompleteSpace (Et k)]

/-- `(u, du) ↦ (du, 0)` on the graph spaces of a Hilbert complex. -/
def graphD (H : Feec.HilbertComplex ℝ (ComplexShape.up ℤ) E) (k : ℤ) :
    graph2 (H.d k (k + 1)) →L[ℝ] graph2 (H.d (k + 1) (k + 1 + 1)) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ (E (k + 1)) (E (k + 1 + 1))).symm.toContinuousLinearMap ∘L
    ((H.d k (k + 1)).graphSnd.prod 0)).codRestrict _ fun v => by
      obtain ⟨x, rfl, -, -⟩ := (H.d k (k + 1)).exists_toGraphSpace_eq v
      rw [graph2_eq, mem_graphL2]
      exact (LinearPMap.mem_graph_iff _).2 ⟨⟨_, H.mapsTo k (k + 1) (k + 1 + 1) x⟩, rfl,
        H.d_comp_d k (k + 1) (k + 1 + 1) x⟩

theorem graphD_fst (H : Feec.HilbertComplex ℝ (ComplexShape.up ℤ) E) (k : ℤ)
    (v : graph2 (H.d k (k + 1))) :
    ((graphD H k v : WithLp 2 (E (k + 1) × E (k + 1 + 1))).ofLp).1 =
      ((v : WithLp 2 (E k × E (k + 1))).ofLp).2 := rfl

theorem graphD_graphD (H : Feec.HilbertComplex ℝ (ComplexShape.up ℤ) E) (k : ℤ)
    (v : graph2 (H.d k (k + 1))) : graphD H (k + 1) (graphD H k v) = 0 := by
  refine graph2_ext ?_
  change (((graphD H k v : WithLp 2 (E (k + 1) × E (k + 1 + 1))).ofLp).2 : E (k + 1 + 1)) = 0
  rfl

/-- `(φ, d̃φ) ↦ (Sφ, -S d̃φ)` from the graph spaces of the bottom row to those of the top row. -/
def graphS (D : Feec.BGG.HilbertData ℝ (ComplexShape.up ℤ) E Et) (k : ℤ) :
    graph2 (D.Ht.d k (k + 1)) →L[ℝ] graph2 (D.H.d (k + 1) (k + 1 + 1)) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ (E (k + 1)) (E (k + 1 + 1))).symm.toContinuousLinearMap ∘L
    ((D.S k (k + 1) ∘L (D.Ht.d k (k + 1)).graphFst).prod
      (-(D.S (k + 1) (k + 1 + 1) ∘L (D.Ht.d k (k + 1)).graphSnd)))).codRestrict _ fun v => by
      obtain ⟨φ, rfl, -, -⟩ := (D.Ht.d k (k + 1)).exists_toGraphSpace_eq v
      rw [graph2_eq, mem_graphL2]
      exact (LinearPMap.mem_graph_iff _).2 ⟨⟨_, D.S_mapsTo k (k + 1) (k + 1 + 1) φ⟩, rfl,
        D.anticomm k (k + 1) (k + 1 + 1) φ⟩

/-- **The stacked diagram of the domain complexes** of analytic BGG data on `ℤ`. -/
def toDomainDiagram (D : Feec.BGG.HilbertData ℝ (ComplexShape.up ℤ) E Et) :
    BGG.DomainDiagram (fun k => D.H.d k (k + 1)) (fun k => D.Ht.d k (k + 1))
      (fun k => D.S k (k + 1)) where
  d := graphD D.H
  dt := graphD D.Ht
  s := graphS D
  fst_d _ _ := rfl
  fst_dt _ _ := rfl
  fst_s _ _ := rfl
  d_d := graphD_graphD D.H
  dt_dt := graphD_graphD D.Ht
  d_s k v := by
    refine graph2_ext ?_
    change (((graphS D k v : WithLp 2 (E (k + 1) × E (k + 1 + 1))).ofLp).2 : E (k + 1 + 1)) =
      -D.S (k + 1) (k + 1 + 1) ((graphD D.Ht k v : WithLp 2 (Et (k + 1) × Et (k + 1 + 1))).ofLp).1
    rfl

/-- **`s` is bounded below where `S` is, in two consecutive degrees**: `‖(φ, d̃φ)‖² ≤
max(K₁, K₂)² (‖Sφ‖² + ‖S d̃φ‖²)`. -/
theorem antilipschitz_graphS (D : Feec.BGG.HilbertData ℝ (ComplexShape.up ℤ) E Et) {k : ℤ}
    {K₁ K₂ : NNReal} (h₁ : AntilipschitzWith K₁ (D.S k (k + 1)))
    (h₂ : AntilipschitzWith K₂ (D.S (k + 1) (k + 1 + 1))) :
    AntilipschitzWith (max K₁ K₂) (graphS D k) := by
  refine (graphS D k).antilipschitz_of_bound fun v => ?_
  obtain ⟨φ, rfl, -, -⟩ := (D.Ht.d k (k + 1)).exists_toGraphSpace_eq v
  have hv : ‖(D.Ht.d k (k + 1)).toGraphSpace φ‖ ^ 2 =
      ‖(φ : Et k)‖ ^ 2 + ‖D.Ht.d k (k + 1) φ‖ ^ 2 :=
    WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 ((φ : Et k), D.Ht.d k (k + 1) φ))
  have hs : ‖graphS D k ((D.Ht.d k (k + 1)).toGraphSpace φ)‖ ^ 2 =
      ‖D.S k (k + 1) φ‖ ^ 2 + ‖D.S (k + 1) (k + 1 + 1) (D.Ht.d k (k + 1) φ)‖ ^ 2 := by
    have := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (D.S k (k + 1) φ,
      -D.S (k + 1) (k + 1 + 1) (D.Ht.d k (k + 1) φ)))
    rw [norm_neg] at this
    exact this
  have b₁ := ((D.S k (k + 1)).bound_of_antilipschitz h₁ φ).trans
    (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.2 (le_max_left K₁ K₂)) (norm_nonneg _))
  have b₂ := ((D.S (k + 1) (k + 1 + 1)).bound_of_antilipschitz h₂ (D.Ht.d k (k + 1) φ)).trans
    (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.2 (le_max_right K₁ K₂)) (norm_nonneg _))
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [hv, mul_pow, hs, mul_add, ← mul_pow, ← mul_pow]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) b₁ 2) (pow_le_pow_left₀ (norm_nonneg _) b₂ 2)

/-- **`s` is onto modulo `d` where the rows split**: if every `u ∈ D(dᵏ⁺¹)` is `dᵏ p + Sᵏ φ`, then
`R(dᵏ) + R(sᵏ) = Γ(dᵏ⁺¹)` in the graph spaces. -/
theorem sup_range_eq_top_of_exists (D : Feec.BGG.HilbertData ℝ (ComplexShape.up ℤ) E Et)
    {k : ℤ} (h : ∀ u ∈ (D.H.d (k + 1) (k + 1 + 1)).domain,
      ∃ (p : (D.H.d k (k + 1)).domain) (φ : (D.Ht.d k (k + 1)).domain),
        D.H.d k (k + 1) p + D.S k (k + 1) φ = u) :
    LinearMap.range ((toDomainDiagram D).d k : graph2 (D.H.d k (k + 1)) →ₗ[ℝ] _) ⊔
      LinearMap.range ((toDomainDiagram D).s k : graph2 (D.Ht.d k (k + 1)) →ₗ[ℝ] _) = ⊤ := by
  refine eq_top_iff.2 fun w _ => ?_
  obtain ⟨u, rfl, -, -⟩ := (D.H.d (k + 1) (k + 1 + 1)).exists_toGraphSpace_eq w
  obtain ⟨p, φ, e⟩ := h u u.2
  have hmem := Submodule.add_mem_sup
    (LinearMap.mem_range_self ((toDomainDiagram D).d k : graph2 (D.H.d k (k + 1)) →ₗ[ℝ] _)
      (graphEquiv _ p))
    (LinearMap.mem_range_self ((toDomainDiagram D).s k : graph2 (D.Ht.d k (k + 1)) →ₗ[ℝ] _)
      (graphEquiv _ φ))
  convert hmem using 1
  refine graph2_ext ?_
  exact e.symm

/-- `D(d i (c.next i)) ≃ Γ(d i (i + 1))`. -/
def graphDomainEquiv (H : Feec.HilbertComplex ℝ (ComplexShape.up ℤ) E) (i : ℤ) :
    (H.d i ((ComplexShape.up ℤ).next i)).domain ≃ₗ[ℝ] graph2 (H.d i (i + 1)) :=
  (LinearEquiv.ofEq _ _ (by rw [CochainComplex.next])).trans (graphEquiv (H.d i (i + 1)))

/-- **The homology of the bounded complex of the graph spaces is the cohomology of the Hilbert
complex** (`Feec.HilbertComplex.cohomologyEquivOfIso`). -/
def graphHomologyEquiv (H : Feec.HilbertComplex ℝ (ComplexShape.up ℤ) E) (i : ℤ) :
    H.cohomology i ≃ₗ[ℝ] (BGG.ofBounded (graphD H) (graphD_graphD H)).homology i :=
  Feec.HilbertComplex.cohomologyEquivOfIso
    (Feec.HilbertComplex.toModuleCatIso H _ (graphDomainEquiv H) fun i j x => by
      by_cases hij : i + 1 = j
      · subst hij
        refine graph2_ext ?_
        change (H.domainMap i (i + 1) x : E (i + 1)) = H.d i (i + 1) ⟨x, _⟩
        rw [Feec.HilbertComplex.coe_domainMap]
      · rw [CochainComplex.of_d_ne _ _ hij]
        have h0 : H.domainMap i j x = 0 := Subtype.ext (by
          rw [Feec.HilbertComplex.coe_domainMap]
          exact H.apply_eq_zero_of_not_rel hij _)
        rw [h0, map_zero]
        rfl) i

end Domain

/-! ### The diagrams of the challenge are those of `Feec` -/

section Identify

variable {n : ℕ}

/-- `vecOp` of a constant family is the product complex of `Feec`. -/
theorem vecOp_eq_piD {W : ℤ → Type} [∀ k, NormedAddCommGroup (W k)]
    [∀ k, InnerProductSpace ℝ (W k)] [∀ k, CompleteSpace (W k)]
    (H : Feec.HilbertComplex ℝ (ComplexShape.up ℤ) W) {k : ℤ} {A : W k →ₗ.[ℝ] W (k + 1)}
    (hA : H.d k (k + 1) = A) :
    (vecOp fun _ : Fin n => A) = (H.pi (Fin n)).d k (k + 1) := by
  subst hA
  refine LinearPMap.ext ?_ fun x y hxy => ?_
  · ext v
    rw [Feec.HilbertComplex.pi_d, Feec.HilbertComplex.piD_domain,
      Feec.HilbertComplex.mem_piDomain]
    rfl
  · refine PiLp.ext fun a => ?_
    rw [Feec.HilbertComplex.pi_d_apply]
    exact LinearPMap.apply_eq_of_eq rfl _ _ (by rw [hxy])

/-- The exterior product with `dxₐ` of the challenge is `Feec`'s. -/
theorem dxWedge_eq (Ω : Set (Fin n → ℝ)) (k : ℤ) (a : Fin n) :
    dxWedge Ω k a = dxL2 (Ω := Ω) k a := by
  unfold dxWedge dxL2
  rw [wedge_eq]

/-- The div–div connecting map of the challenge is `Feec`'s. -/
theorem dxVec_eq (Ω : Set (Fin n → ℝ)) (k : ℤ) : dxVec Ω k = dxVecL2 (Ω := Ω) k := by
  unfold dxVec dxVecL2
  simp only [dxWedge_eq]

/-- The elasticity connecting map of the challenge is `Feec`'s. -/
theorem crossWedge_eq (Ω : Set (Fin 3 → ℝ)) (k : ℤ) : crossWedge Ω k = crossL2 (Ω := Ω) k := by
  unfold crossWedge crossL2
  simp only [dxWedge_eq]

/-- `dMax` on the cube is `Feec`'s `HΛ(Q)`. -/
theorem dMax_cube_eq (k : ℤ) :
    (formRow 3 (Feec.Models.Cube.FEM.isOpen_cubeDomain 3)).d k (k + 1) = dMax (cube 3) k :=
  (formRow_d _ k).trans (dMax_eq (cube 3) k).symm

/-- `vecOp` of `dMax` on the cube is `Feec`'s `HΛ(Q) ⊗ ℝ³`. -/
theorem vecOp_cube_eq (k : ℤ) :
    (vecRow 3 (Feec.Models.Cube.FEM.isOpen_cubeDomain 3)).d k (k + 1) =
      vecOp fun _ : Fin 3 => dMax (cube 3) k :=
  (vecOp_eq_piD _ (dMax_cube_eq k)).symm

end Identify

end FEEC
