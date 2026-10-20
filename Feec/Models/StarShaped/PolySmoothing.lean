module

public import Feec.Models.StarShaped.FiniteElement
public import Feec.Models.Cube.PolySmoothingEstimates

/-!
# Smoothed projections for the higher-order families on star-shaped domains

Let `Ω ⊆ ℝⁿ` be a bounded domain star-shaped with respect to a ball (`StarDomain`) and `M` a
conforming simplicial mesh of `Ω` that is shape regular and quasi-uniform (`MeshData`). For every
admissible sequence `S` (`Feec.FiniteElement.PolySeq`: `P_{r_k}Λᵏ` or `P_{r_k}⁻Λᵏ` in degree `k`,
including the mixed rows such as `P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ² → P₀Λ³`), the glued spaces
`Vₕ(S, M) ⊆ HΛ(Ω)` and `V̊ₕ(S, M) ⊆ H̊Λ(Ω)` (vanishing boundary DOFs) carry uniformly bounded
smoothed cochain projections. This generalizes the Whitney theory of
`Feec.Models.StarShaped.FiniteElement` to all orders, and the higher-order theory of the
Freudenthal meshes of the cube (`Feec.Models.Cube.PolySmoothingEstimates`) to general meshes.

**Local tools on shape-regular simplices** (`‖B_T‖ ≤ C h_T`, `‖B_T⁻¹‖ ≤ C / h_T`,
`c h_Tⁿ ≤ |det B_T|`):
* *Coefficients of the moments*: the DOF `ℓ_{g,i}(ω) = ∫_{T̂_m} Σₛ ω(F_q ξ)ₛ cₛ(ξ) dξ`
  (`Feec.FiniteElement.PolySeq.dof_eq_integral`) has `Σₛ |cₛ| ≤ D h_Tᵏ` (`PolyCoeffBound`,
  `exists_polyCoeffBound`), hence `|ℓ_{g,i}(ω)| ≤ D h_Tᵏ sup_T |ω|` (`abs_polyDof_le`).
* *DOF estimate* (`PolyDofBound`, `exists_polyDofBound`): `h_Tᵏ sup_T ‖z‖ ≤ B max |ℓ_{g,i}(z)|`
  on `P(T)ᵏ`. It is `Feec.FiniteElement.exists_dof_bound_of_le_polySpace` for the unisolvent DOFs
  of the reference simplex (`PolySeq.isUnisolvent_dof`), transported along the reference map
  `F_T` (`refPull`): the lexicographic parametrizations of `ĝ` and of `F_T(ĝ)` differ by a
  vertex permutation `π`, so a moment of `F_T^* z` is `sign π` times a moment of `z` against the
  reparametrized test form `A_{π⁻¹}^* ηᵢ` (`abs_dof_refPull_le`, from
  `Feec.Models.Parallelepiped.vertexMoment_comp_perm`), which is a combination of the DOFs of
  `F_T(ĝ)` with coefficients bounded uniformly in `π` (`permConst`, `abs_vertexMoment_le_of_dof`).
* *Interpolation error* of the canonical interpolant `Π_T` of `S` (the moment DOFs on the faces
  of `T`; [Ciarlet2002], Thm 3.1.4; [Arnold2018], Ch. 7): for `P_sΛᵏ ⊆ P(T)ᵏ`,
  `sup_T ‖w - Π_T w‖ ≤ (1 + B D) h_T^{s+1} sup_T ‖D^{s+1} w‖` (`norm_sub_polyLocalInterp_le`),
  `‖w - Π_T w‖²_{L²(T)} ≲ h_Tⁿ (h_T^{s+1} sup_T ‖D^{s+1} w‖)²`
  (`formL2Sq_sub_polyLocalInterp_le`) and, through `d Π_T = Π_T d`, the same for `dw - d Π_T w`
  (`norm_extDeriv_sub_polyLocalInterp_le`); existence forms with constants depending only on
  `n, S, k, C` (`exists_norm_sub_polyLocalInterp_le`, `exists_formL2Sq_sub_polyLocalInterp_le`,
  `exists_formL2Sq_extDeriv_sub_polyLocalInterp_le`). The proof is the Bramble–Hilbert argument
  (Taylor polynomial `exists_polySpace_near_diam` reproduced by `Π_T`, stability of `Π_T` from the
  two bounds above); the reference transport enters through the DOF estimate.
* *Inverse estimates* (`exists_polyInvBound`, from
  `Feec.FiniteElement.exists_inverse_bound_of_le_polySpace`), in terms of the mesh size on a
  quasi-uniform mesh (`InvBoundV`, `invBoundV_of`), and the mesh-level DOF estimate
  `abs_le_of_abs_polyDof_le`.

**The smoothed-projection estimates** ([AFW2010], §5.4; [ChristiansenWinther2008]), for the
smoothers `pMax`, `pMin` of `Feec.Models.StarShaped.FiniteElement` at scale `γ h`:
* *uniform `L²` bound* of `Q = Π_h R` (`sum_integral_sq_polyInterp_le`,
  `exists_norm_polySmoothedInterp_le`): Jensen's inequality for the mollifier, the DOF stability,
  the DOF estimate and bounded overlap (`sum_locMass_le`);
* *closeness* `‖v - Q v‖ ≤ ½ ‖v‖` on `Vₕ` and `V̊ₕ` (`exists_polyGamma`): the DOF integrand of
  `v - Q v` at points of a face `g` (any dimension, lexicographic parametrization) with
  barycentric weights `≥ θ` is `O(γ)`, since every simplex sampled by the smoother contains `g`
  (`PolyGeomOK`, from the geometric lemma `StarGeom.subset_vertexSet_of_segments`), where the
  traces of the local fields agree (`Feec.Models.Cube.FEM.Poly.pullback_eq_of_mem_globalSpace`),
  and samples outside `Ω` are controlled by `PolySampleOK`; the boundary layer of the reference
  face has measure `O(θ)` (`sqrt_mul_abs_polyIntegrand_le`, `sqrt_mul_abs_polyDof_err_le`,
  `sum_integral_sq_sub_polyInterp_le`, `norm_sq_sub_polySmoothedInterp_le`). Both conditions hold
  for both families (`polyGeomOK_of_isMaximal`, `polyGeomOK_of_isMinimal`,
  `polySampleOK_of_isMaximal`; `polySampleOK_of_isMinimal` from
  `StarGeom.exists_isBoundaryFacet_of_near`: the DOFs of all subfaces of a boundary facet vanish
  on `V̊ₕ`);
* hence **uniformly bounded cochain projections** onto `Vₕ(S, M)` and `V̊ₕ(S, M)`, in `L²` and in
  every graph norm, with constants depending only on `n, S, C, c, q, s₀, R` (chosen after `s₀`
  and `R`; the mathematical dependence through `s₀ / R` alone is not formalized)
  (`exists_uniform_polyCochainProjection`, `exists_uniform_polyCochainProjectionMin`; on a mesh
  family, with the complexes `MeshFamily.poly`, `MeshFamily.polyMin`:
  `MeshFamily.exists_uniform_polyProj`, `MeshFamily.exists_uniform_polyProjMin`).

Everything in this file is proved with no hypothesis beyond the geometry (star-shapedness with
respect to a ball, shape regularity, quasi-uniformity). The finite element theorems built on it
are in `Feec.Models.StarShaped.PolyFiniteElement`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.4 (smoothed projections)
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §4.5–4.6 (the moment degrees of freedom)
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.1–3.2
  (shape-regular families, inverse inequalities), Thm 3.1.4 (interpolation error)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (approximation
  estimates)
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset Filter Topology
open scoped ContDiff

namespace Feec.Models.StarShaped

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex ExteriorFibre Feec.Models.Cube

variable {n : ℕ}

/-! ### Local tools on shape-regular simplices -/

section Local

variable (S : PolySeq)

/-- The edge vectors of the lexicographic parametrization of a face of `T` are bounded by
`h_T`. -/
theorem abs_simplexMatrix_lexEnum_le_diam {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T) {m : ℕ} (hg : #g = m + 1) (i : Fin n)
    (l : Fin m) : |simplexMatrix (lexEnum g m) i l| ≤ diam T := by
  have hmem : ∀ a, lexEnum g m a ∈ T.closedInterior := fun a =>
    vertexSet_subset_closedInterior' T (hgT (lexEnum_mem hg a))
  have h1 := Metric.dist_le_diam_of_mem T.isCompact_closedInterior.isBounded (hmem l.succ)
    (hmem 0)
  rw [dist_eq_norm] at h1
  refine le_trans ?_ h1
  have h := norm_le_pi_norm (lexEnum g m l.succ - lexEnum g m 0) i
  rwa [Real.norm_eq_abs, Pi.sub_apply] at h

/-- **The coefficient fields of the degrees of freedom are `O(h_Tᵏ)`** on every simplex, with one
constant: `Σₛ |cₛ(ξ)| ≤ D h_Tᵏ` for the moment `ℓ_{g,i}(ψ) = ∫_{T̂_m} Σₛ ψ(F_q ξ)ₛ cₛ(ξ) dξ`
(`Feec.FiniteElement.PolySeq.dof_eq_integral`) of a face `g` of `T`. -/
def PolyCoeffBound (n k : ℕ) (D : ℝ) : Prop :=
  ∀ {T : Affine.Simplex ℝ (Fin n → ℝ) n} {g : Finset (Fin n → ℝ)}, g ⊆ vertexSet T →
    ∀ (i : S.DofIdx g k), ∀ ξ ∈ FiniteElement.refSimplex (#g - 1),
      ∑ s, |dofCoeff (lexEnum g (#g - 1)) (S.testBasis k (#g - 1) i.1 : FormField (#g - 1)) k
        ξ s| ≤ D * diam T ^ k

theorem exists_polyCoeffBound (k : ℕ) : ∃ D, 0 ≤ D ∧ PolyCoeffBound S n k D := by
  obtain ⟨M, hM0, hM⟩ := FEM.Poly.exists_testBound (n := n) S k
  refine ⟨2 ^ n * (2 ^ n * k.factorial) * M, by positivity, fun {T g} hgT i ξ hξ => ?_⟩
  have hne := i.2
  have hg : #g = (#g - 1) + 1 := (Nat.succ_pred_eq_of_pos (card_pos.2 hne)).symm
  have hgn : #g - 1 ≤ n := by
    have := Finset.card_le_card hgT
    rw [card_vertexSet] at this; omega
  refine (sum_abs_dofCoeff_le (diam_nonneg T) (abs_simplexMatrix_lexEnum_le_diam hgT hg) _ k
    ξ).trans ?_
  have h2 : (2 : ℝ) ^ (#g - 1) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hgn
  have hη := hM (#g - 1) hgn i.1 ξ hξ
  have hh := pow_nonneg (diam_nonneg T) k
  calc 2 ^ n * (2 ^ (#g - 1) * (k.factorial * diam T ^ k)) *
        ‖(S.testBasis k (#g - 1) i.1 : FormField (#g - 1)) ξ‖
      ≤ 2 ^ n * (2 ^ n * (k.factorial * diam T ^ k)) * M := by
        gcongr
    _ = _ := by ring

/-- **Stability of the degrees of freedom in the sup norm** on any simplex:
`|ℓ_{g,i}(ψ)| ≤ D h_Tᵏ sup_T |ψ|`. -/
theorem abs_polyDof_le {k : ℕ} {D : ℝ} (hD : PolyCoeffBound S n k D)
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T)
    (i : S.DofIdx g k) (ψ : contForms n) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ T.closedInterior, ∀ s, |(ψ : FormField n) x s| ≤ B) :
    |S.dof g k i ψ| ≤ D * diam T ^ k * B := by
  have hne := i.2
  have hg : #g = (#g - 1) + 1 := (Nat.succ_pred_eq_of_pos (card_pos.2 hne)).symm
  set q := lexEnum g (#g - 1)
  set η := (S.testBasis k (#g - 1) i.1 : FormField (#g - 1))
  rw [S.dof_eq_integral]
  have h0 : (0 : Fin (#g - 1) → ℝ) ∈ FiniteElement.refSimplex (#g - 1) := fun a => by
    refine Fin.cases ?_ (fun l => ?_) a
    · simp
    · simp [refBary]
  have hD0 : 0 ≤ D * diam T ^ k :=
    (Finset.sum_nonneg fun s _ => abs_nonneg _).trans (hD hgT i 0 h0)
  have hpt : ∀ ξ ∈ FiniteElement.refSimplex (#g - 1),
      ‖∑ s, (ψ : FormField n) (simplexMap q ξ) s * dofCoeff q η k ξ s‖ ≤ D * diam T ^ k * B := by
    intro ξ hξ
    rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ s, |(ψ : FormField n) (simplexMap q ξ) s * dofCoeff q η k ξ s|
        ≤ ∑ s, B * |dofCoeff q η k ξ s| := Finset.sum_le_sum fun s _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right
            (hB _ (FEM.Poly.simplexMap_lexEnum_mem hgT hg hξ) s) (abs_nonneg _)
      _ = B * ∑ s, |dofCoeff q η k ξ s| := by rw [Finset.mul_sum]
      _ ≤ B * (D * diam T ^ k) := mul_le_mul_of_nonneg_left (hD hgT i ξ hξ) hB0
      _ = D * diam T ^ k * B := by ring
  rw [← Real.norm_eq_abs]
  refine (norm_setIntegral_le_of_norm_le_const (volume_refSimplex_lt_top _) hpt).trans ?_
  calc D * diam T ^ k * B * volume.real (FiniteElement.refSimplex (#g - 1))
      ≤ D * diam T ^ k * B * 1 :=
        mul_le_mul_of_nonneg_left (FEM.Poly.volume_real_refSimplex_le_one _) (mul_nonneg hD0 hB0)
    _ = _ := mul_one _

/-! #### The degrees of freedom under the reference map -/

/-- The test form `ηᵢ` reparametrized by a vertex permutation `π` of the reference `m`-simplex:
`A_{π⁻¹}^* ηᵢ`. -/
def permTest (k m : ℕ) (π : Equiv.Perm (Fin (m + 1)))
    (i : Fin (Module.finrank ℝ (S.test k m))) : FormField m :=
  affinePullback (simplexMatrix (refVertex m ∘ ⇑(π⁻¹ : Equiv.Perm (Fin (m + 1)))))
    (refVertex m ((π⁻¹ : Equiv.Perm (Fin (m + 1))) 0)) (S.testBasis k m i : FormField m)

theorem permTest_mem (k m : ℕ) (π : Equiv.Perm (Fin (m + 1)))
    (i : Fin (Module.finrank ℝ (S.test k m))) : permTest S k m π i ∈ S.test k m :=
  Parallelepiped.affinePullback_mem_test S _ _ k (S.testBasis k m i).2

/-- The size of the reparametrized test forms in the basis of the test forms, summed over all
permutations and basis elements. -/
def permConst (k m : ℕ) : ℝ :=
  ∑ π : Equiv.Perm (Fin (m + 1)), ∑ i, ∑ l,
    |(S.testBasis k m).repr ⟨permTest S k m π i, permTest_mem S k m π i⟩ l|

theorem permConst_nonneg (k m : ℕ) : 0 ≤ permConst S k m :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- **A moment against a test form is controlled by the degrees of freedom of the face**:
`|∫ F_q^* ψ_k ∧ η| ≤ (Σₗ |ηₗ|) max_i |ℓ_{g,i}(ψ)|` with `ηₗ` the coordinates of `η` in the
basis of the test forms. -/
theorem abs_vertexMoment_le_of_dof {g : Finset (Fin n → ℝ)} {m : ℕ} (hg : #g = m + 1) {k : ℕ}
    {η : FormField m} (hη : η ∈ S.test k m) (ψ : contForms n) {D' : ℝ}
    (hD : ∀ i : S.DofIdx g k, |S.dof g k i ψ| ≤ D') :
    |vertexMoment (lexEnum g m) η (degField k ψ)| ≤
      (∑ l, |(S.testBasis k m).repr ⟨η, hη⟩ l|) * D' := by
  obtain rfl : m = #g - 1 := by omega
  have hne : g.Nonempty := card_pos.1 (by omega)
  set b := S.testBasis k (#g - 1)
  conv_lhs => rw [eq_sum_repr_basis b hη]
  rw [vertexMoment_sum_smul_right _ _ _ (fun l => S.continuous_testBasis k _ l)
    (continuous_degField k ψ.2), Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hD ⟨l, hne⟩) (abs_nonneg _)

/-- **The degrees of freedom of the reference pullback** `F_T^* z` on a face `ĝ` are
controlled by the degrees of freedom of `z` on the face `F_T(ĝ)` of `T`: the two lexicographic
parametrizations differ by a vertex permutation `π`, the moment changes by `sign π` and the test
form by `A_{π⁻¹}^*` (`Feec.Models.Parallelepiped.vertexMoment_comp_perm`). -/
theorem abs_dof_refPull_le (T : Affine.Simplex ℝ (Fin n → ℝ) n) {g : Finset (Fin n → ℝ)}
    {k : ℕ} (i : S.DofIdx g k) {z : FormField n} (hz : Continuous z) {D' : ℝ}
    (hD : ∀ i' : S.DofIdx (g.image T.refMap) k,
      |S.dof (g.image T.refMap) k i' ⟨z, hz⟩| ≤ D') :
    |S.dof g k i ⟨refPull T z, continuous_refPull T hz⟩| ≤ permConst S k (#g - 1) * D' := by
  set m := #g - 1
  have hg : #g = m + 1 := by have := card_pos.2 i.2; omega
  have hinjr : Function.Injective (T.refMap : (Fin n → ℝ) → Fin n → ℝ) := T.refMap_injective
  have hg' : #(g.image T.refMap) = m + 1 := by rw [card_image_of_injective _ hinjr, hg]
  set q := lexEnum g m
  set q' := lexEnum (g.image T.refMap) m
  have hinj : Function.Injective fun l => affine (simplexMatrix T.points) (T.points 0) (q l) :=
    fun l l' h => by
      simp only [affine_simplexMatrix_eq_refMap] at h
      exact lexEnum_injective hg (hinjr h)
  have hran : Set.range (fun l => affine (simplexMatrix T.points) (T.points 0) (q l)) =
      Set.range q' := by
    rw [range_lexEnum hg', Finset.coe_image, ← range_lexEnum hg, ← Set.range_comp]
    simp only [affine_simplexMatrix_eq_refMap]
    rfl
  obtain ⟨π, hπ⟩ := exists_perm_comp_eq hinj (lexEnum_injective hg') hran
  have he : S.dof g k i ⟨refPull T z, continuous_refPull T hz⟩ =
      ((Equiv.Perm.sign π : ℤ) : ℝ) * vertexMoment q' (permTest S k m π i.1)
        (degField k (⟨z, hz⟩ : contForms n)) := by
    change vertexMoment q (S.testBasis k m i.1 : FormField m)
      (degField k (affinePullback (simplexMatrix T.points) (T.points 0) z)) = _
    rw [Parallelepiped.degField_affinePullback, Parallelepiped.vertexMoment_affinePullback, hπ,
      Parallelepiped.vertexMoment_comp_perm]
    rfl
  have hsign : |((Equiv.Perm.sign π : ℤ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  have h1 := abs_vertexMoment_le_of_dof S hg' (permTest_mem S k m π i.1) ⟨z, hz⟩ hD
  have h2 : ∑ l, |(S.testBasis k m).repr ⟨permTest S k m π i.1, permTest_mem S k m π i.1⟩ l| ≤
      permConst S k m := by
    have hπ' := Finset.single_le_sum (f := fun π : Equiv.Perm (Fin (m + 1)) => ∑ i, ∑ l,
      |(S.testBasis k m).repr ⟨permTest S k m π i, permTest_mem S k m π i⟩ l|)
      (fun π _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.mem_univ π)
    have hi := Finset.single_le_sum (f := fun i => ∑ l,
      |(S.testBasis k m).repr ⟨permTest S k m π i, permTest_mem S k m π i⟩ l|)
      (fun i _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i.1)
    exact hi.trans hπ'
  have hD0 : 0 ≤ D' := by
    have hne' : (g.image T.refMap).Nonempty := card_pos.1 (by omega)
    have h0 : 0 < Module.finrank ℝ (S.test k (#(g.image T.refMap) - 1)) := by
      rw [show #(g.image T.refMap) - 1 = m by omega]
      exact (Fin.pos_iff_nonempty.2 ⟨i.1⟩)
    exact (abs_nonneg _).trans (hD ⟨⟨0, h0⟩, hne'⟩)
  rw [he, abs_mul, hsign, one_mul]
  exact h1.trans (mul_le_mul_of_nonneg_right h2 hD0)

/-- **The DOF estimate on shape-regular simplices** for an admissible sequence: if the degrees of
freedom of `z ∈ P(T)ᵏ` on the faces of `T` are bounded by `D'`, then `h_Tᵏ sup_T ‖z‖ ≤ B D'`. -/
def PolyDofBound (n k : ℕ) (C c B : ℝ) : Prop :=
  ∀ {Sset : Set (Affine.Simplex ℝ (Fin n → ℝ) n)}, IsShapeRegular Sset C c → ∀ T ∈ Sset,
    0 < diam T → ∀ {z : FormField n} (hz : z ∈ S.space n k) {D' : ℝ}, 0 ≤ D' →
      (∀ g ⊆ vertexSet T, ∀ i : S.DofIdx g k,
        |S.dof g k i ⟨z, S.space_le_contForms n k hz⟩| ≤ D') →
      ∀ x ∈ T.closedInterior, diam T ^ k * ‖z x‖ ≤ B * D'

/-- **The DOF estimate on shape-regular simplices**, from the unisolvence of the degrees of freedom
on the reference simplex (`Feec.FiniteElement.exists_dof_bound_of_le_polySpace`) and the
naturality of the moments under `F_T` (`abs_dof_refPull_le`). -/
theorem exists_polyDofBound (k : ℕ) (C c : ℝ) : ∃ B, 0 ≤ B ∧ PolyDofBound S n k C c B := by
  classical
  set J := Σ g : (vertexSet (Mesh.refSimplex n)).powerset, S.DofIdx (g : Finset (Fin n → ℝ)) k
  set ℓ : J → S.space n k →ₗ[ℝ] ℝ := fun p =>
    S.dof (p.1 : Finset (Fin n → ℝ)) k p.2 ∘ₗ Submodule.inclusion (S.space_le_contForms n k)
  have hℓ : Function.Injective (LinearMap.pi ℓ) := (S.isUnisolvent_dof (Mesh.refSimplex n) k).1
  obtain ⟨B₀, hB₀, hB⟩ := exists_dof_bound_of_le_polySpace (S.space_le_polySpace k)
    (fun B b u hu => Parallelepiped.affinePullback_mem_space_poly S B b k hu) ℓ hℓ (C := C)
    (c := c)
  set Kc := ∑ m ∈ Finset.range (n + 1), permConst S k m
  have hKc0 : 0 ≤ Kc := Finset.sum_nonneg fun m _ => permConst_nonneg S k m
  have hKc : ∀ m ≤ n, permConst S k m ≤ Kc := fun m hm =>
    Finset.single_le_sum (f := fun m => permConst S k m) (fun m _ => permConst_nonneg S k m)
      (Finset.mem_range.2 (by omega))
  refine ⟨B₀ * (Fintype.card J * Kc), by positivity,
    fun {Sset} hS T hT hh z hz D' hD0 hD x hx => ?_⟩
  refine (hB hS T hT hh z hz x hx).trans ?_
  have hterm : ∀ p : J, |ℓ p ⟨refPull T z, Parallelepiped.affinePullback_mem_space_poly S _ _ k
      hz⟩| ≤ Kc * D' := by
    intro p
    have hsub : (p.1 : Finset (Fin n → ℝ)).image T.refMap ⊆ vertexSet T :=
      image_refMap_subset_vertexSet T (Finset.mem_powerset.1 p.1.2)
    have hp := abs_dof_refPull_le S T p.2 (S.space_le_contForms n k hz) (D' := D')
      (fun i' => hD _ hsub i')
    have hle : #(p.1 : Finset (Fin n → ℝ)) - 1 ≤ n := by
      have := Finset.card_le_card (Finset.mem_powerset.1 p.1.2)
      rw [card_vertexSet] at this; omega
    exact hp.trans (mul_le_mul_of_nonneg_right (hKc _ hle) hD0)
  calc B₀ * ∑ j, |ℓ j ⟨refPull T z, Parallelepiped.affinePullback_mem_space_poly S _ _ k hz⟩|
      ≤ B₀ * ∑ _j : J, Kc * D' :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => hterm p) hB₀
    _ = B₀ * (Fintype.card J * Kc) * D' := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-! #### The interpolation error on shape-regular simplices -/

/-- **Taylor approximation on a simplex**: for a `C^{s+1}` degree-`k` field `w` with
`‖D^{s+1} w‖ ≤ M` on `T`, the degree-`k` part `P` of its Taylor polynomial of order `s` at a
vertex lies in `P_sΛᵏ` and `‖w - P‖ ≤ h_T^{s+1} M` on `T`. -/
theorem exists_polySpace_near_diam {k s : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    {w : FormField n} (hw : ContDiff ℝ (s + 1) w) (hdeg : ∀ x, IsDeg k (w x)) {M : ℝ}
    (hM : ∀ y ∈ T.closedInterior, ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ M) :
    ∃ P ∈ polySpace n s k, ∀ x ∈ T.closedInterior, ‖w x - P x‖ ≤ diam T ^ (s + 1) * M := by
  set x₀ := T.points 0
  have hx₀ : x₀ ∈ T.closedInterior := T.point_mem_closedInterior 0
  refine ⟨degPartField k (taylorPoly w x₀ (s + 1)), FEM.Poly.degPartField_taylorPoly_mem w x₀,
    fun x hx => ?_⟩
  have htay := norm_iteratedFDeriv_sub_taylorPoly_le (k := s + 1) (f := w) (U := Set.univ)
    (K := T.closedInterior) (x₀ := x₀) (d := diam T) (M := M) isOpen_univ
    (Set.subset_univ _) (convex_closedInterior _) hx₀ (hw.contDiffOn)
    (fun y hy => by
      rw [← dist_eq_norm]
      exact Metric.dist_le_diam_of_mem T.isCompact_closedInterior.isBounded hy hx₀) hM hx
    (Nat.zero_le _)
  rw [norm_iteratedFDeriv_zero, Nat.sub_zero] at htay
  have e : w x - degPartField k (taylorPoly w x₀ (s + 1)) x =
      degPart k (w x - taylorPoly w x₀ (s + 1) x) := by
    have h2 := congrFun (degPartField_sub k w (taylorPoly w x₀ (s + 1))) x
    rw [degPartField_of_isDeg hdeg] at h2
    exact h2.symm
  rw [e]
  exact (norm_degPart_le k _).trans htay

/-- **The pointwise interpolation error of the canonical interpolant `Π_T` of an admissible
sequence on a shape-regular simplex** ([Ciarlet2002], Thm 3.1.4; [Arnold2018], Ch. 7): if
`P_sΛᵏ ⊆ P(T)ᵏ` and `‖D^{s+1} w‖ ≤ M` on `T`, then
`‖w - Π_T w‖ ≤ (1 + B D) h_T^{s+1} M` on `T`, with `B` the DOF constant of the shape-regular family
and `D` the coefficient constant of the degrees of freedom (Bramble–Hilbert through the DOF bound
and the DOF stability). -/
theorem norm_sub_polyLocalInterp_le {k s : ℕ} (hs : polySpace n s k ≤ S.space n k)
    {C c B D : ℝ} (hB : PolyDofBound S n k C c B) (hD0 : 0 ≤ D) (hD : PolyCoeffBound S n k D)
    {Sset : Set (Affine.Simplex ℝ (Fin n → ℝ) n)} (hS : IsShapeRegular Sset C c)
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ Sset) (hh : 0 < diam T) {w : FormField n}
    (hw : ContDiff ℝ (s + 1) w) (hdeg : ∀ x, IsDeg k (w x)) {M : ℝ}
    (hM : ∀ y ∈ T.closedInterior, ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ M)
    {x : Fin n → ℝ} (hx : x ∈ T.closedInterior) :
    ‖w x - (((polyElement n S).localInterp T k ⟨w, hw.continuous⟩ :
      (polyElement n S).space T k) : FormField n) x‖ ≤ (1 + B * D) * (diam T ^ (s + 1) * M) := by
  obtain ⟨P, hP, hwP⟩ := exists_polySpace_near_diam hw hdeg hM
  have hPS : P ∈ S.space n k := hs hP
  set e := diam T ^ (s + 1) * M
  have he : 0 ≤ e := (norm_nonneg _).trans (hwP x hx)
  set Iw : (polyElement n S).space T k := (polyElement n S).localInterp T k ⟨w, hw.continuous⟩
  have hIw : (Iw : FormField n) ∈ S.space n k := Iw.2
  set z : FormField n := (Iw : FormField n) - P
  have hz : z ∈ S.space n k := Submodule.sub_mem _ hIw hPS
  have hwPc : Continuous (w - P) :=
    hw.continuous.sub (PolyKind.contDiff_of_mem_space hPS).continuous
  have hdof : ∀ g ⊆ vertexSet T, ∀ i : S.DofIdx g k,
      |S.dof g k i ⟨z, S.space_le_contForms n k hz⟩| ≤ D * diam T ^ k * e := by
    intro g hgT i
    have e1 : S.dof g k i ⟨(Iw : FormField n), S.space_le_contForms n k hIw⟩ =
        S.dof g k i ⟨w, hw.continuous⟩ :=
      (polyElement n S).localDof_localInterp T k ⟨w, hw.continuous⟩ g hgT i
    have e2 : S.dof g k i ⟨z, S.space_le_contForms n k hz⟩ = S.dof g k i ⟨w - P, hwPc⟩ := by
      have h1 : (⟨z, S.space_le_contForms n k hz⟩ : contForms n) =
          ⟨(Iw : FormField n), S.space_le_contForms n k hIw⟩ -
            ⟨P, S.space_le_contForms n k hPS⟩ := rfl
      have h2 : (⟨w - P, hwPc⟩ : contForms n) = ⟨w, hw.continuous⟩ -
          ⟨P, S.space_le_contForms n k hPS⟩ := rfl
      rw [h1, h2, map_sub, map_sub, e1]
    rw [e2]
    refine abs_polyDof_le S hD hgT i _ he fun y hy t => ?_
    have := norm_le_pi_norm ((w - P) y) t
    rw [Real.norm_eq_abs] at this
    exact this.trans (hwP y hy)
  have hzb := hB hS T hT hh hz (by positivity) hdof x hx
  have hzx : ‖z x‖ ≤ B * D * e := by
    have hk : 0 < diam T ^ k := pow_pos hh k
    refine le_of_mul_le_mul_left (hzb.trans (le_of_eq ?_)) hk
    ring
  have h1 := hwP x hx
  calc ‖w x - (Iw : FormField n) x‖ = ‖(w x - P x) - z x‖ := by
        congr 1; simp only [z, Pi.sub_apply]; abel
    _ ≤ ‖w x - P x‖ + ‖z x‖ := norm_sub_le _ _
    _ ≤ e + B * D * e := add_le_add h1 hzx
    _ = (1 + B * D) * e := by ring

/-- **The `L²(T)` interpolation error of `Π_T` on a shape-regular simplex**:
`‖w - Π_T w‖²_{L²(T)} ≤ 2ⁿ (2 h_T)ⁿ ((1 + B D) h_T^{s+1} sup_T ‖D^{s+1} w‖)²`, i.e.
`‖w - Π_T w‖_{L²(T)} ≲ h_T^{n/2} h_T^{s+1} sup_T ‖D^{s+1} w‖`. -/
theorem formL2Sq_sub_polyLocalInterp_le {k s : ℕ} (hs : polySpace n s k ≤ S.space n k)
    {C c B D : ℝ} (hB : PolyDofBound S n k C c B) (hD0 : 0 ≤ D) (hD : PolyCoeffBound S n k D)
    {Sset : Set (Affine.Simplex ℝ (Fin n → ℝ) n)} (hS : IsShapeRegular Sset C c)
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ Sset) (hh : 0 < diam T) {w : FormField n}
    (hw : ContDiff ℝ (s + 1) w) (hdeg : ∀ x, IsDeg k (w x)) {M : ℝ}
    (hM : ∀ y ∈ T.closedInterior, ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ M) :
    formL2Sq T.closedInterior (w - (((polyElement n S).localInterp T k ⟨w, hw.continuous⟩ :
      (polyElement n S).space T k) : FormField n)) ≤
      2 ^ n * (2 * diam T) ^ n * ((1 + B * D) * (diam T ^ (s + 1) * M)) ^ 2 := by
  have h := formL2Sq_le_of_norm_le (volume_closedInterior_lt_top T) (u := w -
    (((polyElement n S).localInterp T k ⟨w, hw.continuous⟩ : (polyElement n S).space T k) :
      FormField n)) (B := (1 + B * D) * (diam T ^ (s + 1) * M))
    fun x hx => norm_sub_polyLocalInterp_le S hs hB hD0 hD hS hT hh hw hdeg hM hx
  refine h.trans ?_
  rw [Fintype.card_finset, Fintype.card_fin]
  push_cast
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (volume_real_closedInterior_le T) (by positivity)) (sq_nonneg _)

/-- **The interpolation error of `d Π_T w = Π_T dw` on a shape-regular simplex** (the commuting
property `Feec.FiniteElement.LocalElement.localInterp_extDeriv`): if `P_sΛᵏ⁺¹ ⊆ P(T)ᵏ⁺¹` and
`‖D^{s+1} dw‖ ≤ M'` on `T`, then `‖dw - d Π_T w‖ ≤ (1 + B' D') h_T^{s+1} M'` on `T`. -/
theorem norm_extDeriv_sub_polyLocalInterp_le {k s : ℕ}
    (hs : polySpace n s (k + 1) ≤ S.space n (k + 1)) {C c B D : ℝ}
    (hB : PolyDofBound S n (k + 1) C c B) (hD0 : 0 ≤ D)
    (hD : PolyCoeffBound S n (k + 1) D)
    {Sset : Set (Affine.Simplex ℝ (Fin n → ℝ) n)} (hS : IsShapeRegular Sset C c)
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ Sset) (hh : 0 < diam T) {w : FormField n}
    (hw : ContDiff ℝ (s + 2) w) (hdeg : ∀ x, IsDeg k (w x)) {M : ℝ}
    (hM : ∀ y ∈ T.closedInterior, ‖iteratedFDeriv ℝ (s + 1) (extDeriv w) y‖ ≤ M)
    {x : Fin n → ℝ} (hx : x ∈ T.closedInterior) :
    ‖extDeriv w x - extDeriv (((polyElement n S).localInterp T k ⟨w, hw.continuous⟩ :
      (polyElement n S).space T k) : FormField n) x‖ ≤
        (1 + B * D) * (diam T ^ (s + 1) * M) := by
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by exact_mod_cast Nat.le_add_left 1 (s + 1))
  have hdw : ContDiff ℝ (s + 1) (extDeriv w) := contDiff_extDeriv (m := s + 1) (by
    exact_mod_cast hw)
  have hdeg' : ∀ x, IsDeg (k + 1) (extDeriv w x) := fun x => IsDeg.extDeriv hdeg x
  have hcomm := (polyElement n S).localInterp_extDeriv T k ⟨w, hw1⟩
  have e : extDeriv (((polyElement n S).localInterp T k ⟨w, hw.continuous⟩ :
      (polyElement n S).space T k) : FormField n) =
      (((polyElement n S).localInterp T (k + 1) ⟨extDeriv w, hdw.continuous⟩ :
        (polyElement n S).space T (k + 1)) : FormField n) := by
    rw [show (⟨extDeriv w, hdw.continuous⟩ : contForms n) =
      extDerivC1 (⟨w, hw1⟩ : c1Forms n) from rfl, hcomm]
    rfl
  rw [e]
  exact norm_sub_polyLocalInterp_le S hs hB hD0 hD hS hT hh hdw hdeg' hM hx

/-- **The interpolation error of `Π_T` on shape-regular simplices, existence form**: the transfer
of the homothetic estimate `Feec.FiniteElement.exists_norm_sub_polyInterp_le` to every simplex of a
shape-regular family, `sup_T ‖w - Π_T w‖ ≤ K h_T^{s+1} sup_T ‖D^{s+1} w‖`, with `K` depending
only on `n, S, k, C` (through the DOF estimate `exists_polyDofBound`, which uses the reference
pullback `F_T^*` and the naturality of the moments). -/
theorem exists_norm_sub_polyLocalInterp_le {k s : ℕ} (hs : polySpace n s k ≤ S.space n k)
    (C c : ℝ) : ∃ K, 0 ≤ K ∧ ∀ {Sset : Set (Affine.Simplex ℝ (Fin n → ℝ) n)},
      IsShapeRegular Sset C c → ∀ T ∈ Sset, 0 < diam T → ∀ {w : FormField n}
      (hw : ContDiff ℝ (s + 1) w), (∀ x, IsDeg k (w x)) → ∀ {M : ℝ},
      (∀ y ∈ T.closedInterior, ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ M) →
      ∀ x ∈ T.closedInterior, ‖w x - (((polyElement n S).localInterp T k ⟨w, hw.continuous⟩ :
        (polyElement n S).space T k) : FormField n) x‖ ≤ K * (diam T ^ (s + 1) * M) := by
  obtain ⟨B, hB0, hB⟩ := exists_polyDofBound S k C c
  obtain ⟨D, hD0, hD⟩ := exists_polyCoeffBound (n := n) S k
  exact ⟨1 + B * D, by positivity, fun hS T hT hh w hw hdeg M hM x hx =>
    norm_sub_polyLocalInterp_le S hs hB hD0 hD hS hT hh hw hdeg hM hx⟩

/-- **The `L²(T)` interpolation error of `Π_T` on shape-regular simplices, existence form** (the
transfer of `Feec.FiniteElement.exists_formL2Sq_sub_polyInterp_le`):
`‖w - Π_T w‖²_{L²(T)} ≤ K h_Tⁿ (h_T^{s+1} sup_T ‖D^{s+1} w‖)²`. -/
theorem exists_formL2Sq_sub_polyLocalInterp_le {k s : ℕ} (hs : polySpace n s k ≤ S.space n k)
    (C c : ℝ) : ∃ K, 0 ≤ K ∧ ∀ {Sset : Set (Affine.Simplex ℝ (Fin n → ℝ) n)},
      IsShapeRegular Sset C c → ∀ T ∈ Sset, 0 < diam T → ∀ {w : FormField n}
      (hw : ContDiff ℝ (s + 1) w), (∀ x, IsDeg k (w x)) → ∀ {M : ℝ},
      (∀ y ∈ T.closedInterior, ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ M) →
      formL2Sq T.closedInterior (w - (((polyElement n S).localInterp T k ⟨w, hw.continuous⟩ :
        (polyElement n S).space T k) : FormField n)) ≤
        K * diam T ^ n * (diam T ^ (s + 1) * M) ^ 2 := by
  obtain ⟨B, hB0, hB⟩ := exists_polyDofBound S k C c
  obtain ⟨D, hD0, hD⟩ := exists_polyCoeffBound (n := n) S k
  refine ⟨4 ^ n * (1 + B * D) ^ 2, by positivity, fun hS T hT hh w hw hdeg M hM => ?_⟩
  refine (formL2Sq_sub_polyLocalInterp_le S hs hB hD0 hD hS hT hh hw hdeg hM).trans
    (le_of_eq ?_)
  rw [mul_pow, show (4 : ℝ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
  ring

/-- **The `L²(T)` interpolation error of `d Π_T w = Π_T dw` on shape-regular simplices,
existence form**: `‖dw - d Π_T w‖²_{L²(T)} ≤ K h_Tⁿ (h_T^{s+1} sup_T ‖D^{s+1} dw‖)²` for
`P_sΛᵏ⁺¹ ⊆ P(T)ᵏ⁺¹` and `w ∈ C^{s+2}`. -/
theorem exists_formL2Sq_extDeriv_sub_polyLocalInterp_le {k s : ℕ}
    (hs : polySpace n s (k + 1) ≤ S.space n (k + 1)) (C c : ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ {Sset : Set (Affine.Simplex ℝ (Fin n → ℝ) n)},
      IsShapeRegular Sset C c → ∀ T ∈ Sset, 0 < diam T → ∀ {w : FormField n}
      (hw : ContDiff ℝ (s + 2) w), (∀ x, IsDeg k (w x)) → ∀ {M : ℝ},
      (∀ y ∈ T.closedInterior, ‖iteratedFDeriv ℝ (s + 1) (extDeriv w) y‖ ≤ M) →
      formL2Sq T.closedInterior (extDeriv w - extDeriv
        (((polyElement n S).localInterp T k ⟨w, hw.continuous⟩ :
          (polyElement n S).space T k) : FormField n)) ≤
        K * diam T ^ n * (diam T ^ (s + 1) * M) ^ 2 := by
  obtain ⟨B, hB0, hB⟩ := exists_polyDofBound S (k + 1) C c
  obtain ⟨D, hD0, hD⟩ := exists_polyCoeffBound (n := n) S (k + 1)
  refine ⟨4 ^ n * (1 + B * D) ^ 2, by positivity, fun hS T hT hh w hw hdeg M hM => ?_⟩
  have h := formL2Sq_le_of_norm_le (volume_closedInterior_lt_top T) (u := extDeriv w -
    extDeriv (((polyElement n S).localInterp T k ⟨w, hw.continuous⟩ :
      (polyElement n S).space T k) : FormField n)) (B := (1 + B * D) * (diam T ^ (s + 1) * M))
    fun x hx => norm_extDeriv_sub_polyLocalInterp_le S hs hB hD0 hD hS hT hh hw hdeg hM hx
  refine h.trans ?_
  rw [Fintype.card_finset, Fintype.card_fin]
  push_cast
  calc (2 : ℝ) ^ n * volume.real T.closedInterior * ((1 + B * D) * (diam T ^ (s + 1) * M)) ^ 2
      ≤ 2 ^ n * (2 * diam T) ^ n * ((1 + B * D) * (diam T ^ (s + 1) * M)) ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (volume_real_closedInterior_le T) (by positivity)) (sq_nonneg _)
    _ = 4 ^ n * (1 + B * D) ^ 2 * diam T ^ n * (diam T ^ (s + 1) * M) ^ 2 := by
        rw [mul_pow 2 (diam T), show (4 : ℝ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
        ring

end Local

/-! ### Local estimates on the simplices of a quasi-uniform shape-regular mesh -/

section MeshTools

variable (S : PolySeq)

/-- **The DOF estimate on a quasi-uniform shape-regular mesh**: if the degrees of freedom of
`z ∈ P(T)ᵏ` on the faces of a mesh simplex `T` are bounded by `hᵏ D''` (`h` the mesh size), then
`|z(x)ₛ| ≤ B D'' / qᵏ` on `T`. -/
theorem abs_le_of_abs_polyDof_le {M : SimplicialMesh n} {C c q : ℝ} (hM : MeshData M C c q)
    (hq : 0 < q) {k : ℕ} {B : ℝ} (hB : PolyDofBound S n k C c B)
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ M.simplices) {z : FormField n}
    (hz : z ∈ S.space n k) {D'' : ℝ} (hD0 : 0 ≤ D'')
    (hD : ∀ g ⊆ vertexSet T, ∀ i : S.DofIdx g k,
      |S.dof g k i ⟨z, S.space_le_contForms n k hz⟩| ≤ M.meshSize ^ k * D'')
    {x : Fin n → ℝ} (hx : x ∈ T.closedInterior) (s : Finset (Fin n)) :
    |z x s| ≤ B * D'' / q ^ k := by
  have hh := hM.meshSize_pos
  have hzb := hB hM.shape T hT (hM.diam_pos hq hT) hz (by positivity) hD x hx
  have hqh : q * M.meshSize ≤ diam T := hM.quasi T hT
  have hzs : |z x s| ≤ ‖z x‖ := by
    have := norm_le_pi_norm (z x) s; rwa [Real.norm_eq_abs] at this
  have h1 : (q * M.meshSize) ^ k * |z x s| ≤ B * (M.meshSize ^ k * D'') :=
    (mul_le_mul (pow_le_pow_left₀ (by positivity) hqh k) hzs (abs_nonneg _)
      (pow_nonneg (diam_nonneg T) k)).trans hzb
  rw [le_div_iff₀ (pow_pos hq k)]
  have hhk : 0 < M.meshSize ^ k := pow_pos hh k
  refine le_of_mul_le_mul_left ?_ hhk
  calc M.meshSize ^ k * (|z x s| * q ^ k) = (q * M.meshSize) ^ k * |z x s| := by ring
    _ ≤ B * (M.meshSize ^ k * D'') := h1
    _ = M.meshSize ^ k * (B * D'') := by ring

/-- The local inverse estimates on all simplices of `M` for the fields of `V`, coefficientwise and
in terms of the mesh size. -/
def InvBoundV (M : SimplicialMesh n) (V : Submodule ℝ (FormField n)) (A : ℝ) : Prop :=
  ∀ T ∈ M.simplices, ∀ z ∈ V,
    (∀ x ∈ T.closedInterior, ∀ s, √M.meshSize ^ n * |z x s| ≤
      A * √(∑ s, ∫ x in T.closedInterior, (z x s) ^ 2)) ∧
    (∀ x ∈ T.closedInterior, ∀ x' ∈ T.closedInterior, ∀ s,
      √M.meshSize ^ n * M.meshSize * |z x s - z x' s| ≤
        A * ‖x - x'‖ * √(∑ s, ∫ x in T.closedInterior, (z x s) ^ 2))

/-- **Inverse estimates on the mesh in terms of the mesh size**, from the shape-regular local
inverse estimates and quasi-uniformity: `A' = A q^{-n/2} q⁻¹`. -/
theorem invBoundV_of {M : SimplicialMesh n} {C c q : ℝ} (hM : MeshData M C c q) (hq : 0 < q)
    {V : Submodule ℝ (FormField n)} {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ {Sset : Set (Affine.Simplex ℝ (Fin n → ℝ) n)}, IsShapeRegular Sset C c →
      ∀ T ∈ Sset, 0 < diam T → ∀ u ∈ V,
        (∀ x ∈ T.closedInterior, √(diam T) ^ n * ‖u x‖ ≤
          A * √(formL2Sq T.closedInterior u)) ∧
        (∀ x ∈ T.closedInterior, ∀ x' ∈ T.closedInterior,
          √(diam T) ^ n * diam T * ‖u x - u x'‖ ≤
            A * ‖x - x'‖ * √(formL2Sq T.closedInterior u))) :
    InvBoundV M V (A / √q ^ n / q) := by
  intro T hT z hz
  have hh := hM.meshSize_pos
  have hq1 := hM.q_le_one
  have hTd := hM.diam_pos hq hT
  obtain ⟨h1, h2⟩ := hA hM.shape T hT hTd z hz
  simp only [formL2Sq] at h1 h2
  set F := ∑ s, ∫ x in T.closedInterior, (z x s) ^ 2
  have hqh : q * M.meshSize ≤ diam T := hM.quasi T hT
  have hsq : √M.meshSize ^ n * √q ^ n ≤ √(diam T) ^ n := by
    rw [← mul_pow, ← Real.sqrt_mul hh.le]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (by linarith)) n
  have hsqq : 0 < √q ^ n := pow_pos (Real.sqrt_pos.2 hq) n
  have hF : 0 ≤ √F := Real.sqrt_nonneg _
  constructor
  · intro x hx s
    have hxs : |z x s| ≤ ‖z x‖ := by
      have := norm_le_pi_norm (z x) s; rwa [Real.norm_eq_abs] at this
    have := h1 x hx
    have hk : √M.meshSize ^ n * |z x s| ≤ A / √q ^ n * √F := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hsqq]
      calc √M.meshSize ^ n * |z x s| * √q ^ n = (√M.meshSize ^ n * √q ^ n) * |z x s| := by ring
        _ ≤ √(diam T) ^ n * ‖z x‖ :=
            mul_le_mul hsq hxs (abs_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) n)
        _ ≤ _ := this
    refine hk.trans (mul_le_mul_of_nonneg_right ?_ hF)
    exact le_div_self (by positivity) hq hq1
  · intro x hx x' hx' s
    have hxs : |z x s - z x' s| ≤ ‖z x - z x'‖ := by
      have := norm_le_pi_norm (z x - z x') s; rwa [Real.norm_eq_abs, Pi.sub_apply] at this
    have := h2 x hx x' hx'
    rw [div_div]
    rw [show A / (√q ^ n * q) * ‖x - x'‖ * √F =
      ‖x - x'‖ * A * √F / (√q ^ n * q) by ring]
    rw [le_div_iff₀ (by positivity)]
    calc √M.meshSize ^ n * M.meshSize * |z x s - z x' s| * (√q ^ n * q)
        = (√M.meshSize ^ n * √q ^ n) * (q * M.meshSize) * |z x s - z x' s| := by ring
      _ ≤ √(diam T) ^ n * diam T * ‖z x - z x'‖ := by
          gcongr
      _ ≤ A * ‖x - x'‖ * √F := this
      _ = ‖x - x'‖ * A * √F := by ring

/-- **Inverse estimates on shape-regular simplices** for the spaces of an admissible sequence
(`Feec.FiniteElement.exists_inverse_bound_of_le_polySpace`). -/
theorem exists_polyInvBound (k : ℕ) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ A, 0 ≤ A ∧ ∀ {Sset : Set (Affine.Simplex ℝ (Fin n → ℝ) n)}, IsShapeRegular Sset C c →
      ∀ T ∈ Sset, 0 < diam T → ∀ u ∈ S.space n k,
        (∀ x ∈ T.closedInterior, √(diam T) ^ n * ‖u x‖ ≤
          A * √(formL2Sq T.closedInterior u)) ∧
        (∀ x ∈ T.closedInterior, ∀ x' ∈ T.closedInterior,
          √(diam T) ^ n * diam T * ‖u x - u x'‖ ≤
            A * ‖x - x'‖ * √(formL2Sq T.closedInterior u)) :=
  exists_inverse_bound_of_le_polySpace (S.space_le_polySpace k)
    (fun B b _ hu => Parallelepiped.affinePullback_mem_space_poly S B b k hu) hC hc

/-- **The local mass controls the local fields** of the simplices inside the neighbourhood, for
any element family (`interior T' ⊆ Ω` for every simplex). -/
theorem sum_integral_sq_le_locMass_of (E : LocalElement n) {M : SimplicialMesh n}
    (hΩ : MeasurableSet M.domain) (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain)
    {k : ℕ} {r : ℝ} (u : E.Piecewise M k) (T' : M.simplices)
    {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hsub : (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior ⊆
      Metric.cthickening r T.closedInterior) :
    ∑ s, ∫ y in (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      (((u T' : E.space T' k) : FormField n) y s) ^ 2 ≤ locMass r (E.glue M k u) T := by
  set z : FormField n := ((u T' : E.space T' k) : FormField n)
  have hdeg : ∀ y, IsDeg k (z y) := E.isDeg_of_mem (u T').2
  rw [FEM.sum_eq_sum_formIdx (fun s hs => by
    have : ∀ y, (z y s) ^ 2 = 0 := fun y => by rw [hdeg y s hs]; ring
    simp_rw [this]; simp)]
  refine Finset.sum_le_sum fun s _ => ?_
  have hae := FEM.Poly.ae_glue_eq_local E u hΩ
  rw [FEM.integral_closedInterior_eq_interior]
  have heq : ∫ y in interior (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, (z y s.1) ^ 2 =
      ∫ y in interior (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
        (M.domain.indicator ((E.glue M k u s : L2 ℝ M.domain) : (Fin n → ℝ) → ℝ) y) ^ 2 := by
    refine setIntegral_congr_ae isOpen_interior.measurableSet ?_
    filter_upwards [hae] with y hy hyT
    obtain ⟨T'', hyT'', hval⟩ := hy (hint T' T'.2 hyT)
    have : T'' = T' := by
      by_contra hne
      exact Set.disjoint_left.1 (M.pairwise_disjoint_interior T''.2 T'.2
        (fun e => hne (Subtype.ext e))) hyT'' hyT
    subst this
    rw [hval s]
  rw [heq]
  refine setIntegral_mono_set (integrable_sq_indicator hΩ _).integrableOn
    (Eventually.of_forall fun _ => sq_nonneg _)
    (Eventually.of_forall fun y hy => hsub (interior_subset hy))

end MeshTools

/-! ### The uniform `L²` bound of the smoothed interpolants -/

section Bound

variable (S : PolySeq) {x₀ : Fin n → ℝ} {R σ γ : ℝ}

/-- **The local `L²` bound of `Q = Π_h R`** for an admissible sequence on a simplex of a
quasi-uniform shape-regular mesh: `‖Q x‖²_{L²(T)} ≲ (2 / (γ σ))ⁿ m_T(x)`. -/
theorem sum_integral_sq_polyInterp_le {M : SimplicialMesh n} {C c q : ℝ} (hM : MeshData M C c q)
    (hq : 0 < q) [NeZero n] {k : ℕ} {B D : ℝ} (hB : PolyDofBound S n k C c B)
    (hD0 : 0 ≤ D) (hD : PolyCoeffBound S n k D)
    (hR : 0 < R) (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R)
    {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm x₀ R σ γ M.meshSize p) (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hγh : γ * M.meshSize / R ≤ 1)
    (hΩ : MeasurableSet M.domain) (x : L2F ℝ M.domain (formIdx n k))
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ M.simplices) :
    ∑ s : formIdx n k, ∫ y in T.closedInterior,
      (((((polyElement n S).globalInterp M k
        (Submodule.inclusion c1Forms_le_contForms (smoothForm p hΩ k x)) :
          (polyElement n S).Piecewise M k) ⟨T, hT⟩ : (polyElement n S).space T k) :
          FormField n) y s.1) ^ 2 ≤
      2 ^ n * (B * D * 2 ^ k / q ^ k) ^ 2 * (2 / (γ * σ)) ^ n *
        locMass (2 * M.meshSize) x T := by
  set h := M.meshSize
  have hh : 0 < h := hM.meshSize_pos
  have hTh : diam T ≤ h := M.diam_le_meshSize hT
  set w := smoothForm p hΩ k x
  set z : FormField n := ((((polyElement n S).globalInterp M k
    (Submodule.inclusion c1Forms_le_contForms w) :
      (polyElement n S).Piecewise M k) ⟨T, hT⟩ : (polyElement n S).space T k) : FormField n)
  have hz : z ∈ S.space n k := ((((polyElement n S).globalInterp M k
    (Submodule.inclusion c1Forms_le_contForms w) :
      (polyElement n S).Piecewise M k) ⟨T, hT⟩ : (polyElement n S).space T k)).2
  set L := locMass (2 * h) x T
  have hL := locMass_nonneg (2 * h) x T
  set Mρ := 1 / volume.real (Metric.closedBall (0 : Fin n → ℝ) p.bump.rIn)
  have hMρ : Mρ = (1 / (γ * h * σ)) ^ n := by
    simp only [Mρ]
    rw [hp.rIn_eq, FEM.volume_real_closedBall_zero (by positivity), one_div_pow]
    congr 2; ring
  set A := 2 ^ k * √(Mρ * L)
  have hA0 : 0 ≤ A := by positivity
  -- the smoothed field is bounded by `A` on `T`
  have hw : ∀ y ∈ T.closedInterior, ∀ s, |(w : FormField n) y s| ≤ A := by
    intro y hy s
    refine (FEM.abs_smoothForm_le hΩ p k x y s).trans (mul_le_mul (hp.pow_factor_le hγh k)
      ?_ (Real.sqrt_nonneg _) (by positivity))
    refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s' _ => ?_)
      (by positivity))
    refine setIntegral_mono_set (integrable_sq_indicator hΩ _).integrableOn
      (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall fun t ht => ?_)
    have hyc : y ∈ closure M.domain := M.closedInterior_subset_closure hT hy
    have h1 := hp.norm_sub_le_of_dist_le hR hσ1 (hRx y hyc) (Metric.mem_closedBall.1 ht)
    refine Metric.mem_cthickening_of_dist_le t y _ _ hy ?_
    rw [dist_eq_norm]
    nlinarith
  -- its degrees of freedom are `O(hᵏ A)`
  have hdof : ∀ g ⊆ vertexSet T, ∀ i : S.DofIdx g k,
      |S.dof g k i ⟨z, S.space_le_contForms n k hz⟩| ≤ h ^ k * (D * A) := by
    intro g hgT i
    have e : S.dof g k i ⟨z, S.space_le_contForms n k hz⟩ =
        S.dof g k i (Submodule.inclusion c1Forms_le_contForms w) :=
      (polyElement n S).localDof_globalInterp M k
        (Submodule.inclusion c1Forms_le_contForms w) ⟨T, hT⟩ g hgT i
    rw [e]
    refine (abs_polyDof_le S hD hgT i _ hA0 hw).trans ?_
    calc D * diam T ^ k * A ≤ D * h ^ k * A :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (diam_nonneg T) hTh k) hD0) hA0
      _ = h ^ k * (D * A) := by ring
  -- hence `|z| ≤ B D A / qᵏ` on `T`
  have hzb : ∀ y ∈ T.closedInterior, ∀ s, |z y s| ≤ B * (D * A) / q ^ k :=
    fun y hy s => abs_le_of_abs_polyDof_le S hM hq hB hT hz (mul_nonneg hD0 hA0) hdof hy s
  have hzc : Continuous z := (PolyKind.contDiff_of_mem_space hz).continuous
  have hloc : ∀ s : formIdx n k, ∫ y in T.closedInterior, (z y s.1) ^ 2 ≤
      (2 * h) ^ n * (B * (D * A) / q ^ k) ^ 2 := by
    intro s
    refine (integral_closedInterior_le (f := fun y => (z y s.1) ^ 2)
      (A := (B * (D * A) / q ^ k) ^ 2)
      (((continuous_apply s.1).comp hzc).pow 2) (fun y hy => ?_) (fun y => sq_nonneg _)).trans ?_
    · rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hzb y hy s.1) 2
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith [diam_nonneg T])
        (by linarith) n) (sq_nonneg _)
  calc ∑ s : formIdx n k, ∫ y in T.closedInterior, (z y s.1) ^ 2
      ≤ ∑ _s : formIdx n k, (2 * h) ^ n * (B * (D * A) / q ^ k) ^ 2 :=
        Finset.sum_le_sum fun s _ => hloc s
    _ = Fintype.card (formIdx n k) * ((2 * h) ^ n * (B * (D * A) / q ^ k) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 2 ^ n * ((2 * h) ^ n * (B * (D * A) / q ^ k) ^ 2) :=
        mul_le_mul_of_nonneg_right (FEM.card_formIdx_le _) (by positivity)
    _ = 2 ^ n * (B * D * 2 ^ k / q ^ k) ^ 2 * ((2 * h) ^ n * Mρ) * L := by
        have hA2 : A ^ 2 = (2 ^ k) ^ 2 * (Mρ * L) := by
          simp only [A]; rw [mul_pow, Real.sq_sqrt (by positivity)]
        rw [show B * (D * A) / q ^ k = (B * D / q ^ k) * A by ring, mul_pow (B * D / q ^ k) A, hA2,
          show B * D * 2 ^ k / q ^ k = (B * D / q ^ k) * 2 ^ k by ring]
        ring
    _ = 2 ^ n * (B * D * 2 ^ k / q ^ k) ^ 2 * (2 / (γ * σ)) ^ n * L := by
        rw [hMρ, ← mul_pow, show 2 * h * (1 / (γ * h * σ)) = 2 / (γ * σ) by field_simp]

/-- **The uniform `L²` bound of the smoothed interpolants** `Q = Π_h R` of an admissible sequence
on quasi-uniform shape-regular meshes, for every admissible parameter at scale `γ h` (either
family): `‖Q x‖ ≤ K ‖x‖`, with `K` depending only on `n, S, C, c, q, γ, σ`. -/
theorem exists_norm_polySmoothedInterp_le [NeZero n] {C c q : ℝ} (hc : 0 < c) (hq : 0 < q)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ∃ K, 0 ≤ K ∧ ∀ (M : SimplicialMesh n), MeshData M C c q → ∀ (hΩ : MeasurableSet M.domain),
      0 < R → (∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) → γ * M.meshSize / R ≤ 1 →
      ∀ (p : SmoothingParam (Fin n → ℝ)), IsAdm x₀ R σ γ M.meshSize p →
      ∀ (k : ℕ) (x : L2F ℝ M.domain (formIdx n k)),
        ‖(polyElement n S).smoothedInterp M p hΩ k x‖ ≤ K * ‖x‖ := by
  classical
  choose B hB0 hB using fun k : ℕ => exists_polyDofBound (n := n) S k C c
  choose D hD0 hD using fun k : ℕ => exists_polyCoeffBound (n := n) S k
  set G : ℕ → ℝ := fun k => 2 ^ n * (B k * D k * 2 ^ k / q ^ k) ^ 2 * (2 / (γ * σ)) ^ n *
    covConst n c q
  have hG : ∀ k, 0 ≤ G k := fun k => by
    have := hB0 k; have := hD0 k; simp only [G, covConst]; positivity
  refine ⟨√(∑ k ∈ Finset.range (n + 1), G k), Real.sqrt_nonneg _,
    fun M hM hΩ hR hRx hγh p hp k x => ?_⟩
  by_cases hk : n < k
  · have := FEM.subsingleton_L2F_of_lt (Ω := M.domain) hk
    rw [Subsingleton.elim x 0]
    simp
  push Not at hk
  have hQ := (polyElement n S).smoothedInterp_natCast M p hΩ k x
  set u := (polyElement n S).globalInterp M k (Submodule.inclusion c1Forms_le_contForms
    (smoothForm p hΩ k x))
  have h1 := norm_sq_pieceL2_le M M.domain (fun T => formComp (k := (k : ℤ))
    ((polyElement n S).extendPW M (u : (polyElement n S).Piecewise M k) T))
    (fun T hT s => continuous_formComp ((polyElement n S).contDiff_extendPW M _
      hT).continuous s)
  have h2 : ∑ T ∈ M.simplices, ∑ s : formIdx n k, ∫ y in T.closedInterior,
      (formComp (k := (k : ℤ)) ((polyElement n S).extendPW M
        (u : (polyElement n S).Piecewise M k) T) s y) ^ 2 ≤
      ∑ T ∈ M.simplices, 2 ^ n * (B k * D k * 2 ^ k / q ^ k) ^ 2 * (2 / (γ * σ)) ^ n *
        locMass (2 * M.meshSize) x T := by
    refine Finset.sum_le_sum fun T hT => ?_
    have e : ∀ s : formIdx n k, ∀ y, formComp (k := (k : ℤ))
        ((polyElement n S).extendPW M (u : (polyElement n S).Piecewise M k) T)
          s y = (((u : (polyElement n S).Piecewise M k) ⟨T, hT⟩ :
            (polyElement n S).space T k) : FormField n) y s.1 := fun s y => by
      change (polyElement n S).extendPW M _ T y s.1 = _
      rw [(polyElement n S).extendPW_of_mem M _ hT]
    simp_rw [e]
    exact sum_integral_sq_polyInterp_le S hM hq (hB k) (hD0 k) (hD k) hR hRx hp hγ hγ1
      hσ hσ1 hγh hΩ x hT
  have h3 := sum_locMass_le hM hc hq hΩ x
  have hsq : ‖(polyElement n S).smoothedInterp M p hΩ k x‖ ^ 2 ≤
      (√(∑ k ∈ Finset.range (n + 1), G k) * ‖x‖) ^ 2 := by
    rw [hQ, mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun k _ => hG k)]
    refine h1.trans (h2.trans ?_)
    rw [← Finset.mul_sum]
    calc 2 ^ n * (B k * D k * 2 ^ k / q ^ k) ^ 2 * (2 / (γ * σ)) ^ n *
          ∑ T ∈ M.simplices, locMass (2 * M.meshSize) x T
        ≤ 2 ^ n * (B k * D k * 2 ^ k / q ^ k) ^ 2 * (2 / (γ * σ)) ^ n *
            (covConst n c q * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = G k * ‖x‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun k _ => hG k)
          (Finset.mem_range.2 (by omega))) (sq_nonneg _)
  exact le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) hsq

end Bound

/-! ### Closeness of the smoothed interpolants to the identity on `Vₕ` -/

section Close

variable (S : PolySeq) {x₀ : Fin n → ℝ} {R σ γ : ℝ}

/-- **The geometric condition of the smoother for the faces of all dimensions** (lexicographic
parametrizations): at points of a face `g` with barycentric weights `≥ θ`, every simplex whose
interior contains a sample of the smoother contains `g`. -/
def PolyGeomOK (M : SimplicialMesh n) (p : SmoothingParam (Fin n → ℝ)) (θ : ℝ) : Prop :=
  ∀ (T : M.simplices) (g : Finset (Fin n → ℝ)),
    g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) → ∀ {m : ℕ}, #g = m + 1 →
    ∀ ξ ∈ FiniteElement.refSimplex m, ξ ∉ FEM.nearBdry m θ →
      ∀ t, dist t (p.center + p.factor • (simplexMap (lexEnum g m) ξ - p.center)) <
        p.bump.rOut → ∀ T' : M.simplices,
        t ∈ interior (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior →
        g ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n)

/-- **The sampling condition for an admissible sequence**: a sample of the smoother outside `Ω`
near a point of a face `g` with barycentric weights `≥ θ` forces the degrees of freedom of the
subfaces of `g` to vanish (vacuous for the maximal family; for the minimal family the vanishing
of the boundary DOFs of `V̊ₕ`). -/
def PolySampleOK {M : SimplicialMesh n} {k : ℕ} (p : SmoothingParam (Fin n → ℝ)) (θ : ℝ)
    (u : (polyElement n S).Piecewise M k) : Prop :=
  ∀ (T : M.simplices) (g : Finset (Fin n → ℝ)),
    g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) → ∀ {m : ℕ}, #g = m + 1 →
    ∀ ξ ∈ FiniteElement.refSimplex m, ξ ∉ FEM.nearBdry m θ →
      ∀ t, dist t (p.center + p.factor • (simplexMap (lexEnum g m) ξ - p.center)) <
        p.bump.rOut → t ∉ M.domain →
        ∀ g' ⊆ g, ∀ i : S.DofIdx g' k, (polyElement n S).localDof T k g' i (u T) = 0

open Classical in
/-- **The pointwise estimate of the DOF integrand of `v - Q v`** (`v ∈ Vₕ`) for an admissible
sequence on a quasi-uniform shape-regular mesh: at `x = F_q(ξ)` (`q` the lexicographic
parametrization of a face `g` of `T`) and for any coefficient vector `c` that only sees the trace
on `g`, `h^{n/2} |Σₛ (v_T - R v)(x)ₛ cₛ| ≤ (Σₛ |cₛ|) A m_T(v)^{1/2} 2^{k+1} · (1 or 2 (k + 1) γ)`,
with the factor `2 (k + 1) γ` when all barycentric coordinates of `ξ` are `≥ θ`: then every
simplex sampled by the smoother inside `Ω` contains `g` (`PolyGeomOK`), where the traces of the
local fields agree, and samples outside `Ω` are controlled by `PolySampleOK`. -/
theorem sqrt_mul_abs_polyIntegrand_le {M : SimplicialMesh n} (hΩ : MeasurableSet M.domain)
    (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) {k : ℕ} {A : ℝ}
    (hA0 : 0 ≤ A) (hA : InvBoundV M (S.space n k) A) {p : SmoothingParam (Fin n → ℝ)}
    (hp : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hhR : M.meshSize ≤ 2 * R)
    (hh : 0 < M.meshSize) (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hσ1 : σ ≤ 1) {θ : ℝ}
    (hgeom : PolyGeomOK M p θ) {u : (polyElement n S).Piecewise M k}
    (hu : u ∈ (polyElement n S).globalSpace M k) (hs : PolySampleOK S p θ u) (T : M.simplices)
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n)) {m : ℕ}
    (hg : #g = m + 1) {ξ : Fin m → ℝ} (hξ : ξ ∈ FiniteElement.refSimplex m)
    (c : Finset (Fin n) → ℝ)
    (hc : ∀ α β : Finset (Fin n) → ℝ, IsDeg k α → IsDeg k β →
      pullback (simplexMatrix (lexEnum g m)) α = pullback (simplexMatrix (lexEnum g m)) β →
        ∑ s, α s * c s = ∑ s, β s * c s) :
    √M.meshSize ^ n * |∑ s, (((u T : (polyElement n S).space T k) : FormField n)
        (simplexMap (lexEnum g m) ξ) s -
      (smoothForm p hΩ k ((polyElement n S).glue M k u) : FormField n)
        (simplexMap (lexEnum g m) ξ) s) * c s| ≤
      (∑ s, |c s|) * A *
        √(locMass (2 * M.meshSize) ((polyElement n S).glue M k u)
          (T : Affine.Simplex ℝ (Fin n → ℝ) n)) *
        2 ^ (k + 1) * (if ξ ∈ FEM.nearBdry m θ then 1 else (k + 1) * (2 * γ)) := by
  set h := M.meshSize
  have hγ1 : γ ≤ 1 := by linarith
  have hγh : γ * h / R ≤ 1 := by
    rw [div_le_one hR]; nlinarith
  set v := (polyElement n S).glue M k u
  set q := lexEnum g m
  set x := simplexMap q ξ
  set uT : FormField n := ((u T : (polyElement n S).space T k) : FormField n)
  have huT : uT ∈ S.space n k := (u T).2
  set L := locMass (2 * h) v (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have hL0 : 0 ≤ L := locMass_nonneg _ _ _
  set Rb := (∑ s, |c s|) * A * √L * 2 ^ (k + 1) *
    (if ξ ∈ FEM.nearBdry m θ then 1 else (k + 1) * (2 * γ))
  have hsq : 0 < √h ^ n := pow_pos (Real.sqrt_pos.2 hh) n
  have hxT : x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior :=
    FEM.Poly.simplexMap_lexEnum_mem hgT hg hξ
  have hxc : x ∈ closure M.domain := M.closedInterior_subset_closure T.2 hxT
  set ŷ := p.center + p.factor • (x - p.center)
  have hc0 : 0 < p.factor := p.factor_pos
  have hck : p.factor ^ k ≤ 2 ^ k := hp.pow_factor_le hγh k
  have hck0 : 0 ≤ p.factor ^ k := pow_nonneg hc0.le k
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hdef : |1 - p.factor ^ k| ≤ k * 2 ^ k * (2 * γ) := by
    refine (hp.abs_one_sub_pow_le hR hγh k).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [div_le_iff₀ hR]; nlinarith
  have hTinv := hA T T.2 uT huT
  have hLT : ∑ s, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, (uT y s) ^ 2 ≤ L :=
    sum_integral_sq_le_locMass_of (polyElement n S) hΩ hint u T
      (FEM.self_subset_cthickening _ (by positivity))
  have hsqLT : √(∑ s, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      (uT y s) ^ 2) ≤ √L := Real.sqrt_le_sqrt hLT
  have hR0 : 0 ≤ (∑ s, |c s|) * A * √L * 2 ^ (k + 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (Finset.sum_nonneg fun s _ => abs_nonneg _) hA0)
      (Real.sqrt_nonneg _)) (by positivity)
  -- the integrand as a mollified average
  rw [FEM.sum_sub_smoothForm_mul_eq hΩ p k v (uT x) c x]
  set G : (Fin n → ℝ) → ℝ := fun t => ∑ s, (uT x s - p.factor ^ k * FEM.extField v t s) * c s
  set ρ : (Fin n → ℝ) → ℝ := fun t => p.bump.normed volume (ŷ - t)
  have hρ0 : ∀ t, 0 ≤ ρ t := fun t => p.bump.nonneg_normed _
  have hρi : Integrable ρ :=
    (FEM.isTest_normed_comp_sub p.bump ŷ).continuous.integrable_of_hasCompactSupport
      (FEM.isTest_normed_comp_sub p.bump ŷ).hasCompactSupport
  have hρ1 : ∫ t, ρ t = 1 := FEM.integral_normed_comp_sub p.bump ŷ
  have hρG : Integrable fun t => ρ t * G t := by
    have e : (fun t => ρ t * G t) = fun t => ∑ s, ((uT x s * c s) * ρ t -
        (p.factor ^ k * c s) * (FEM.extField v t s * ρ t)) := by
      funext t; simp only [G, Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => by ring
    rw [e]
    exact integrable_finsetSum _ fun s _ =>
      (hρi.const_mul _).sub ((FEM.integrable_extField_mul hΩ v p.bump ŷ s).const_mul _)
  -- the bound of the `T`-term
  have hbT : √h ^ n * ∑ s, |uT x s| * |c s| ≤ (∑ s, |c s|) * A * √L := by
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun s _ => ?_
    calc √h ^ n * (|uT x s| * |c s|) = (√h ^ n * |uT x s|) * |c s| := by ring
      _ ≤ (A * √L) * |c s| := mul_le_mul_of_nonneg_right ((hTinv.1 x hxT s).trans
          (mul_le_mul_of_nonneg_left hsqLT hA0)) (abs_nonneg _)
      _ = |c s| * A * √L := by ring
  -- the pointwise bound on the support of the mollifier
  have hae := FEM.Poly.ae_glue_eq_local (polyElement n S) u hΩ
  have hb : ∀ᵐ t ∂volume, ρ t ≠ 0 → |G t| ≤ Rb / √h ^ n := by
    filter_upwards [hae] with t ht hρt
    have hdist : dist t ŷ < p.bump.rOut := by
      by_contra hcon; push Not at hcon
      exact hρt (FEM.normed_eq_zero_of_le p.bump hcon)
    rw [le_div_iff₀ hsq, mul_comm]
    have hxt' : ‖t - x‖ ≤ 2 * (γ * h) := hp.norm_sub_le_of_dist_le hR hσ1 (hRx x hxc) hdist.le
    by_cases htΩ : t ∈ M.domain
    · obtain ⟨T', htT', hval⟩ := ht htΩ
      set u' : FormField n := ((u T' : (polyElement n S).space T' k) : FormField n)
      have hu' : u' ∈ S.space n k := (u T').2
      have hext : ∀ s, FEM.extField v t s = u' t s := by
        intro s
        by_cases hs' : (#s : ℤ) = (k : ℤ)
        · rw [FEM.extField, formExt_of_card _ hs']; exact hval ⟨s, hs'⟩
        · have : FEM.extField v t s = 0 := by simp [FEM.extField, formExt, hs']
          rw [this, PolyKind.isDeg_of_mem_space hu' t s (fun h' => hs' (by rw [h']))]
      have hGt : G t = ∑ s, (uT x s - p.factor ^ k * u' t s) * c s := by
        simp only [G, hext]
      have htT'c : t ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior := interior_subset htT'
      have hT'sub : (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior ⊆
          Metric.cthickening (2 * h) (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior := by
        intro y hy
        have hdy : ‖y - t‖ ≤ h := by
          rw [← dist_eq_norm]
          exact (Metric.dist_le_diam_of_mem
            (T' : Affine.Simplex ℝ (Fin n → ℝ) n).isCompact_closedInterior.isBounded
            hy htT'c).trans (M.diam_le_meshSize T'.2)
        refine Metric.mem_cthickening_of_dist_le y x _ _ hxT ?_
        rw [dist_eq_norm]
        calc ‖y - x‖ = ‖(y - t) + (t - x)‖ := by congr 1; abel
          _ ≤ ‖y - t‖ + ‖t - x‖ := norm_add_le _ _
          _ ≤ h + 2 * (γ * h) := add_le_add hdy hxt'
          _ ≤ 2 * h := by nlinarith
      have hL' : ∑ s, ∫ y in (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
          (u' y s) ^ 2 ≤ L := sum_integral_sq_le_locMass_of (polyElement n S) hΩ hint u T' hT'sub
      have hT'inv := hA T' T'.2 u' hu'
      have hsqL' : √(∑ s, ∫ y in (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
          (u' y s) ^ 2) ≤ √L := Real.sqrt_le_sqrt hL'
      rw [hGt]
      by_cases hbad : ξ ∈ FEM.nearBdry m θ
      · -- near the boundary of the face: inverse estimates only
        have hR' : Rb = (∑ s, |c s|) * A * √L * 2 ^ (k + 1) * 1 := by
          simp only [Rb, hbad, ite_true]
        rw [hR']
        calc √h ^ n * |∑ s, (uT x s - p.factor ^ k * u' t s) * c s|
            ≤ √h ^ n * ∑ s, (2 ^ k * (|uT x s| + |u' t s|)) * |c s| := by
              refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
                (Finset.sum_le_sum fun s _ => ?_)) hsq.le
              rw [abs_mul]
              refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
              calc |uT x s - p.factor ^ k * u' t s| ≤ |uT x s| + |p.factor ^ k * u' t s| :=
                    abs_sub _ _
                _ ≤ 2 ^ k * |uT x s| + 2 ^ k * |u' t s| := by
                    rw [abs_mul, abs_of_nonneg hck0]
                    exact add_le_add (le_mul_of_one_le_left (abs_nonneg _) h2k)
                      (mul_le_mul_of_nonneg_right hck (abs_nonneg _))
                _ = 2 ^ k * (|uT x s| + |u' t s|) := by ring
          _ = 2 ^ k * ∑ s, (√h ^ n * |uT x s| + √h ^ n * |u' t s|) * |c s| := by
              rw [Finset.mul_sum, Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => by ring
          _ ≤ 2 ^ k * ∑ s, (A * √L + A * √L) * |c s| := by
              refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ =>
                mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)) (by positivity)
              exact add_le_add ((hTinv.1 x hxT s).trans (mul_le_mul_of_nonneg_left hsqLT hA0))
                ((hT'inv.1 t htT'c s).trans (mul_le_mul_of_nonneg_left hsqL' hA0))
          _ = (∑ s, |c s|) * A * √L * 2 ^ (k + 1) * 1 := by
              rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
              refine Finset.sum_congr rfl fun s _ => by ring
      · -- away from the boundary of the face: the sampled simplex contains the face
        have hR' : Rb = (∑ s, |c s|) * A * √L * 2 ^ (k + 1) * ((k + 1) * (2 * γ)) := by
          simp only [Rb, hbad, ite_false]
        rw [hR']
        have hgT' : g ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n) :=
          hgeom T g hgT hg ξ hξ hbad t hdist T' htT'
        have htr : ∑ s, uT x s * c s = ∑ s, u' x s * c s :=
          hc _ _ (PolyKind.isDeg_of_mem_space huT x) (PolyKind.isDeg_of_mem_space hu' x)
            (FEM.Poly.pullback_eq_of_mem_globalSpace hu T T' hgT hgT' hg ξ)
        have e : ∑ s, (uT x s - p.factor ^ k * u' t s) * c s =
            ∑ s, ((1 - p.factor ^ k) * u' x s + p.factor ^ k * (u' x s - u' t s)) * c s := by
          have e1 : ∑ s, (uT x s - p.factor ^ k * u' t s) * c s =
              ∑ s, uT x s * c s - ∑ s, p.factor ^ k * u' t s * c s := by
            rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun s _ => by ring
          have e2 : ∑ s, ((1 - p.factor ^ k) * u' x s + p.factor ^ k * (u' x s - u' t s)) * c s =
              ∑ s, u' x s * c s - ∑ s, p.factor ^ k * u' t s * c s := by
            rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun s _ => by ring
          rw [e1, e2, htr]
        rw [e]
        have hxT' : x ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior :=
          FEM.Poly.simplexMap_lexEnum_mem hgT' hg hξ
        have hxt : ‖x - t‖ ≤ 2 * (γ * h) := by rw [norm_sub_rev]; exact hxt'
        calc √h ^ n * |∑ s, ((1 - p.factor ^ k) * u' x s + p.factor ^ k * (u' x s - u' t s)) * c s|
            ≤ √h ^ n * ∑ s, ((k * 2 ^ k * (2 * γ)) * |u' x s| + 2 ^ k * |u' x s - u' t s|) *
                |c s| := by
              refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
                (Finset.sum_le_sum fun s _ => ?_)) hsq.le
              rw [abs_mul]
              refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
              refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
              · rw [abs_mul]; exact mul_le_mul_of_nonneg_right hdef (abs_nonneg _)
              · rw [abs_mul, abs_of_nonneg hck0]
                exact mul_le_mul_of_nonneg_right hck (abs_nonneg _)
          _ = ∑ s, ((k * 2 ^ k * (2 * γ)) * (√h ^ n * |u' x s|) +
                2 ^ k * ((√h ^ n * h * |u' x s - u' t s|) / h)) * |c s| := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => by field_simp
          _ ≤ ∑ s, ((k * 2 ^ k * (2 * γ)) * (A * √L) + 2 ^ k * ((A * (2 * (γ * h)) * √L) / h)) *
                |c s| := by
              refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right
                (add_le_add ?_ (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hh.le)
                  (by positivity))) (abs_nonneg _)
              · exact mul_le_mul_of_nonneg_left ((hT'inv.1 x hxT' s).trans
                  (mul_le_mul_of_nonneg_left hsqL' hA0)) (by positivity)
              · refine (hT'inv.2 x hxT' t htT'c s).trans ?_
                refine mul_le_mul (mul_le_mul_of_nonneg_left hxt hA0) hsqL'
                  (Real.sqrt_nonneg _) (by positivity)
          _ = ∑ s, (2 ^ k * ((k + 1) * (2 * γ)) * (A * √L)) * |c s| := by
              refine Finset.sum_congr rfl fun s _ => by field_simp
          _ ≤ ∑ s, (2 ^ (k + 1) * ((k + 1) * (2 * γ)) * (A * √L)) * |c s| := by
              refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              rw [pow_succ]
              have : 0 ≤ (2 : ℝ) ^ k * ((k + 1) * (2 * γ)) := by positivity
              nlinarith
          _ = (∑ s, |c s|) * A * √L * 2 ^ (k + 1) * ((k + 1) * (2 * γ)) := by
              rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
              refine Finset.sum_congr rfl fun s _ => by ring
    · -- a sample outside `Ω`: the zero extension vanishes there
      have hext : ∀ s, FEM.extField v t s = 0 := fun s => by
        simp [FEM.extField, formExt, Set.indicator_of_notMem htΩ]
      have hGt : G t = ∑ s, uT x s * c s := by simp only [G, hext]; simp
      rw [hGt]
      by_cases hbad : ξ ∈ FEM.nearBdry m θ
      · have hR' : Rb = (∑ s, |c s|) * A * √L * 2 ^ (k + 1) * 1 := by
          simp only [Rb, hbad, ite_true]
        rw [hR']
        calc √h ^ n * |∑ s, uT x s * c s| ≤ √h ^ n * ∑ s, |uT x s| * |c s| := by
              refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
                (le_of_eq (Finset.sum_congr rfl fun s _ => abs_mul _ _))) hsq.le
          _ ≤ (∑ s, |c s|) * A * √L := hbT
          _ ≤ (∑ s, |c s|) * A * √L * 2 ^ (k + 1) * 1 := by
              rw [mul_one]
              exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
      · have h0 := hs T g hgT hg ξ hξ hbad t hdist htΩ
        have hpb : pullback (simplexMatrix q) (uT x) =
            pullback (simplexMatrix q) ((0 : FormField n) x) :=
          S.pullback_eq_of_dof_eq hgT hg huT (Submodule.zero_mem _) (fun g' hg' i => by
            rw [show (⟨(0 : FormField n), S.space_le_contForms n k (Submodule.zero_mem _)⟩ :
              contForms n) = 0 from rfl, map_zero]
            exact h0 g' hg' i) ξ
        have h00 := hc _ _ (PolyKind.isDeg_of_mem_space huT x) (fun s _ => rfl) hpb
        have hz : ∑ s, uT x s * c s = 0 := by rw [h00]; simp
        rw [hz, abs_zero, mul_zero]
        have hR' : Rb = (∑ s, |c s|) * A * √L * 2 ^ (k + 1) * ((k + 1) * (2 * γ)) := by
          simp only [Rb, hbad, ite_false]
        rw [hR']
        exact mul_nonneg hR0 (by positivity)
  have hmain := FEM.abs_integral_mul_le_of_ae hρ0 hρi hρ1 hρG hb
  rw [le_div_iff₀ hsq, mul_comm] at hmain
  exact hmain

/-- **The DOF error of `Q` on `Vₕ`** for an admissible sequence: for a face `g` of `T` and a degree
of freedom `i` of `g`,
`h^{n/2} |ℓ_{g,i}(v_T - R v)| ≤ 2 (n + 1) D 2^{k+1} A (γ + θ) hᵏ m_T(v)^{1/2}`. -/
theorem sqrt_mul_abs_polyDof_err_le {M : SimplicialMesh n} (hΩ : MeasurableSet M.domain)
    (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) {k : ℕ} {A D : ℝ}
    (hA0 : 0 ≤ A) (hA : InvBoundV M (S.space n k) A) (hD0 : 0 ≤ D)
    (hD : PolyCoeffBound S n k D) {p : SmoothingParam (Fin n → ℝ)}
    (hp : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hhR : M.meshSize ≤ 2 * R)
    (hh : 0 < M.meshSize) (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hσ1 : σ ≤ 1) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hgeom : PolyGeomOK M p θ) {u : (polyElement n S).Piecewise M k}
    (hu : u ∈ (polyElement n S).globalSpace M k) (hs : PolySampleOK S p θ u) (T : M.simplices)
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n))
    (i : S.DofIdx g k) :
    √M.meshSize ^ n * |S.dof g k i ⟨((u T : (polyElement n S).space T k) : FormField n),
        S.space_le_contForms n k (u T).2⟩ -
      S.dof g k i (Submodule.inclusion c1Forms_le_contForms
        (smoothForm p hΩ k ((polyElement n S).glue M k u)))| ≤
      2 * (n + 1) * D * 2 ^ (k + 1) * A * (γ + θ) * M.meshSize ^ k *
        √(locMass (2 * M.meshSize) ((polyElement n S).glue M k u)
          (T : Affine.Simplex ℝ (Fin n → ℝ) n)) := by
  classical
  set h := M.meshSize
  have hne := i.2
  set m := #g - 1
  have hg : #g = m + 1 := (Nat.succ_pred_eq_of_pos (card_pos.2 hne)).symm
  have hkm : k ≤ m := by have := FEM.Poly.card_le_of_dofIdx S i; omega
  have hmn : m ≤ n := by
    have := Finset.card_le_card hgT
    rw [card_vertexSet] at this; omega
  set q := lexEnum g m
  set η := (S.testBasis k m i.1 : FormField m)
  set uT : FormField n := ((u T : (polyElement n S).space T k) : FormField n)
  have huT : uT ∈ S.space n k := (u T).2
  set w : c1Forms n := smoothForm p hΩ k ((polyElement n S).glue M k u)
  set L := locMass (2 * h) ((polyElement n S).glue M k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have huc : Continuous uT := (PolyKind.contDiff_of_mem_space huT).continuous
  have hwc : Continuous (w : FormField n) := (mem_c1Forms.1 w.2).continuous
  set F : (Fin m → ℝ) → ℝ := fun ξ =>
    ∑ s, (uT (simplexMap q ξ) s - (w : FormField n) (simplexMap q ξ) s) * dofCoeff q η k ξ s
  have hdc : Continuous fun ξ : Fin m → ℝ => η ξ := S.continuous_testBasis k m i.1
  have hcoef : ∀ s, Continuous fun ξ => dofCoeff q η k ξ s := fun s => by
    simp only [dofCoeff]
    split_ifs
    · simp only [wedgeForm_apply]
      exact continuous_finsetSum _ fun a _ => continuous_const.mul
        ((continuous_apply _).comp hdc)
    · exact continuous_const
  have hFc : Continuous F := continuous_finsetSum _ fun s _ =>
    ((((continuous_apply s).comp (huc.comp (continuous_simplexMap q))).sub
      ((continuous_apply s).comp (hwc.comp (continuous_simplexMap q)))).mul (hcoef s))
  have herr : S.dof g k i ⟨uT, S.space_le_contForms n k huT⟩ -
      S.dof g k i (Submodule.inclusion c1Forms_le_contForms w) =
        ∫ ξ in FiniteElement.refSimplex m, F ξ := by
    rw [← map_sub, S.dof_eq_integral]
    refine setIntegral_congr_fun (measurableSet_refSimplex _) fun ξ _ => ?_
    refine Finset.sum_congr rfl fun s _ => ?_
    rfl
  have hsq : 0 ≤ √h ^ n := pow_nonneg (Real.sqrt_nonneg _) n
  set Mc := D * h ^ k
  have hMc : ∀ ξ ∈ FiniteElement.refSimplex m, ∑ s, |dofCoeff q η k ξ s| ≤ Mc :=
    fun ξ hξ => (hD hgT i ξ hξ).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (diam_nonneg _) (M.diam_le_meshSize T.2) k) hD0)
  have hMc0 : 0 ≤ Mc := by positivity
  set β : (Fin m → ℝ) → ℝ := fun ξ =>
    Mc * A * √L * 2 ^ (k + 1) * ((k + 1) * (2 * γ) + 2 * (FEM.nearBdry m θ).indicator 1 ξ)
  have hpt : ∀ ξ ∈ FiniteElement.refSimplex m, √h ^ n * |F ξ| ≤ β ξ := by
    intro ξ hξ
    refine (sqrt_mul_abs_polyIntegrand_le S hΩ hint hA0 hA hp hR hRx hhR hh hγ hγ2 hσ1 hgeom hu
      hs T hgT hg hξ (dofCoeff q η k ξ)
      (fun α β hα hβ hαβ => sum_mul_dofCoeff_eq_of_pullback_eq q η ξ hα hβ hαβ)).trans ?_
    have h0 : 0 ≤ A * √L * 2 ^ (k + 1) := by positivity
    have h1 : (∑ s, |dofCoeff q η k ξ s|) * A * √L * 2 ^ (k + 1) ≤
        Mc * A * √L * 2 ^ (k + 1) := by
      have := mul_le_mul_of_nonneg_right (hMc ξ hξ) h0
      linarith [show (∑ s, |dofCoeff q η k ξ s|) * A * √L * 2 ^ (k + 1) =
        (∑ s, |dofCoeff q η k ξ s|) * (A * √L * 2 ^ (k + 1)) by ring,
        show Mc * A * √L * 2 ^ (k + 1) = Mc * (A * √L * 2 ^ (k + 1)) by ring]
    have hfac : 0 ≤ (if ξ ∈ FEM.nearBdry m θ then 1 else (k + 1) * (2 * γ) : ℝ) := by
      split_ifs <;> positivity
    refine (mul_le_mul_of_nonneg_right h1 hfac).trans ?_
    have h0' : 0 ≤ Mc * A * √L * 2 ^ (k + 1) := by positivity
    refine mul_le_mul_of_nonneg_left ?_ h0'
    by_cases hb : ξ ∈ FEM.nearBdry m θ
    · rw [Set.indicator_of_mem hb, Pi.one_apply]; simp only [hb, ↓reduceIte]
      have : 0 ≤ (k + 1 : ℝ) * (2 * γ) := by positivity
      linarith
    · rw [Set.indicator_of_notMem hb]; simp [hb]
  have hS : MeasurableSet (FiniteElement.refSimplex m) := measurableSet_refSimplex m
  have hfin : volume (FiniteElement.refSimplex m) ≠ ⊤ := (volume_refSimplex_lt_top m).ne
  set cc := Mc * A * √L * 2 ^ (k + 1)
  have hβ' : ∀ ξ, β ξ = cc * ((k + 1) * (2 * γ)) +
      (cc * 2) * (FEM.nearBdry m θ).indicator 1 ξ := fun ξ => by
    simp only [β, cc]; ring
  have hind : IntegrableOn (fun ξ => (FEM.nearBdry m θ).indicator (1 : (Fin m → ℝ) → ℝ) ξ)
      (FiniteElement.refSimplex m) :=
    (integrableOn_const hfin).indicator (FEM.isOpen_nearBdry m θ).measurableSet
  have hβi : IntegrableOn β (FiniteElement.refSimplex m) := by
    have : IntegrableOn (fun ξ => cc * ((k + 1) * (2 * γ)) +
        (cc * 2) * (FEM.nearBdry m θ).indicator 1 ξ) (FiniteElement.refSimplex m) :=
      (integrableOn_const hfin).add (hind.const_mul _)
    exact this.congr_fun (fun ξ _ => (hβ' ξ).symm) hS
  have hint' : ∫ ξ in FiniteElement.refSimplex m, β ξ =
      cc * ((k + 1) * (2 * γ) * volume.real (FiniteElement.refSimplex m) +
        2 * volume.real (FiniteElement.refSimplex m ∩ FEM.nearBdry m θ)) := by
    simp_rw [hβ']
    rw [integral_add (integrableOn_const hfin) (hind.const_mul _), setIntegral_const, smul_eq_mul,
      integral_const_mul (cc * 2), integral_indicator_one (FEM.isOpen_nearBdry m θ).measurableSet,
      Measure.real, Measure.real, Measure.restrict_apply (FEM.isOpen_nearBdry m θ).measurableSet,
      Set.inter_comm]
    simp only [Measure.real]
    ring
  have hvol := FEM.Poly.volume_real_refSimplex_le_one m
  have hbad := FEM.volume_real_nearBdry_le (k := m) hθ0 hθ1
  rw [herr]
  have hc0 : 0 ≤ cc := by positivity
  calc √h ^ n * |∫ ξ in FiniteElement.refSimplex m, F ξ|
      ≤ √h ^ n * ∫ ξ in FiniteElement.refSimplex m, |F ξ| :=
        mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs) hsq
    _ = ∫ ξ in FiniteElement.refSimplex m, √h ^ n * |F ξ| := (integral_const_mul _ _).symm
    _ ≤ ∫ ξ in FiniteElement.refSimplex m, β ξ :=
        setIntegral_mono_on ((hFc.abs.continuousOn.integrableOn_compact
          (isCompact_refSimplex m)).const_mul _) hβi hS hpt
    _ = cc * ((k + 1) * (2 * γ) * volume.real (FiniteElement.refSimplex m) +
        2 * volume.real (FiniteElement.refSimplex m ∩ FEM.nearBdry m θ)) := hint'
    _ ≤ cc * ((k + 1) * (2 * γ) * 1 + 2 * ((m + 1) * θ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        have : 0 ≤ (k + 1 : ℝ) * (2 * γ) := by positivity
        nlinarith
    _ ≤ cc * (2 * (n + 1) * (γ + θ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        have hk' : (k : ℝ) ≤ n := by exact_mod_cast hkm.trans hmn
        have hm' : (m : ℝ) ≤ n := by exact_mod_cast hmn
        nlinarith
    _ = 2 * (n + 1) * D * 2 ^ (k + 1) * A * (γ + θ) * h ^ k * √L := by simp only [cc, Mc]; ring

/-- **The local `L²` error of `Q` on `Vₕ`** for an admissible sequence:
`‖v - Q v‖²_{L²(T)} ≲ (γ + θ)² m_T(v)`. -/
theorem sum_integral_sq_sub_polyInterp_le {M : SimplicialMesh n} [NeZero n] {C c q : ℝ}
    (hM : MeshData M C c q) (hq : 0 < q) (hΩ : MeasurableSet M.domain)
    (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) {k : ℕ} {A B D : ℝ}
    (hA0 : 0 ≤ A) (hA : InvBoundV M (S.space n k) A) (hB : PolyDofBound S n k C c B)
    (hD0 : 0 ≤ D) (hD : PolyCoeffBound S n k D) {p : SmoothingParam (Fin n → ℝ)}
    (hp : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hhR : M.meshSize ≤ 2 * R)
    (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hσ1 : σ ≤ 1) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hgeom : PolyGeomOK M p θ) {u : (polyElement n S).Piecewise M k}
    (hu : u ∈ (polyElement n S).globalSpace M k) (hs : PolySampleOK S p θ u)
    (T : M.simplices) :
    ∑ s : formIdx n k, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      ((((u T : (polyElement n S).space T k) : FormField n) -
        ((((polyElement n S).globalInterp M k
          (Submodule.inclusion c1Forms_le_contForms
            (smoothForm p hΩ k ((polyElement n S).glue M k u))) :
            (polyElement n S).Piecewise M k) T : (polyElement n S).space T k) :
              FormField n)) y s.1) ^ 2 ≤
      4 ^ n * (B * (2 * (n + 1) * D * 2 ^ (k + 1) * A) * (γ + θ) / q ^ k) ^ 2 *
        locMass (2 * M.meshSize) ((polyElement n S).glue M k u)
          (T : Affine.Simplex ℝ (Fin n → ℝ) n) := by
  set h := M.meshSize
  have hh : 0 < h := hM.meshSize_pos
  set w := smoothForm p hΩ k ((polyElement n S).glue M k u)
  set Pw : (polyElement n S).space T k := (((polyElement n S).globalInterp M k
    (Submodule.inclusion c1Forms_le_contForms w) : (polyElement n S).Piecewise M k) T)
  set uT : FormField n := ((u T : (polyElement n S).space T k) : FormField n)
  have huT : uT ∈ S.space n k := (u T).2
  have hPw : (Pw : FormField n) ∈ S.space n k := Pw.2
  set z : FormField n := uT - (Pw : FormField n)
  have hz : z ∈ S.space n k := Submodule.sub_mem _ huT hPw
  set L := locMass (2 * h) ((polyElement n S).glue M k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have hL0 : 0 ≤ L := locMass_nonneg _ _ _
  set C₁ := 2 * (n + 1) * D * 2 ^ (k + 1) * A
  have hC₁ : 0 ≤ C₁ := by positivity
  have hsq : 0 < √h ^ n := pow_pos (Real.sqrt_pos.2 hh) n
  have hγθ : 0 ≤ γ + θ := by linarith
  set D'' := C₁ * (γ + θ) * √L / √h ^ n
  have hD''0 : 0 ≤ D'' := by positivity
  have hdof : ∀ g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n), ∀ i : S.DofIdx g k,
      |S.dof g k i ⟨z, S.space_le_contForms n k hz⟩| ≤ h ^ k * D'' := by
    intro g hgT i
    have e1 : S.dof g k i ⟨(Pw : FormField n), S.space_le_contForms n k hPw⟩ =
        S.dof g k i (Submodule.inclusion c1Forms_le_contForms w) :=
      (polyElement n S).localDof_globalInterp M k
        (Submodule.inclusion c1Forms_le_contForms w) T g hgT i
    have e : S.dof g k i ⟨z, S.space_le_contForms n k hz⟩ =
        S.dof g k i ⟨uT, S.space_le_contForms n k huT⟩ -
          S.dof g k i (Submodule.inclusion c1Forms_le_contForms w) := by
      rw [← e1, ← map_sub]; rfl
    rw [e]
    have h1 := sqrt_mul_abs_polyDof_err_le S hΩ hint hA0 hA hD0 hD hp hR hRx hhR hh hγ hγ2 hσ1
      hθ0 hθ1 hgeom hu hs T hgT i
    have e2 : h ^ k * D'' = C₁ * (γ + θ) * h ^ k * √L / √h ^ n := by
      simp only [D'']; ring
    rw [e2, le_div_iff₀ hsq, mul_comm]
    refine h1.trans (le_of_eq ?_)
    simp only [C₁]; ring
  have hzb : ∀ y ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ∀ s,
      |z y s| ≤ B * D'' / q ^ k :=
    fun y hy s => abs_le_of_abs_polyDof_le S hM hq hB T.2 hz hD''0 hdof hy s
  have hzc : Continuous z := (PolyKind.contDiff_of_mem_space hz).continuous
  have hloc : ∀ s : formIdx n k, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      (z y s.1) ^ 2 ≤ (2 * h) ^ n * (B * D'' / q ^ k) ^ 2 := by
    intro s
    refine (integral_closedInterior_le (f := fun y => (z y s.1) ^ 2)
      (A := (B * D'' / q ^ k) ^ 2)
      (((continuous_apply s.1).comp hzc).pow 2) (fun y hy => ?_) (fun y => sq_nonneg _)).trans ?_
    · rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hzb y hy s.1) 2
    · have hT0 := diam_nonneg (T : Affine.Simplex ℝ (Fin n → ℝ) n)
      have hTh := M.diam_le_meshSize T.2
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (by linarith) n)
        (sq_nonneg _)
  have hhn : h ^ n = (√h ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hh.le]
  calc ∑ s : formIdx n k, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
        (z y s.1) ^ 2
      ≤ ∑ _s : formIdx n k, (2 * h) ^ n * (B * D'' / q ^ k) ^ 2 :=
        Finset.sum_le_sum fun s _ => hloc s
    _ = Fintype.card (formIdx n k) * ((2 * h) ^ n * (B * D'' / q ^ k) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 2 ^ n * ((2 * h) ^ n * (B * D'' / q ^ k) ^ 2) :=
        mul_le_mul_of_nonneg_right (FEM.card_formIdx_le _) (by positivity)
    _ = 4 ^ n * (B * C₁ * (γ + θ) / q ^ k) ^ 2 * (√L) ^ 2 := by
        rw [mul_pow 2 h, hhn, show (4 : ℝ) ^ n = 2 ^ n * 2 ^ n by
          rw [← mul_pow]; norm_num]
        simp only [D'']
        field_simp
    _ = 4 ^ n * (B * C₁ * (γ + θ) / q ^ k) ^ 2 * L := by rw [Real.sq_sqrt hL0]

/-- **`Q` is close to the identity on `Vₕ`** for an admissible sequence:
`‖v - Q v‖² ≤ 4ⁿ (B C₁ (γ + θ) / qᵏ)² 6ⁿ n! / (c qⁿ) ‖v‖²`, `C₁ = 2 (n + 1) D 2^{k+1} A`. -/
theorem norm_sq_sub_polySmoothedInterp_le {M : SimplicialMesh n} [NeZero n] {C c q : ℝ}
    (hM : MeshData M C c q) (hc : 0 < c) (hq : 0 < q) (hΩ : MeasurableSet M.domain)
    (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) {k : ℕ} {A B D : ℝ}
    (hA0 : 0 ≤ A) (hA : InvBoundV M (S.space n k) A) (hB : PolyDofBound S n k C c B)
    (hD0 : 0 ≤ D) (hD : PolyCoeffBound S n k D) {p : SmoothingParam (Fin n → ℝ)}
    (hp : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hhR : M.meshSize ≤ 2 * R)
    (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hσ1 : σ ≤ 1) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hgeom : PolyGeomOK M p θ) {u : (polyElement n S).Piecewise M k}
    (hu : u ∈ (polyElement n S).globalSpace M k) (hs : PolySampleOK S p θ u) :
    ‖(polyElement n S).glue M k u - (polyElement n S).smoothedInterp M p hΩ k
        ((polyElement n S).glue M k u)‖ ^ 2 ≤
      4 ^ n * (B * (2 * (n + 1) * D * 2 ^ (k + 1) * A) * (γ + θ) / q ^ k) ^ 2 *
        (covConst n c q * ‖(polyElement n S).glue M k u‖ ^ 2) := by
  set v := (polyElement n S).glue M k u
  have hQ := (polyElement n S).smoothedInterp_natCast M p hΩ k v
  set Pw := (polyElement n S).globalInterp M k (Submodule.inclusion c1Forms_le_contForms
    (smoothForm p hΩ k v))
  set d : (polyElement n S).Piecewise M k := u - (Pw : (polyElement n S).Piecewise M k)
  have hsub : v - (polyElement n S).smoothedInterp M p hΩ k v =
      (polyElement n S).glue M k d := by
    rw [hQ, map_sub]
  have hglue : (polyElement n S).glue M k d = pieceL2 M M.domain
      (fun T => formComp (k := (k : ℤ)) ((polyElement n S).extendPW M d T))
      (fun T hT s => continuous_formComp ((polyElement n S).contDiff_extendPW M _
        hT).continuous s) := rfl
  have h1 := norm_sq_pieceL2_le M M.domain (fun T => formComp (k := (k : ℤ))
    ((polyElement n S).extendPW M d T))
    (fun T hT s => continuous_formComp ((polyElement n S).contDiff_extendPW M _
      hT).continuous s)
  set K := 4 ^ n * (B * (2 * (n + 1) * D * 2 ^ (k + 1) * A) * (γ + θ) / q ^ k) ^ 2
  have h2 : ∑ T ∈ M.simplices, ∑ s : formIdx n k, ∫ y in T.closedInterior,
      (formComp (k := (k : ℤ)) ((polyElement n S).extendPW M d T) s y) ^ 2 ≤
      ∑ T ∈ M.simplices, K * locMass (2 * M.meshSize) v T := by
    refine Finset.sum_le_sum fun T hT => ?_
    have e : ∀ s : formIdx n k, ∀ y, formComp (k := (k : ℤ))
        ((polyElement n S).extendPW M d T) s y =
        ((((u ⟨T, hT⟩ : (polyElement n S).space T k) : FormField n) -
          (((Pw : (polyElement n S).Piecewise M k) ⟨T, hT⟩ :
            (polyElement n S).space T k) : FormField n)) y s.1) := fun s y => by
      change (polyElement n S).extendPW M d T y s.1 = _
      rw [(polyElement n S).extendPW_of_mem M _ hT]
      rfl
    simp_rw [e]
    exact sum_integral_sq_sub_polyInterp_le S hM hq hΩ hint hA0 hA hB hD0 hD hp hR hRx hhR hγ
      hγ2 hσ1 hθ0 hθ1 hgeom hu hs ⟨T, hT⟩
  have h3 := sum_locMass_le hM hc hq hΩ v
  rw [hsub, hglue]
  refine h1.trans (h2.trans ?_)
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

end Close

/-! ### The geometric and sampling conditions for both families -/

section Families

variable (S : PolySeq) {x₀ : Fin n → ℝ} {s₀ R σ γ : ℝ}

/-- Points of a face with barycentric weights `≥ θ` (lexicographic parametrization) are face
points. -/
theorem isFacePoint_lexEnum {M : SimplicialMesh n} {m : ℕ} {g : Finset (Fin n → ℝ)}
    (hg : #g = m + 1) {θ : ℝ} {ξ : Fin m → ℝ} (hξ : ξ ∉ FEM.nearBdry m θ) :
    StarGeom.IsFacePoint M g θ (simplexMap (lexEnum g m) ξ) := by
  rw [simplexMap_eq_sum]
  refine StarGeom.isFacePoint_sum_smul (lexEnum_injective hg) (range_lexEnum hg)
    (fun a => ?_) (sum_refBary ξ)
  by_contra hlt; push Not at hlt; exact hξ ⟨a, hlt⟩

/-- **The geometric condition for the maximal family**, for the faces of all dimensions. -/
theorem polyGeomOK_of_isMaximal [NeZero n] {M : SimplicialMesh n} {C c q : ℝ}
    (hM : MeshData M C c q) (hq : 0 < q) (hC : 0 ≤ C) (hstar : StarBall M.domain x₀ s₀)
    (hs₀ : 0 < s₀) {p : SmoothingParam (Fin n → ℝ)} (hp : p.IsMaximal x₀ s₀)
    (hpA : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hσ1 : σ ≤ 1) (hγ : 0 < γ) {θ : ℝ}
    (hθ : 2 * (n * ((n + 1) * C)) / q * γ < θ) : PolyGeomOK M p θ := by
  intro T g hgT m hg ξ hξ hξb t ht T' htT'
  have hh := hM.meshSize_pos
  set x := simplexMap (lexEnum g m) ξ
  have hx := isFacePoint_lexEnum (M := M) hg hξb
  have hxT := FEM.Poly.simplexMap_lexEnum_mem hgT hg hξ
  have hxc := M.closedInterior_subset_closure T.2 hxT
  obtain ⟨h1, h2⟩ := path_of_isMaximal hstar hs₀ hp hxc ht
  have hgh := hpA.gh_nonneg hR
  have hŷ : ‖(p.center + p.factor • (x - p.center)) - x‖ ≤ 2 * (γ * M.meshSize) :=
    (hpA.norm_dil_sub_le hR (hRx x hxc)).trans (by linarith)
  have ht' : ‖t - x‖ ≤ 2 * (γ * M.meshSize) :=
    hpA.norm_sub_le_of_dist_le hR hσ1 (hRx x hxc) ht.le
  have hxx : ‖x - x‖ ≤ 2 * (γ * M.meshSize) := by rw [sub_self, norm_zero]; positivity
  exact StarGeom.subset_vertexSet_of_segments (coordLip_of hM hq hC) hx
    (StarGeom.mem_starSet.2 ⟨T, T.2, hgT, hxT⟩) h1
    (fun y hy => coord_near hq hC hh hγ hθ (norm_sub_le_of_mem_segment hxx hŷ hy)) h2
    (fun y hy => coord_near hq hC hh hγ hθ (norm_sub_le_of_mem_segment hŷ ht' hy)) T'.2 htT'

/-- **The geometric condition for the minimal family**, for the faces of all dimensions. -/
theorem polyGeomOK_of_isMinimal [NeZero n] {M : SimplicialMesh n} {C c q : ℝ}
    (hM : MeshData M C c q) (hq : 0 < q) (hC : 0 ≤ C) (hstar : StarBall M.domain x₀ s₀)
    (hs₀ : 0 < s₀) (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain)
    {p : SmoothingParam (Fin n → ℝ)} (hp : p.IsMinimal x₀ s₀)
    (hpA : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hσ1 : σ ≤ 1) (hσ : σ ≤ s₀ / (16 * R))
    (hγ : 0 < γ) (hγh : γ * M.meshSize / R ≤ 1) {θ : ℝ}
    (hθ : 2 * (n * ((n + 1) * C)) / q * γ < θ) : PolyGeomOK M p θ := by
  intro T g hgT m hg ξ hξ hξb t ht T' htT'
  have hh := hM.meshSize_pos
  set x := simplexMap (lexEnum g m) ξ
  have hx := isFacePoint_lexEnum (M := M) hg hξb
  have hxT := FEM.Poly.simplexMap_lexEnum_mem hgT hg hξ
  have hxc := M.closedInterior_subset_closure T.2 hxT
  have htΩ := hint T' T'.2 htT'
  obtain ⟨h1, h2, h3⟩ := path_of_isMinimal hstar hs₀ hR hp hpA hγh hσ htΩ ht
  have hgh := hpA.gh_nonneg hR
  have htt : ‖x₀ + p.factor⁻¹ • (t - x₀) - x‖ ≤ 2 * (γ * M.meshSize) := by
    refine h3.trans ?_
    rw [hpA.rOut_eq]; nlinarith
  have ht' : ‖t - x‖ ≤ 2 * (γ * M.meshSize) :=
    hpA.norm_sub_le_of_dist_le hR hσ1 (hRx x hxc) ht.le
  have hxx : ‖x - x‖ ≤ 2 * (γ * M.meshSize) := by rw [sub_self, norm_zero]; positivity
  exact StarGeom.subset_vertexSet_of_segments (coordLip_of hM hq hC) hx
    (StarGeom.mem_starSet.2 ⟨T, T.2, hgT, hxT⟩) h1
    (fun y hy => coord_near hq hC hh hγ hθ (norm_sub_le_of_mem_segment hxx htt hy)) h2
    (fun y hy => coord_near hq hC hh hγ hθ (norm_sub_le_of_mem_segment htt ht' hy)) T'.2 htT'

/-- **The maximal family samples only inside `Ω`**, so the sampling condition holds for every
field. -/
theorem polySampleOK_of_isMaximal {M : SimplicialMesh n} (hstar : StarBall M.domain x₀ s₀)
    {p : SmoothingParam (Fin n → ℝ)} (hp : p.IsMaximal x₀ s₀) {θ : ℝ} {k : ℕ}
    (u : (polyElement n S).Piecewise M k) : PolySampleOK S p θ u := by
  intro T g hgT m hg ξ hξ _ t ht htΩ
  exfalso
  have hxT := FEM.Poly.simplexMap_lexEnum_mem hgT hg hξ
  have hxc := M.closedInterior_subset_closure T.2 hxT
  have := closedBall_dil_subset_of_starBall hstar p.half_le_factor hp.factor_lt_one hp.rOut_lt hxc
  rw [← hp.center_eq] at this
  exact htΩ (this (Metric.mem_closedBall.2 ht.le))

/-- **The minimal family satisfies the sampling condition on `V̊ₕ`**: a sample outside `Ω` near a
point of a face with weights `≥ θ` forces the face into a boundary facet
(`StarGeom.exists_isBoundaryFacet_of_near`), where the degrees of freedom of all its subfaces
vanish for the fields of `V̊ₕ`. -/
theorem polySampleOK_of_isMinimal [NeZero n] {M : SimplicialMesh n} {C c q : ℝ}
    (hM : MeshData M C c q) (hq : 0 < q) (hC : 0 ≤ C) (hstar : StarBall M.domain x₀ s₀)
    (hs₀ : 0 < s₀) {p : SmoothingParam (Fin n → ℝ)}
    (hpA : IsAdm x₀ R σ γ M.meshSize p) (hR : 0 < R)
    (hRx : ∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) (hσ1 : σ ≤ 1) (hγ : 0 < γ) {θ : ℝ}
    (hθ : 2 * (n * ((n + 1) * C)) / q * γ < θ) {k : ℕ}
    {u : (polyElement n S).Piecewise M k} (hu : u ∈ (polyElement n S).globalSpace₀ M k) :
    PolySampleOK S p θ u := by
  classical
  intro T g hgT m hg ξ hξ hξb t ht htΩ
  have hh := hM.meshSize_pos
  set x := simplexMap (lexEnum g m) ξ
  have hx := isFacePoint_lexEnum (M := M) hg hξb
  have hxT := FEM.Poly.simplexMap_lexEnum_mem hgT hg hξ
  have hxc := M.closedInterior_subset_closure T.2 hxT
  have ht' : ‖t - x‖ ≤ 2 * (γ * M.meshSize) :=
    hpA.norm_sub_le_of_dist_le hR hσ1 (hRx x hxc) ht.le
  have htc : t ∉ interior (closure M.domain) := fun h' =>
    htΩ (hstar.interior_closure_subset hs₀ h')
  obtain ⟨F, hF, hgF⟩ := StarGeom.exists_isBoundaryFacet_of_near (by positivity)
    (coordLip_of hM hq hC) hx T.2 hgT hxT htc (coord_near hq hC hh hγ hθ ht')
  obtain ⟨-, T'', hT'', hFT''⟩ := hF.1
  intro g' hg' j
  have h0 := hu.2 ⟨T'', hT''⟩ F hF hFT'' g' (hg'.trans hgF) j
  rw [hu.1 T ⟨T'', hT''⟩ g' (hg'.trans hgT) ((hg'.trans hgF).trans hFT'') j]
  exact h0

end Families

/-! ### The smoothing scale and the uniformly bounded cochain projections -/

section Estimates

variable (S : PolySeq) {x₀ : Fin n → ℝ}

variable (n) in
/-- **The smoothing scale** `γ` and the threshold `θ` for an admissible sequence, depending only
on `n, S, C, c, q`: for every admissible parameter at scale `γ h` (either family) satisfying the
geometric and sampling conditions at threshold `θ`, `‖v - Q v‖ ≤ ½ ‖v‖` on `Vₕ`. -/
theorem exists_polyGamma [NeZero n] {C c q : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hq : 0 < q) :
    ∃ γ θ : ℝ, 0 < γ ∧ γ ≤ 1 / 4 ∧ 0 ≤ θ ∧ θ ≤ 1 ∧ 2 * (n * ((n + 1) * C)) / q * γ < θ ∧
      ∀ (M : SimplicialMesh n), MeshData M C c q → ∀ (hΩ : MeasurableSet M.domain),
      (∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) →
      ∀ {R σ : ℝ}, 0 < R → (∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) → M.meshSize ≤ 2 * R →
      σ ≤ 1 → ∀ (p : SmoothingParam (Fin n → ℝ)), IsAdm x₀ R σ γ M.meshSize p →
      PolyGeomOK M p θ → ∀ (k : ℕ), ∀ u ∈ (polyElement n S).globalSpace M k,
        PolySampleOK S p θ u →
        ‖(polyElement n S).glue M k u - (polyElement n S).smoothedInterp M p hΩ k
          ((polyElement n S).glue M k u)‖ ≤ 1 / 2 * ‖(polyElement n S).glue M k u‖ := by
  classical
  choose A hA0 hA using fun k : ℕ => exists_polyInvBound (n := n) S k hC hc
  choose B hB0 hB using fun k : ℕ => exists_polyDofBound (n := n) S k C c
  choose D hD0 hD using fun k : ℕ => exists_polyCoeffBound (n := n) S k
  set K₀ : ℝ := 2 * (n * ((n + 1) * C)) / q + 1
  have hK₀ : 1 ≤ K₀ := by
    simp only [K₀]; have : 0 ≤ 2 * (n * ((n + 1) * C)) / q := by positivity
    linarith
  set A' : ℕ → ℝ := fun k => A k / √q ^ n / q
  have hA'0 : ∀ k, 0 ≤ A' k := fun k => by have := hA0 k; simp only [A']; positivity
  set x : ℕ → ℝ := fun k =>
    B k * (2 * (n + 1) * D k * 2 ^ (k + 1) * A' k) * (1 + K₀) / q ^ k
  have hx0 : ∀ k, 0 ≤ x k := fun k => by
    have := hB0 k; have := hA'0 k; have := hD0 k; simp only [x]; positivity
  set Sx := ∑ k ∈ Finset.range (n + 1), x k
  have hS : 0 ≤ Sx := Finset.sum_nonneg fun k _ => hx0 k
  set Kc : ℝ := max 1 (4 ^ n * covConst n c q)
  have hKc : 1 ≤ Kc := le_max_left _ _
  set γ₀ := 1 / (2 * (1 + Sx * Kc))
  have hpos : 0 < 1 + Sx * Kc := by nlinarith
  have hγ₀ : 0 < γ₀ := by positivity
  set γ := min (min (1 / 4) (1 / K₀)) γ₀
  have hγ : 0 < γ := lt_min (lt_min (by norm_num) (by positivity)) hγ₀
  have hγ4 : γ ≤ 1 / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hγK : γ ≤ 1 / K₀ := (min_le_left _ _).trans (min_le_right _ _)
  have hγγ₀ : γ ≤ γ₀ := min_le_right _ _
  refine ⟨γ, K₀ * γ, hγ, hγ4, by positivity, ?_, ?_, ?_⟩
  · calc K₀ * γ ≤ K₀ * (1 / K₀) := mul_le_mul_of_nonneg_left hγK (by linarith)
      _ = 1 := by field_simp
  · have : 2 * (n * ((n + 1) * C)) / q * γ < (2 * (n * ((n + 1) * C)) / q + 1) * γ := by
      nlinarith
    exact this
  intro M hM hΩ hint R σ hR hRx hhR hσ1 p hp hgeom k u hu hs
  by_cases hk : n < k
  · have := FEM.subsingleton_L2F_of_lt (Ω := M.domain) hk
    rw [Subsingleton.elim ((polyElement n S).glue M k u) 0]; simp
  push Not at hk
  have hInv := invBoundV_of hM hq (hA0 k) (hA k)
  have hθ0 : 0 ≤ K₀ * γ := by positivity
  have hθ1 : K₀ * γ ≤ 1 := by
    calc K₀ * γ ≤ K₀ * (1 / K₀) := mul_le_mul_of_nonneg_left hγK (by linarith)
      _ = 1 := by field_simp
  have h := norm_sq_sub_polySmoothedInterp_le S hM hc hq hΩ hint (hA'0 k) hInv (hB k) (hD0 k)
    (hD k) hp hR hRx hhR hγ (by linarith) hσ1 hθ0 hθ1 hgeom hu hs
  have hxk : x k ≤ Sx := Finset.single_le_sum (fun k _ => hx0 k) (Finset.mem_range.2 (by omega))
  have he : B k * (2 * (n + 1) * D k * 2 ^ (k + 1) * A' k) * (γ + K₀ * γ) /
      q ^ k = x k * γ := by simp only [x]; ring
  rw [he] at h
  have hq1 : 4 ^ n * (x k * γ) ^ 2 * covConst n c q ≤ 1 / 4 := by
    have h1 : 4 ^ n * (x k * γ) ^ 2 * covConst n c q ≤ Kc * (x k * γ₀) ^ 2 := by
      have hcov : 0 ≤ covConst n c q := by unfold covConst; positivity
      calc 4 ^ n * (x k * γ) ^ 2 * covConst n c q = (4 ^ n * covConst n c q) * (x k * γ) ^ 2 := by
            ring
        _ ≤ Kc * (x k * γ₀) ^ 2 := mul_le_mul (le_max_right _ _)
            (pow_le_pow_left₀ (by have := hx0 k; positivity)
              (mul_le_mul_of_nonneg_left hγγ₀ (hx0 k)) 2) (sq_nonneg _) (by linarith)
    exact h1.trans (FEM.sq_le_quarter hS hKc (hx0 k) hxk)
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) (h.trans ?_)
  calc 4 ^ n * (x k * γ) ^ 2 * (covConst n c q * ‖(polyElement n S).glue M k u‖ ^ 2)
      = (4 ^ n * (x k * γ) ^ 2 * covConst n c q) * ‖(polyElement n S).glue M k u‖ ^ 2 := by ring
    _ ≤ 1 / 4 * ‖(polyElement n S).glue M k u‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hq1 (sq_nonneg _)
    _ = (1 / 2 * ‖(polyElement n S).glue M k u‖) ^ 2 := by ring

/-- **Uniformly bounded smoothed cochain projections onto the complexes of an admissible sequence
on quasi-uniform shape-regular meshes of a domain star-shaped with respect to a ball**
([AFW2010], §5.4; [ChristiansenWinther2008]): there is `K`, depending only on `n`, `S`, the
shape-regularity and quasi-uniformity constants, `s₀` and `R` (mathematically only on the ratio
`s₀ / R`, which is not formalized here), such that every such mesh
`M` of `Ω` (star-shaped with respect to `B(x₀, s₀)`, `cl Ω ⊆ B̄(x₀, R)`) carries a cochain
projection onto `Vₕ(S, M) ⊆ HΛ(Ω)` (`P_{r_k}Λᵏ` or `P_{r_k}⁻Λᵏ` in degree `k`) bounded by `K` in
`L²` and in every graph norm. -/
theorem exists_uniform_polyCochainProjection [NeZero n] {C c q : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hq : 0 < q) {s₀ R : ℝ} (hs₀ : 0 < s₀) (hR : 0 < R) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (M : SimplicialMesh n), MeshData M C c q → ∀ (hΩo : IsOpen M.domain),
      StarBall M.domain x₀ s₀ → (∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) →
      ∃ π : ((polyElement n S).subcomplex M hΩo).CochainProjection,
        (∀ i x, ‖π.π i x‖ ≤ K * ‖x‖) ∧ ∀ i j, π.IsGraphBounded i j K := by
  obtain ⟨γ, θ, hγ, hγ4, hθ0, hθ1, hθ, hclose⟩ := exists_polyGamma n S (x₀ := x₀) hC hc hq
  set σ := sigmaOf s₀ R
  obtain ⟨K', hK'0, hbound⟩ := exists_norm_polySmoothedInterp_le S (x₀ := x₀) (R := R) hc hq hγ
    (by linarith) (sigmaOf_pos hs₀ hR) (sigmaOf_le_one s₀ R)
  refine ⟨max 1 (2 * K'), le_max_left _ _, fun M hM hΩo hstar hRx => ?_⟩
  set h := M.meshSize
  have hh := hM.meshSize_pos
  have hhR := meshSize_le_two_mul hR hRx
  have hγh2 : γ * h / R ≤ 1 / 2 := by
    rw [div_le_iff₀ hR]; nlinarith
  have hpos : 0 < γ * h * σ := by have := sigmaOf_pos hs₀ hR; positivity
  have hnn : 0 ≤ γ * h / R := by positivity
  set p := pMax x₀ R σ γ h hpos hγh2
  have hp : p.IsMaximal x₀ s₀ := pMax_isMaximal hR hpos hγh2 (by positivity) (sigmaOf_lt hs₀ hR)
  have hpA : IsAdm x₀ R σ γ h p := pMax_isAdm hpos hγh2 hnn
  have hint := interior_subset_domain hstar hs₀
  set Q := (polyElement n S).smoothedCommutingMap M p hΩo hstar hp
  have hQ : ∀ i, Q.Q i = (polyElement n S).smoothedInterp M p hΩo.measurableSet i :=
    fun i => rfl
  have hQb : ∀ i x, ‖Q.Q i x‖ ≤ K' * ‖x‖ := by
    intro i x
    rw [hQ]
    rcases i with k | k
    · exact hbound M hM hΩo.measurableSet hR hRx (by linarith) p hpA k x
    · exact (FEM.norm_eq_zero_negSucc k _).le.trans (by positivity)
  have hQc : ∀ i, ∀ v ∈ ((polyElement n S).subcomplex M hΩo).V i,
      ‖v - Q.Q i v‖ ≤ 1 / 2 * ‖v‖ := by
    intro i v hv
    rw [hQ]
    rcases i with k | k
    · obtain ⟨u, rfl⟩ := hv
      exact hclose M hM hΩo.measurableSet hint hR hRx hhR (sigmaOf_le_one s₀ R) p hpA
        (polyGeomOK_of_isMaximal hM hq hC hstar hs₀ hp hpA hR hRx (sigmaOf_le_one s₀ R) hγ hθ)
        k u.1 u.2 (polySampleOK_of_isMaximal S hstar hp u.1)
    · exact (FEM.norm_eq_zero_negSucc k _).le.trans (by positivity)
  refine ⟨Q.toCochainProjection (θ := 1 / 2) (by norm_num) hQc, fun i x => ?_, fun i j => ?_⟩
  · have h1 := Q.norm_toCochainProjection_le (θ := 1 / 2) (by norm_num) hQc (hQb i) x
    have e : (1 - 1 / 2 : ℝ)⁻¹ * K' = 2 * K' := by norm_num
    rw [e] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  · have h1 := Q.isGraphBounded_toCochainProjection_of_norm_le (θ := 1 / 2) (by norm_num) hQc
      (hQb i) (hQb j)
    have e : (1 - 1 / 2 : ℝ)⁻¹ * K' = 2 * K' := by norm_num
    rw [e] at h1
    exact h1.mono' (by positivity) (le_max_right _ _)

/-- **Uniformly bounded smoothed cochain projections onto the complexes of an admissible sequence
with vanishing boundary DOFs** `V̊ₕ(S, M) ⊆ H̊Λ(Ω)` on quasi-uniform shape-regular meshes of a
domain star-shaped with respect to a ball. The samples of the minimal-family smoother outside `Ω`
only meet faces lying in boundary facets (`StarGeom.exists_isBoundaryFacet_of_near`). -/
theorem exists_uniform_polyCochainProjectionMin [NeZero n] {C c q : ℝ} (hC : 0 ≤ C)
    (hc : 0 < c) (hq : 0 < q) {s₀ R : ℝ} (hs₀ : 0 < s₀) (hR : 0 < R) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (M : SimplicialMesh n), MeshData M C c q → ∀ (hΩo : IsOpen M.domain),
      ∀ (hstar : StarBall M.domain x₀ s₀), (∀ y ∈ closure M.domain, ‖y - x₀‖ ≤ R) →
      ∃ π : ((polyElement n S).subcomplexMin M hΩo x₀
          (fun _ hx _ ht0 ht1 => hstar.strict hs₀ hx ht0 ht1)).CochainProjection,
        (∀ i x, ‖π.π i x‖ ≤ K * ‖x‖) ∧ ∀ i j, π.IsGraphBounded i j K := by
  obtain ⟨γ, θ, hγ, hγ4, hθ0, hθ1, hθ, hclose⟩ := exists_polyGamma n S (x₀ := x₀) hC hc hq
  set σ := sigmaOf s₀ R
  obtain ⟨K', hK'0, hbound⟩ := exists_norm_polySmoothedInterp_le S (x₀ := x₀) (R := R) hc hq hγ
    (by linarith) (sigmaOf_pos hs₀ hR) (sigmaOf_le_one s₀ R)
  refine ⟨max 1 (2 * K'), le_max_left _ _, fun M hM hΩo hstar hRx => ?_⟩
  set h := M.meshSize
  have hh := hM.meshSize_pos
  have hhR := meshSize_le_two_mul hR hRx
  have hγh1 : γ * h / R ≤ 1 := by
    rw [div_le_iff₀ hR]; nlinarith
  have hpos : 0 < γ * h * σ := by have := sigmaOf_pos hs₀ hR; positivity
  have hnn : 0 ≤ γ * h / R := by positivity
  set p := pMin x₀ R σ γ h hpos hnn
  have hp : p.IsMinimal x₀ s₀ := pMin_isMinimal hR hpos hnn (by positivity) (sigmaOf_lt hs₀ hR)
  have hpA : IsAdm x₀ R σ γ h p := pMin_isAdm hpos hnn
  have hint := interior_subset_domain hstar hs₀
  have hb := isBounded_domain_of hRx
  set Q := (polyElement n S).smoothedCommutingMapMin M p hΩo hb hstar hp x₀
    (fun _ hx _ ht0 ht1 => hstar.strict hs₀ hx ht0 ht1)
  have hQ : ∀ i, Q.Q i = (polyElement n S).smoothedInterp M p hΩo.measurableSet i :=
    fun i => rfl
  have hQb : ∀ i x, ‖Q.Q i x‖ ≤ K' * ‖x‖ := by
    intro i x
    rw [hQ]
    rcases i with k | k
    · exact hbound M hM hΩo.measurableSet hR hRx hγh1 p hpA k x
    · exact (FEM.norm_eq_zero_negSucc k _).le.trans (by positivity)
  have hQc : ∀ i, ∀ v ∈ ((polyElement n S).subcomplexMin M hΩo x₀
      (fun _ hx _ ht0 ht1 => hstar.strict hs₀ hx ht0 ht1)).V i,
      ‖v - Q.Q i v‖ ≤ 1 / 2 * ‖v‖ := by
    intro i v hv
    rw [hQ]
    rcases i with k | k
    · obtain ⟨u, rfl⟩ := hv
      exact hclose M hM hΩo.measurableSet hint hR hRx hhR (sigmaOf_le_one s₀ R) p hpA
        (polyGeomOK_of_isMinimal hM hq hC hstar hs₀ hint hp hpA hR hRx (sigmaOf_le_one s₀ R)
          (sigmaOf_le s₀ R) hγ hγh1 hθ)
        k u.1 ((polyElement n S).globalSpace₀_le M k u.2)
        (polySampleOK_of_isMinimal S hM hq hC hstar hs₀ hpA hR hRx (sigmaOf_le_one s₀ R) hγ hθ
          u.2)
    · exact (FEM.norm_eq_zero_negSucc k _).le.trans (by positivity)
  refine ⟨Q.toCochainProjection (θ := 1 / 2) (by norm_num) hQc, fun i x => ?_, fun i j => ?_⟩
  · have h1 := Q.norm_toCochainProjection_le (θ := 1 / 2) (by norm_num) hQc (hQb i) x
    have e : (1 - 1 / 2 : ℝ)⁻¹ * K' = 2 * K' := by norm_num
    rw [e] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  · have h1 := Q.isGraphBounded_toCochainProjection_of_norm_le (θ := 1 / 2) (by norm_num) hQc
      (hQb i) (hQb j)
    have e : (1 - 1 / 2 : ℝ)⁻¹ * K' = 2 * K' := by norm_num
    rw [e] at h1
    exact h1.mono' (by positivity) (le_max_right _ _)

end Estimates

/-! ### The complexes of an admissible sequence on a mesh family -/

namespace MeshFamily

variable {D : StarDomain n} (F : MeshFamily D) [NeZero n] (S : PolySeq)

/-- **The complex `Vₕ(S, M_N)` of the admissible sequence `S`** (`P_{r_k}Λᵏ` or `P_{r_k}⁻Λᵏ` in
degree `k`) on the mesh `M_N`, as a subcomplex of `HΛ(Ω)`. -/
def poly (N : ℕ) : D.complex.Subcomplex :=
  (deRham ℝ n).maximalSubcomplexOfEq (F.domain_eq N) (F.isOpen_domain N) D.isOpen
    (S.subcomplex (F.mesh N) (F.isOpen_domain N))

instance (N : ℕ) (k : ℤ) : FiniteDimensional ℝ ((F.poly S N).V k) :=
  (deRham ℝ n).finiteDimensional_maximalSubcomplexOfEq _ _ _ _ k

/-- **The complex `V̊ₕ(S, M_N)` of `S` with vanishing boundary DOFs** on the mesh `M_N`, as a
subcomplex of `H̊Λ(Ω)`. -/
def polyMin (N : ℕ) : D.complexMin.Subcomplex :=
  (deRham ℝ n).minimalSubcomplexOfEq (F.domain_eq N) (F.isOpen_domain N) D.isOpen
    (S.subcomplexMin (F.mesh N) (F.isOpen_domain N) D.x₀ (F.strict_mesh N))

instance (N : ℕ) (k : ℤ) : FiniteDimensional ℝ ((F.polyMin S N).V k) :=
  (deRham ℝ n).finiteDimensional_minimalSubcomplexOfEq _ _ _ _ k

/-- **Uniformly bounded smoothed cochain projections onto the complexes of `S` on the family**,
in `L²` and in every graph norm of `HΛ(Ω)` ([AFW2010], §5.4; [ChristiansenWinther2008]), with no
hypothesis beyond shape regularity and quasi-uniformity. -/
theorem exists_uniform_polyProj : ∃ K : ℝ, 1 ≤ K ∧ ∀ N,
    ∃ π : (F.poly S N).CochainProjection,
      (∀ i x, ‖π.π i x‖ ≤ K * ‖x‖) ∧ ∀ i j, π.IsGraphBounded i j K := by
  obtain ⟨K, hK1, hK⟩ := exists_uniform_polyCochainProjection S (x₀ := D.x₀) F.C_nonneg F.c_pos
    F.q_pos D.s₀_pos D.R_pos
  refine ⟨K, hK1, fun N => ?_⟩
  obtain ⟨π, h1, h2⟩ := hK (F.mesh N) (F.data N) (F.isOpen_domain N) (F.starBall_mesh N)
    (F.norm_sub_le_mesh N)
  exact (deRham ℝ n).maximalSubcomplexOfEq_induction (F.domain_eq N) (F.isOpen_domain N)
    D.isOpen (S.subcomplex (F.mesh N) (F.isOpen_domain N))
    (fun Θ hΘ S' => ∃ π : S'.CochainProjection, (∀ i x, ‖π.π i x‖ ≤ K * ‖x‖) ∧
      ∀ i j, π.IsGraphBounded i j K) ⟨π, h1, h2⟩

/-- **Uniformly bounded smoothed cochain projections onto the complexes of `S` with vanishing
boundary DOFs on the family**, in `L²` and in every graph norm of `H̊Λ(Ω)`. -/
theorem exists_uniform_polyProjMin : ∃ K : ℝ, 1 ≤ K ∧ ∀ N,
    ∃ π : (F.polyMin S N).CochainProjection,
      (∀ i x, ‖π.π i x‖ ≤ K * ‖x‖) ∧ ∀ i j, π.IsGraphBounded i j K := by
  obtain ⟨K, hK1, hK⟩ := exists_uniform_polyCochainProjectionMin S (x₀ := D.x₀) F.C_nonneg
    F.c_pos F.q_pos D.s₀_pos D.R_pos
  refine ⟨K, hK1, fun N => ?_⟩
  obtain ⟨π, h1, h2⟩ := hK (F.mesh N) (F.data N) (F.isOpen_domain N) (F.starBall_mesh N)
    (F.norm_sub_le_mesh N)
  exact (deRham ℝ n).minimalSubcomplexOfEq_induction (F.domain_eq N) (F.isOpen_domain N)
    D.isOpen (S.subcomplexMin (F.mesh N) (F.isOpen_domain N) D.x₀ (F.strict_mesh N))
    (fun Θ hΘ S' => ∃ π : S'.CochainProjection, (∀ i x, ‖π.π i x‖ ≤ K * ‖x‖) ∧
      ∀ i j, π.IsGraphBounded i j K) ⟨π, h1, h2⟩

end MeshFamily

end Feec.Models.StarShaped
