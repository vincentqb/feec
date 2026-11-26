module

public import Feec.Models.Cube.SmoothingEstimates
public import Feec.Models.StarShaped.PolySmoothing

/-!
# Smoothed-projection estimates for the higher-order families on the cube

For every admissible sequence `S` on the Freudenthal meshes of `Q = (0, ½)ⁿ`, the smoothed
interpolants of the complexes `FEM.poly n S N ⊆ HΛ(Q)` and `FEM.polyMin n S N ⊆ H̊Λ(Q)` are bounded
in `L²` uniformly in `N` and close to the identity, for every small enough smoothing scale `γ`
([AFW2010], §5.5; [ChristiansenWinther2008]).

## Main results

* `FEM.polySmoothingEstimates_pMax`, `FEM.polySmoothingEstimatesMin_pMin`: the estimates.
* `FEM.exists_common_gamma`: one smoothing scale for finitely many families at once.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset Filter

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex ExteriorFibre

variable {n : ℕ}

namespace Poly

variable (S : PolySeq)

/-! ### Uniform local estimates on the mesh simplices -/

theorem abs_simplexMatrix_lexEnum_le {N : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T) {m : ℕ}
    (hg : #g = m + 1) (i : Fin n) (l : Fin m) :
    |simplexMatrix (lexEnum g m) i l| ≤ hN N := by
  obtain ⟨m', σ, rfl⟩ := mem_mesh_simplices.1 hT
  have hmem : ∀ a, lexEnum g m a ∈ (cubeSimplex N m' σ).closedInterior := fun a =>
    vertexSet_subset_closedInterior _ (hgT (lexEnum_mem hg a))
  have := norm_sub_le_of_mem_cubeSimplex (hmem l.succ) (hmem 0)
  refine le_trans ?_ this
  have h := norm_le_pi_norm (lexEnum g m l.succ - lexEnum g m 0) i
  rwa [Real.norm_eq_abs, Pi.sub_apply] at h

/-- The coefficient fields of the degrees of freedom of `S` are `O(h_Nᵏ)` on the mesh simplices. -/
def CoeffBound (n k : ℕ) (D : ℝ) : Prop :=
  ∀ (N : ℕ) {T : Affine.Simplex ℝ (Fin n → ℝ) n}, T ∈ (mesh n N).simplices →
    ∀ {g : Finset (Fin n → ℝ)}, g ⊆ vertexSet T → ∀ (i : S.DofIdx g k),
      ∀ ξ ∈ FiniteElement.refSimplex (#g - 1),
        ∑ s, |dofCoeff (lexEnum g (#g - 1)) (S.testBasis k (#g - 1) i.1 : FormField (#g - 1)) k
          ξ s| ≤ D * hN N ^ k

theorem exists_coeffBound (k : ℕ) : ∃ D, 0 ≤ D ∧ CoeffBound S n k D := by
  obtain ⟨D, hD0, hD⟩ := S.exists_coeffBound_of_le k
  exact ⟨D, hD0, fun N T hT g hgT i => hD hgT i (hN_pos N).le
    (abs_simplexMatrix_lexEnum_le hT hgT (Nat.succ_pred_eq_of_pos (card_pos.2 i.2)).symm)⟩

theorem abs_dof_le {k : ℕ} {D : ℝ} (hD : CoeffBound S n k D) {N : ℕ}
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ (mesh n N).simplices)
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T) (i : S.DofIdx g k) (ω : contForms n)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x ∈ T.closedInterior, ∀ s, |(ω : FormField n) x s| ≤ B) :
    |S.dof g k i ω| ≤ D * hN N ^ k * B :=
  S.abs_dof_le_of_coeff_le hgT i ω (hD N hT hgT i) hB0 hB

/-- The local DOF estimate `h_Nᵏ ‖z(x)‖ ≤ B Σ |ℓ_{g,i}(z)|` on the mesh simplices. -/
def DofBound (n k : ℕ) (B : ℝ) : Prop :=
  ∀ (N : ℕ) {T : Affine.Simplex ℝ (Fin n → ℝ) n}, T ∈ (mesh n N).simplices →
    ∀ {z : FormField n} (hz : z ∈ S.space n k), ∀ x ∈ T.closedInterior,
      hN N ^ k * ‖z x‖ ≤ B * ∑ p : Σ g : (vertexSet T).powerset, S.DofIdx (g : Finset (Fin n → ℝ)) k,
        |S.dof (p.1 : Finset (Fin n → ℝ)) k p.2 ⟨z, S.space_le_contForms n k hz⟩|

theorem exists_dofBound (k : ℕ) : ∃ B, 0 ≤ B ∧ DofBound S n k B := by
  obtain ⟨B, hB0, hB⟩ := S.exists_local_dof_bound_uniform (n := n) kuhnSimplex k
  refine ⟨B, hB0, fun N T hT z hz x hx => ?_⟩
  obtain ⟨m, σ, rfl⟩ := mem_mesh_simplices.1 hT
  rw [cubeSimplex_eq] at hx ⊢
  exact hB σ (hN_pos N) _ hz x hx

/-- The local inverse estimates of the spaces of `S` on the mesh simplices, with constant `A`. -/
def InvBound (n k : ℕ) (A : ℝ) : Prop :=
  ∀ (N : ℕ) {T : Affine.Simplex ℝ (Fin n → ℝ) n}, T ∈ (mesh n N).simplices →
    ∀ z ∈ S.space n k,
      (∀ x ∈ T.closedInterior, √(hN N) ^ n * ‖z x‖ ≤ A * √(formL2Sq T.closedInterior z)) ∧
      (∀ x ∈ T.closedInterior, ∀ x' ∈ T.closedInterior,
        √(hN N) ^ n * hN N * ‖z x - z x'‖ ≤ A * ‖x - x'‖ * √(formL2Sq T.closedInterior z))

theorem exists_invBound (k : ℕ) : ∃ A, 0 ≤ A ∧ InvBound S n k A := by
  choose A hA0 hA using fun σ : Equiv.Perm (Fin n) =>
    exists_local_inverse_bound_of_le_polySpace (S.space_le_polySpace k)
      (fun h t _ hu => S.affinePullback_mem_space_scalarMat k h t hu) (kuhnSimplex σ)
  have hle : ∀ σ, A σ ≤ ∑ σ, A σ := fun σ =>
    Finset.single_le_sum (fun σ _ => hA0 σ) (Finset.mem_univ σ)
  refine ⟨∑ σ, A σ, Finset.sum_nonneg fun σ _ => hA0 σ, fun N T hT z hz => ?_⟩
  obtain ⟨m, σ, rfl⟩ := mem_mesh_simplices.1 hT
  rw [cubeSimplex_eq]
  obtain ⟨h1, h2⟩ := hA σ (hN_pos N) _ z hz
  exact ⟨fun x hx => (h1 x hx).trans (mul_le_mul_of_nonneg_right (hle σ) (Real.sqrt_nonneg _)),
    fun x hx x' hx' => (h2 x hx x' hx').trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hle σ) (norm_nonneg _)) (Real.sqrt_nonneg _))⟩

/-! ### The uniform `L²` bound -/

theorem card_dofs_eq (T : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) :
    (Fintype.card (Σ g : (vertexSet T).powerset, S.DofIdx (g : Finset (Fin n → ℝ)) k) : ℝ) =
      Module.finrank ℝ (S.space n k) := by
  exact_mod_cast S.card_sigma_dofIdx T k

theorem abs_le_of_abs_dof_le {k : ℕ} {B : ℝ} (hB : DofBound S n k B) (hB0 : 0 ≤ B) {N : ℕ}
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ (mesh n N).simplices) {z : FormField n}
    (hz : z ∈ S.space n k) {D' : ℝ}
    (hD : ∀ g ⊆ vertexSet T, ∀ i : S.DofIdx g k,
      |S.dof g k i ⟨z, S.space_le_contForms n k hz⟩| ≤ hN N ^ k * D')
    {x : Fin n → ℝ} (hx : x ∈ T.closedInterior) (s : Finset (Fin n)) :
    |z x s| ≤ B * Module.finrank ℝ (S.space n k) * D' := by
  have hhk : 0 < hN N ^ k := pow_pos (hN_pos N) k
  have h1 := hB N hT hz x hx
  have h2 : ∑ p : Σ g : (vertexSet T).powerset, S.DofIdx (g : Finset (Fin n → ℝ)) k,
      |S.dof (p.1 : Finset (Fin n → ℝ)) k p.2 ⟨z, S.space_le_contForms n k hz⟩| ≤
      Module.finrank ℝ (S.space n k) * (hN N ^ k * D') := by
    calc _ ≤ ∑ _p : Σ g : (vertexSet T).powerset, S.DofIdx (g : Finset (Fin n → ℝ)) k,
          hN N ^ k * D' := Finset.sum_le_sum fun p _ => hD _ (Finset.mem_powerset.1 p.1.2) p.2
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_dofs_eq]
  have h3 : |z x s| ≤ ‖z x‖ := by
    have := norm_le_pi_norm (z x) s; rwa [Real.norm_eq_abs] at this
  refine le_of_mul_le_mul_left ?_ hhk
  calc hN N ^ k * |z x s| ≤ hN N ^ k * ‖z x‖ := mul_le_mul_of_nonneg_left h3 hhk.le
    _ ≤ B * (Module.finrank ℝ (S.space n k) * (hN N ^ k * D')) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 hB0)
    _ = hN N ^ k * (B * Module.finrank ℝ (S.space n k) * D') := by ring

theorem subset_vertexSet_of_near_lex {N : ℕ} {T T' : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) (hT' : T' ∈ (mesh n N).simplices) {m : ℕ}
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T) (hg : #g = m + 1) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) {μ : Fin (m + 1) → ℝ} (hμ : ∀ a, θ ≤ μ a)
    (hμ1 : ∑ a, μ a = 1) {t : Fin n → ℝ} (ht : t ∈ T'.closedInterior)
    (hxt : ‖∑ a, μ a • lexEnum g m a - t‖ < θ * hN N / 2) : g ⊆ vertexSet T' := by
  classical
  set q := lexEnum g m
  have hq := lexEnum_injective hg
  have hqT : ∀ a, q a ∈ vertexSet T := fun a => hgT (lexEnum_mem hg a)
  obtain ⟨m₀, σ, rfl⟩ := mem_mesh_simplices.1 hT
  obtain ⟨m', σ', rfl⟩ := mem_mesh_simplices.1 hT'
  have hj : ∀ a, ∃ j, q a = hN N • (latticePoint (finLattice m₀) + kuhnVertex σ j) := fun a => by
    obtain ⟨j, hj⟩ := mem_vertexSet.1 (hqT a)
    exact ⟨j, by rw [← hj, cubeSimplex_points]⟩
  choose j hj using hj
  set x := ∑ a, μ a • q a
  have hxs : (hN N)⁻¹ • x = latticePoint (finLattice m₀) + ∑ a, μ a • kuhnVertex σ (j a) := by
    have hh := hN_ne_zero N
    simp only [x, hj, Finset.smul_sum, smul_smul, smul_add, Finset.sum_add_distrib,
      ← Finset.sum_smul]
    have e1 : (hN N)⁻¹ * ∑ i, μ i * hN N = 1 := by
      rw [← Finset.sum_mul, hμ1]; field_simp
    have e2 : ∀ a, (hN N)⁻¹ * (μ a * hN N) = μ a := fun a => by field_simp
    simp only [e1, e2, one_smul]
  have hsep := isSep_latticePoint_add_sum hθ0.le hθ (finLattice m₀) σ j hμ hμ1
  rw [← hxs] at hsep
  have hx' : x ∈ (cubeSimplex N m' σ').closedInterior := by
    rw [mem_closedInterior_cubeSimplex] at ht ⊢
    refine mem_freudenthalSet_of_isSep hsep ht fun l => ?_
    have h := hN_pos N
    have : ‖(hN N)⁻¹ • x - (hN N)⁻¹ • t‖ < θ / 2 := by
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 h.le), inv_mul_lt_iff₀ h]
      linarith
    exact lt_of_le_of_lt (by
      have := norm_le_pi_norm ((hN N)⁻¹ • x - (hN N)⁻¹ • t) l
      rwa [Real.norm_eq_abs, Pi.sub_apply] at this) this
  intro v hv
  have : v ∈ Set.range q := by rw [range_lexEnum hg]; exact hv
  obtain ⟨a, rfl⟩ := this
  exact SimplicialMesh.subset_vertexSet_of_mem hT hT' hq hqT
    (fun a => hθ0.trans_le (hμ a)) hμ1 hx' a

theorem sum_integral_sq_globalInterp_le {N k : ℕ} {B D : ℝ} (hB : DofBound S n k B)
    (hB0 : 0 ≤ B) (hD : CoeffBound S n k D) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) {w : contForms n} {A : ℝ} (hA0 : 0 ≤ A)
    (hw : ∀ y ∈ T.closedInterior, ∀ s, |(w : FormField n) y s| ≤ A) :
    ∑ s : formIdx n k, ∫ y in T.closedInterior,
      (((((polyElement n S).globalInterp (mesh n N) k w :
        (polyElement n S).Piecewise (mesh n N) k) ⟨T, hT⟩ : (polyElement n S).space T k) :
          FormField n) y s.1) ^ 2 ≤
      2 ^ n * hN N ^ n * (B * Module.finrank ℝ (S.space n k) * (D * A)) ^ 2 := by
  set h := hN N
  have hh : 0 < h := hN_pos N
  set z : FormField n := ((((polyElement n S).globalInterp (mesh n N) k w :
    (polyElement n S).Piecewise (mesh n N) k) ⟨T, hT⟩ : (polyElement n S).space T k) :
      FormField n)
  have hz : z ∈ S.space n k := (((polyElement n S).globalInterp (mesh n N) k w :
      (polyElement n S).Piecewise (mesh n N) k) ⟨T, hT⟩).2
  have hdof : ∀ g ⊆ vertexSet T, ∀ i : S.DofIdx g k,
      |S.dof g k i ⟨z, S.space_le_contForms n k hz⟩| ≤ h ^ k * (D * A) := by
    intro g hgT i
    have e : S.dof g k i ⟨z, S.space_le_contForms n k hz⟩ = S.dof g k i w :=
      (polyElement n S).localDof_globalInterp (mesh n N) k w ⟨T, hT⟩ g hgT i
    rw [e]
    refine (abs_dof_le S hD hT hgT i _ hA0 hw).trans (le_of_eq ?_)
    ring
  have hzb : ∀ y ∈ T.closedInterior, ∀ s,
      |z y s| ≤ B * Module.finrank ℝ (S.space n k) * (D * A) :=
    fun y hy s => abs_le_of_abs_dof_le S hB hB0 hT hz hdof hy s
  exact (sum_integral_sq_le_of_abs_le hT (PolyKind.contDiff_of_mem_space hz).continuous
    hzb).trans (le_of_eq (by ring))

variable {γ : ℝ}

/-! ### The smoothing scale, uniformly for all small `γ` -/

theorem sq_le_quarter_of_le {S K x γ : ℝ} (hS : 0 ≤ S) (hK : 1 ≤ K) (hx0 : 0 ≤ x) (hx : x ≤ S)
    (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / (2 * (1 + S * K))) : K * (x * γ) ^ 2 ≤ 1 / 4 := by
  refine le_trans ?_ (sq_le_quarter hS hK hx0 hx)
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  exact pow_le_pow_left₀ (mul_nonneg hx0 hγ0) (mul_le_mul_of_nonneg_left hγ hx0) 2

end Poly

/-! ### The higher-order complexes of the cube and their smoothed interpolants -/

variable [NeZero n]

variable (n) in
theorem Poly.exists_gamma₀ (S : PolySeq) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 / 2 ∧ ∀ γ, 0 < γ → γ ≤ γ₀ → ∃ C, 0 ≤ C ∧
      ∀ (N k : ℕ) (p : SmoothingParam (Fin n → ℝ)), IsAdm γ N p →
        (∀ x : L2F ℝ (mesh n N).domain (formIdx n k),
          ‖(polyElement n S).smoothedInterp (mesh n N) p
            (isOpen_mesh_domain n N).measurableSet k x‖ ≤ C * ‖x‖) ∧
        (p.IsMaximal (center n) (1 / 4) → ∀ u ∈ (polyElement n S).globalSpace (mesh n N) k,
          ‖(polyElement n S).glue (mesh n N) k u - (polyElement n S).smoothedInterp (mesh n N) p
            (isOpen_mesh_domain n N).measurableSet k ((polyElement n S).glue (mesh n N) k u)‖ ≤
            1 / 2 * ‖(polyElement n S).glue (mesh n N) k u‖) ∧
        (p.IsMinimal (center n) (1 / 4) → ∀ u ∈ (polyElement n S).globalSpace₀ (mesh n N) k,
          ‖(polyElement n S).glue (mesh n N) k u - (polyElement n S).smoothedInterp (mesh n N) p
            (isOpen_mesh_domain n N).measurableSet k ((polyElement n S).glue (mesh n N) k u)‖ ≤
            1 / 2 * ‖(polyElement n S).glue (mesh n N) k u‖) := by
  have hC : (0 : ℝ) ≤ ((max n 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  obtain ⟨γ₁, K₀, hγ₁, hγ₁4, hK₀, hclose⟩ :=
    StarShaped.exists_polyGamma n S (x₀ := center n) hC one_pos one_pos
  refine ⟨2 * γ₁, by positivity, by linarith, fun γ hγ hγγ₀ => ?_⟩
  have hγ4 : 0 < γ / 4 := by positivity
  obtain ⟨C, hC0, hbound⟩ := StarShaped.exists_norm_polySmoothedInterp_le S (x₀ := center n)
    (R := 1 / 4) (σ := 1 / 8) (C := ((max n 2 : ℕ) : ℝ)) one_pos one_pos hγ4 (by linarith)
    (by norm_num) (by norm_num)
  refine ⟨C, hC0, fun N k p hp => ?_⟩
  have hM := meshData (n := n) N
  have hΩ := (isOpen_mesh_domain n N).measurableSet
  have hstar : StarShaped.StarBall (mesh n N).domain (center n) (1 / 4) := starBall_mesh n N
  have hRx : ∀ y ∈ closure (mesh n N).domain, ‖y - center n‖ ≤ 1 / 4 := fun y hy =>
    norm_sub_center_le (by rwa [mesh_domain] at hy)
  have hint := StarShaped.interior_subset_domain hstar (by norm_num)
  have hhR := StarShaped.meshSize_le_two_mul (by norm_num) hRx
  have hpA := hp.starShaped
  have hγh : γ / 4 * (mesh n N).meshSize / (1 / 4) ≤ 1 / 4 := by
    rw [meshSize_mesh]; have := hN_le N; have := hN_pos N; field_simp; nlinarith
  have hθ := mul_lt_mul_of_pos_right hK₀ hγ4
  have hclose' := hclose (γ / 4) hγ4 (by linarith) (mesh n N) hM hΩ hint (by norm_num) hRx hhR
    (by norm_num) p hpA
  refine ⟨hbound (mesh n N) hM hΩ (by norm_num) hRx (by linarith) p hpA k, fun hmax u hu => ?_,
    fun hmin u hu => ?_⟩
  · exact hclose' (StarShaped.polyGeomOK_of_isMaximal hM one_pos hC hstar (by norm_num) hmax hpA
      (by norm_num) hRx (by norm_num) hγ4 hθ) k u hu
      (StarShaped.polySampleOK_of_isMaximal S hstar hmax u)
  · exact hclose' (StarShaped.polyGeomOK_of_isMinimal hM one_pos hC hstar (by norm_num) hint hmin
      hpA (by norm_num) hRx (by norm_num) (by norm_num) hγ4 (by linarith) hθ) k u
      ((polyElement n S).globalSpace₀_le (mesh n N) k hu)
      (StarShaped.polySampleOK_of_isMinimal S hM one_pos hC hstar (by norm_num) hpA (by norm_num)
        hRx (by norm_num) hγ4 hθ hu)

variable (n) in
/-- The finite element complex of `S` on the level-`(N + 1)` Freudenthal mesh, in `HΛ(Q)`. -/
def poly (S : PolySeq) (N : ℕ) : (complex n).Subcomplex :=
  (deRham ℝ n).maximalSubcomplexOfEq (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n) (S.subcomplex (mesh n N) (isOpen_mesh_domain n N))

instance (S : PolySeq) (N : ℕ) (k : ℤ) : FiniteDimensional ℝ ((poly n S N).V k) :=
  (deRham ℝ n).finiteDimensional_maximalSubcomplexOfEq _ _ _ _ k

variable (n) in
/-- The complex of `S` with vanishing boundary DOFs on the Freudenthal mesh, in `H̊Λ(Q)`. -/
def polyMin (S : PolySeq) (N : ℕ) : (complexMin n).Subcomplex :=
  (deRham ℝ n).minimalSubcomplexOfEq (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n)
    (S.subcomplexMin (mesh n N) (isOpen_mesh_domain n N) (center n) (strictStar_mesh n N))

instance (S : PolySeq) (N : ℕ) (k : ℤ) : FiniteDimensional ℝ ((polyMin n S N).V k) :=
  (deRham ℝ n).finiteDimensional_minimalSubcomplexOfEq _ _ _ _ k

variable (n) in
/-- The smoothed canonical interpolant `Q_N = Π_h R` of the complex of `S`, maximal family. -/
def polySmoothed (S : PolySeq) (N : ℕ) (p : SmoothingParam (Fin n → ℝ))
    (hp : p.IsMaximal (center n) (1 / 4)) : (poly n S N).CommutingMap :=
  (deRham ℝ n).commutingMapOfEq (mesh_domain n N) (isOpen_mesh_domain n N) (isOpen_cubeDomain n)
    ((polyElement n S).smoothedCommutingMap (mesh n N) p (isOpen_mesh_domain n N)
      (starBall_mesh n N) hp)

variable (n) in
/-- The smoothed canonical interpolant `Q̊_N` of the complex of `S`, minimal family. -/
def polySmoothedMin (S : PolySeq) (N : ℕ) (p : SmoothingParam (Fin n → ℝ))
    (hp : p.IsMinimal (center n) (1 / 4)) : (polyMin n S N).CommutingMap :=
  (deRham ℝ n).commutingMapOfEqMin (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n)
    ((polyElement n S).smoothedCommutingMapMin (mesh n N) p (isOpen_mesh_domain n N)
      (mesh_domain n N ▸ isBounded_cubeDomain n) (starBall_mesh n N) hp (center n)
      (strictStar_mesh n N))

variable (n) in
/-- The smoothing estimates of the complex of `S` ([AFW2010], §5.5; [ChristiansenWinther2008]). -/
structure PolySmoothingEstimates (S : PolySeq) (p : ℕ → SmoothingParam (Fin n → ℝ)) (C : ℝ) :
    Prop where
  isMaximal : ∀ N, (p N).IsMaximal (center n) (1 / 4)
  half_le : 1 / 2 ≤ C
  bound : ∀ N i x, ‖(polySmoothed n S N (p N) (isMaximal N)).Q i x‖ ≤ C * ‖x‖
  close : ∀ N i, ∀ v ∈ (poly n S N).V i,
    ‖v - (polySmoothed n S N (p N) (isMaximal N)).Q i v‖ ≤ 1 / 2 * ‖v‖

variable (n) in
/-- The smoothing estimates of the complex of `S` with vanishing boundary DOFs. -/
structure PolySmoothingEstimatesMin (S : PolySeq) (p : ℕ → SmoothingParam (Fin n → ℝ)) (C : ℝ) :
    Prop where
  isMinimal : ∀ N, (p N).IsMinimal (center n) (1 / 4)
  half_le : 1 / 2 ≤ C
  bound : ∀ N i x, ‖(polySmoothedMin n S N (p N) (isMinimal N)).Q i x‖ ≤ C * ‖x‖
  close : ∀ N i, ∀ v ∈ (polyMin n S N).V i,
    ‖v - (polySmoothedMin n S N (p N) (isMinimal N)).Q i v‖ ≤ 1 / 2 * ‖v‖

/-- **`pMax γ` satisfies `PolySmoothingEstimates` for every small `γ`** ([AFW2010], §5.5). -/
theorem polySmoothingEstimates_pMax (S : PolySeq) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 / 2 ∧ ∀ (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1), γ ≤ γ₀ →
      ∃ C, PolySmoothingEstimates n S (pMax γ hγ hγ1) C := by
  obtain ⟨γ₀, hγ₀, hγ₀2, h⟩ := Poly.exists_gamma₀ n S
  refine ⟨γ₀, hγ₀, hγ₀2, fun γ hγ hγ1 hγγ₀ => ?_⟩
  obtain ⟨C, -, h⟩ := h γ hγ hγγ₀
  refine ⟨max C (1 / 2), ?_⟩
  have hest : ∀ N, (∀ i x, ‖(polySmoothed n S N (pMax γ hγ hγ1 N) (pMax_isMaximal N)).Q i x‖ ≤
      max C (1 / 2) * ‖x‖) ∧ (∀ i, ∀ v ∈ (poly n S N).V i,
        ‖v - (polySmoothed n S N (pMax γ hγ hγ1 N) (pMax_isMaximal N)).Q i v‖ ≤
          1 / 2 * ‖v‖) := by
    intro N
    refine commutingMapOfEq_estimates (mesh_domain n N) (isOpen_mesh_domain n N)
      (isOpen_cubeDomain n) _ (fun i x => ?_) (fun i v hv => ?_)
    · rw [LocalElement.smoothedCommutingMap_Q]
      rcases i with k | k
      · exact ((h N k _ (pMax_isAdm N)).1 x).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
    · rw [LocalElement.smoothedCommutingMap_Q]
      rcases i with k | k
      · obtain ⟨u, rfl⟩ := hv
        exact (h N k _ (pMax_isAdm N)).2.1 (pMax_isMaximal N) u.1 u.2
      · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
  exact ⟨fun N => pMax_isMaximal N, le_max_right _ _, fun N => (hest N).1,
    fun N => (hest N).2⟩

/-- **`pMin γ` satisfies `PolySmoothingEstimatesMin` for every small `γ`.** -/
theorem polySmoothingEstimatesMin_pMin (S : PolySeq) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 / 2 ∧ ∀ (γ : ℝ) (hγ : 0 < γ), γ ≤ γ₀ →
      ∃ C, PolySmoothingEstimatesMin n S (pMin γ hγ) C := by
  obtain ⟨γ₀, hγ₀, hγ₀2, h⟩ := Poly.exists_gamma₀ n S
  refine ⟨γ₀, hγ₀, hγ₀2, fun γ hγ hγγ₀ => ?_⟩
  obtain ⟨C, -, h⟩ := h γ hγ hγγ₀
  refine ⟨max C (1 / 2), ?_⟩
  have hest : ∀ N, (∀ i x, ‖(polySmoothedMin n S N (pMin γ hγ N) (pMin_isMinimal N)).Q i x‖ ≤
      max C (1 / 2) * ‖x‖) ∧ (∀ i, ∀ v ∈ (polyMin n S N).V i,
        ‖v - (polySmoothedMin n S N (pMin γ hγ N) (pMin_isMinimal N)).Q i v‖ ≤
          1 / 2 * ‖v‖) := by
    intro N
    refine commutingMapOfEqMin_estimates (mesh_domain n N) (isOpen_mesh_domain n N)
      (isOpen_cubeDomain n) _ (fun i x => ?_) (fun i v hv => ?_)
    · rw [LocalElement.smoothedCommutingMapMin_Q]
      rcases i with k | k
      · exact ((h N k _ (pMin_isAdm N)).1 x).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
    · rw [LocalElement.smoothedCommutingMapMin_Q]
      rcases i with k | k
      · obtain ⟨u, rfl⟩ := hv
        exact (h N k _ (pMin_isAdm N)).2.2 (pMin_isMinimal N) u.1 u.2
      · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
  exact ⟨fun N => pMin_isMinimal N, le_max_right _ _, fun N => (hest N).1,
    fun N => (hest N).2⟩

/-- **One smoothing scale serves the Whitney complex and finitely many sequences `S i`.** -/
theorem exists_common_gamma {ι : Type*} [Finite ι] (S : ι → PolySeq) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 / 2 ∧ ∀ (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1), γ ≤ γ₀ →
      (∃ C, SmoothingEstimates n (pMax γ hγ hγ1) C) ∧
      (∃ C, SmoothingEstimatesMin n (pMin γ hγ) C) ∧
      ∀ i, (∃ C, PolySmoothingEstimates n (S i) (pMax γ hγ hγ1) C) ∧
        ∃ C, PolySmoothingEstimatesMin n (S i) (pMin γ hγ) C := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨γw, hγw, hγw2, hw⟩ := smoothingEstimates_pMax_forall (n := n)
  obtain ⟨γw', hγw', hγw'2, hw'⟩ := smoothingEstimatesMin_pMin_forall (n := n)
  choose γp hγp hγp2 hp using fun i => polySmoothingEstimates_pMax (n := n) (S i)
  choose γq hγq hγq2 hq using fun i => polySmoothingEstimatesMin_pMin (n := n) (S i)
  set G : Finset ℝ := insert γw (insert γw' (Finset.univ.image γp ∪ Finset.univ.image γq))
  have hGne : G.Nonempty := Finset.insert_nonempty _ _
  set γ₀ := G.min' hGne
  have hmem : γ₀ ∈ G := Finset.min'_mem G hGne
  have hle : ∀ x ∈ G, γ₀ ≤ x := fun x hx => Finset.min'_le G x hx
  have hpos : ∀ x ∈ G, 0 < x ∧ x ≤ 1 / 2 := by
    intro x hx
    simp only [G, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and] at hx
    rcases hx with rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨hγw, hγw2⟩
    · exact ⟨hγw', hγw'2⟩
    · exact ⟨hγp i, hγp2 i⟩
    · exact ⟨hγq i, hγq2 i⟩
  refine ⟨γ₀, (hpos _ hmem).1, (hpos _ hmem).2, fun γ hγ hγ1 hγγ₀ => ⟨hw γ hγ hγ1
    (hγγ₀.trans (hle _ (by simp [G]))), hw' γ hγ (hγγ₀.trans (hle _ (by simp [G]))),
    fun i => ⟨hp i γ hγ hγ1 (hγγ₀.trans (hle _ (by simp [G]))),
      hq i γ hγ (hγγ₀.trans (hle _ (by simp [G])))⟩⟩⟩

end Feec.Models.Cube.FEM
