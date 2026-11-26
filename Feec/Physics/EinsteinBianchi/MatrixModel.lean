module

public import Feec.Physics.EinsteinBianchi.WaveFEM
public import Feec.Models.Cube.RegularDecomposition
public import Feec.Models.BoundedDomain.BGG
public import Feec.HilbertComplex.Transport

/-!
# The forms model of Ch. 6 on the cube is the matrix model

The forms model and the matrix model `Feec.Models.BoundedDomain.bggComplex` of the
Einstein–Bianchi system with weak symmetries on `Q = (0, ½)³` ([QuennevilleBelair2015], §6.3)
are unitarily equivalent Hilbert complexes (`matrixComplex_eq_map`), so that their Hodge wave
operators, wave groups and strong solutions correspond.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set Filter Topology MeasureTheory

@[expose] public noncomputable section

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W W' : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace 𝕜 (W' i)] [∀ i, CompleteSpace (W' i)]

omit [∀ i, CompleteSpace (W' i)] in
theorem mem_transportD_one_graph_iff {H : HilbertComplex 𝕜 c W} {e : ∀ i, W i ≃L[𝕜] W' i}
    {i j : ι} {p : W' i × W' j} :
    p ∈ (transportD H e (fun _ _ => 1) i j).graph ↔
      ((e i).symm p.1, (e j).symm p.2) ∈ (H.d i j).graph := by
  rw [mem_transportD_graph_iff one_ne_zero, inv_one, one_smul]

theorem map_map_symm (H : HilbertComplex 𝕜 c W) (u : ∀ i, W i ≃ₗᵢ[𝕜] W' i) :
    (H.map u).map (fun i => (u i).symm) = H := by
  refine ext_d (funext fun i => funext fun j => LinearPMap.eq_of_eq_graph
    (Submodule.ext fun p => ?_))
  change p ∈ (transportD (H.map u) (fun i => ((u i).symm).toContinuousLinearEquiv)
    (fun _ _ => 1) i j).graph ↔ _
  rw [mem_transportD_one_graph_iff]
  change ((u i).symm.symm p.1, (u j).symm.symm p.2) ∈ (transportD H
    (fun i => (u i).toContinuousLinearEquiv) (fun _ _ => 1) i j).graph ↔ _
  rw [mem_transportD_one_graph_iff]
  simp

variable [Fintype ι]

/-- The total unitary `∏ W i ≃ ∏ W' i` of a degreewise unitary family. -/
def totalIso (u : ∀ i, W i ≃ₗᵢ[𝕜] W' i) : PiLp 2 W ≃ₗᵢ[𝕜] PiLp 2 W' :=
  LinearIsometryEquiv.piLpCongrRight 2 u

omit [∀ i, CompleteSpace (W i)] [∀ i, CompleteSpace (W' i)] in
theorem totalMap_eq_totalIso (u : ∀ i, W i ≃ₗᵢ[𝕜] W' i) :
    totalMap (fun i => (u i).toContinuousLinearEquiv) =
      ((totalIso u).toContinuousLinearEquiv : PiLp 2 W →L[𝕜] PiLp 2 W') := rfl

theorem wave_map (H : HilbertComplex 𝕜 c W) (u : ∀ i, W i ≃ₗᵢ[𝕜] W' i) :
    LinearPMap.Intertwines ((totalIso u).toContinuousLinearEquiv : PiLp 2 W →L[𝕜] PiLp 2 W')
      H.wave (H.map u).wave := by
  rw [← totalMap_eq_totalIso]
  exact wave_transport (s := 1) one_pos fun i x y => by simp

theorem wave_map_of_eq {H : HilbertComplex 𝕜 c W} {H' : HilbertComplex 𝕜 c W'}
    {u : ∀ i, W i ≃ₗᵢ[𝕜] W' i} (hH : H' = H.map u) :
    LinearPMap.Intertwines ((totalIso u).toContinuousLinearEquiv : PiLp 2 W →L[𝕜] PiLp 2 W')
      H.wave H'.wave := by
  subst hH; exact wave_map H u

theorem wave_map_symm_of_eq {H : HilbertComplex 𝕜 c W} {H' : HilbertComplex 𝕜 c W'}
    {u : ∀ i, W i ≃ₗᵢ[𝕜] W' i} (hH : H' = H.map u) :
    LinearPMap.Intertwines ((totalIso u).symm.toContinuousLinearEquiv : PiLp 2 W' →L[𝕜] PiLp 2 W)
      H'.wave H.wave := by
  subst hH
  have h := wave_map (H.map u) fun i => (u i).symm
  rw [map_map_symm] at h
  exact h

end Feec.HilbertComplex

namespace Feec.HilbertComplex

variable {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W W' : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace ℝ (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace ℝ (W' i)] [∀ i, CompleteSpace (W' i)]

theorem waveGroup_map_of_eq {H : HilbertComplex ℝ c W} {H' : HilbertComplex ℝ c W'}
    {u : ∀ i, W i ≃ₗᵢ[ℝ] W' i} (hH : H' = H.map u) (t : ℝ) (x : PiLp 2 W) :
    totalIso u (H.waveGroup.S t x) = H'.waveGroup.S t (totalIso u x) := by
  have hJ := wave_map_of_eq hH
  rw [← generator_waveGroup, ← generator_waveGroup] at hJ
  exact H'.isIsometric_waveGroup.intertwines_S _ hJ t x

end Feec.HilbertComplex

namespace Feec.Evolution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {A : E →ₗ.[ℝ] E} {B : F →ₗ.[ℝ] F}
  {J : E →L[ℝ] F} {I : Set ℝ} {G U : ℝ → E}

theorem IsStrongSolution.map (hJ : LinearPMap.Intertwines J A B)
    (hU : IsStrongSolution A I G U) : IsStrongSolution B I (fun t => J (G t)) (fun t => J (U t)) :=
  IsStrongSolution.of_deriv fun t ht => by
    obtain ⟨v, hv, hd⟩ := hU.deriv t ht
    obtain ⟨x, hx1, hx2⟩ := (LinearPMap.mem_graph_iff _).1 hv
    refine ⟨J v, (LinearPMap.mem_graph_iff _).2 ⟨⟨J x, hJ.mapsTo x⟩, by simp [hx1], ?_⟩, ?_⟩
    · simp only
      rw [hJ.comm x, hx2]
    · have := J.hasFDerivAt.comp_hasDerivWithinAt t hd
      rw [map_add] at this
      exact this

theorem IsClassicalSolution.map (hJ : LinearPMap.Intertwines J A B)
    (hU : IsClassicalSolution A I G U) :
    IsClassicalSolution B I (fun t => J (G t)) (fun t => J (U t)) := by
  refine ⟨hU.toIsStrongSolution.map hJ, ?_⟩
  obtain ⟨V, hVc, hV⟩ := hU.deriv_cont
  refine ⟨fun t => J (V t), J.continuous.comp_continuousOn hVc, fun t ht => ?_⟩
  obtain ⟨x, hx1, hx2⟩ := (LinearPMap.mem_graph_iff _).1 (hV t ht)
  refine (LinearPMap.mem_graph_iff _).2 ⟨⟨J x, hJ.mapsTo x⟩, by simp [hx1], ?_⟩
  simp only
  rw [hJ.comm x, hx2]

end Feec.Evolution

namespace Feec.EinsteinBianchi.MatrixModel

open Feec.Domain Feec.HilbertComplex Feec.FiniteElement Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry Feec.Models.BoundedDomain Feec.EinsteinBianchi.WaveFEM

/-- `j ↦ {j}`: the coordinate `1`-forms. -/
def idx1 : Fin 3 ≃ formIdx 3 1 :=
  Equiv.ofBijective (fun j => ⟨{j}, by simp⟩) (by decide)

/-- `k ↦ {k}ᶜ`: the coordinate `2`-forms dual to `dx_k`. -/
def idx2 : Fin 3 ≃ formIdx 3 2 :=
  Equiv.ofBijective (fun k => ⟨{k}ᶜ, by rw [Finset.card_compl]; simp⟩) (by decide)

/-- The sign of the Hodge-star proxy `(⋆w)_k = sgn2 k · w_{{k}ᶜ}`: `(w_{12}, −w_{02}, w_{01})`. -/
def sgn2 (k : Fin 3) : ℝ := if k = 1 then -1 else 1

@[simp] theorem sgn2_mul_self (k : Fin 3) : sgn2 k * sgn2 k = 1 := by
  unfold sgn2; split_ifs <;> norm_num

theorem sgn2_smul_sgn2_smul {E : Type*} [AddCommGroup E] [Module ℝ E] (k : Fin 3) (x : E) :
    sgn2 k • sgn2 k • x = x := by
  rw [smul_smul, sgn2_mul_self, one_smul]

/-! ### The isometries -/

/-- `L²Λ¹(Q) ≃ L²(Q; ℝ³)`, `w ↦ (w_{{j}})_j`. -/
def vecEquiv : W1 ≃ₗᵢ[ℝ] L2F ℝ (cubeDomain 3) (Fin 3) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ (L2 ℝ (cubeDomain 3)) idx1.symm

/-- The linear equivalence underlying `rowsEquiv`. -/
def rowsLin : Wv W1 ≃ₗ[ℝ] L2F ℝ (cubeDomain 3) Ix where
  toFun u := WithLp.toLp 2 fun ab => u ab.1 (idx1 ab.2)
  invFun E := WithLp.toLp 2 fun a => WithLp.toLp 2 fun t => E (a, idx1.symm t)
  map_add' u v := rfl
  map_smul' c u := rfl
  left_inv u := by
    refine PiLp.ext fun a => PiLp.ext fun t => ?_
    simp
  right_inv E := by
    refine PiLp.ext fun ab => ?_
    simp

/-- **The rows dictionary** `(L²Λ¹(Q))³ ≃ L²(Q; ℝ³ˣ³)`, `u ↦ E`, `E_{ab} = (uₐ)_{{b}}`. -/
def rowsEquiv : Wv W1 ≃ₗᵢ[ℝ] L2F ℝ (cubeDomain 3) Ix :=
  rowsLin.isometryOfInner fun u v => by
    change ∑ ab : Ix, ⟪u ab.1 (idx1 ab.2), v ab.1 (idx1 ab.2)⟫ = ∑ a, ⟪u a, v a⟫
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [PiLp.inner_apply (u a) (v a)]
    exact Equiv.sum_comp idx1 (fun t => ⟪u a t, v a t⟫)

@[simp] theorem rowsEquiv_apply (u : Wv W1) (ab : Ix) : rowsEquiv u ab = u ab.1 (idx1 ab.2) :=
  rfl

@[simp] theorem rowsEquiv_symm_apply (E : L2F ℝ (cubeDomain 3) Ix) (a : Fin 3) (t : formIdx 3 1) :
    rowsEquiv.symm E a t = E (a, idx1.symm t) := rfl

/-- The linear equivalence underlying `starEquiv`. -/
def starLin : W2 ≃ₗ[ℝ] L2F ℝ (cubeDomain 3) (Fin 3) where
  toFun w := WithLp.toLp 2 fun k => sgn2 k • w (idx2 k)
  invFun m := WithLp.toLp 2 fun t => sgn2 (idx2.symm t) • m (idx2.symm t)
  map_add' u v := by
    refine PiLp.ext fun k => ?_
    simp [smul_add]
  map_smul' c u := by
    refine PiLp.ext fun k => ?_
    simp [smul_comm c]
  left_inv w := by
    refine PiLp.ext fun t => ?_
    simp [sgn2_smul_sgn2_smul]
  right_inv m := by
    refine PiLp.ext fun k => ?_
    simp [sgn2_smul_sgn2_smul]

/-- The Hodge-star proxy `L²Λ²(Q) ≃ L²(Q; ℝ³)`, `w ↦ (w_{12}, −w_{02}, w_{01})`. -/
def starEquiv : W2 ≃ₗᵢ[ℝ] L2F ℝ (cubeDomain 3) (Fin 3) :=
  starLin.isometryOfInner fun u v => by
    change ∑ k : Fin 3, ⟪sgn2 k • u (idx2 k), sgn2 k • v (idx2 k)⟫ = ∑ t, ⟪u t, v t⟫
    simp only [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, sgn2_mul_self, one_mul]
    exact Equiv.sum_comp idx2 (fun t => ⟪u t, v t⟫)

@[simp] theorem starEquiv_apply (w : W2) (k : Fin 3) : starEquiv w k = sgn2 k • w (idx2 k) :=
  rfl

/-- The linear equivalence underlying `rows2Equiv`. -/
def rows2Lin : Wv W2 ≃ₗ[ℝ] L2F ℝ (cubeDomain 3) Ix where
  toFun w := WithLp.toLp 2 fun ak => sgn2 ak.2 • w ak.1 (idx2 ak.2)
  invFun B := WithLp.toLp 2 fun a => WithLp.toLp 2 fun t => sgn2 (idx2.symm t) • B (a, idx2.symm t)
  map_add' u v := by
    refine PiLp.ext fun k => ?_
    simp [smul_add]
  map_smul' c u := by
    refine PiLp.ext fun k => ?_
    simp [smul_comm c]
  left_inv w := by
    refine PiLp.ext fun a => PiLp.ext fun t => ?_
    simp [sgn2_smul_sgn2_smul]
  right_inv B := by
    refine PiLp.ext fun ak => ?_
    simp [sgn2_smul_sgn2_smul]

/-- The rows dictionary `(L²Λ²(Q))³ ≃ L²(Q; ℝ³ˣ³)`: the Hodge star row by row. -/
def rows2Equiv : Wv W2 ≃ₗᵢ[ℝ] L2F ℝ (cubeDomain 3) Ix :=
  rows2Lin.isometryOfInner fun u v => by
    change ∑ ak : Ix, ⟪sgn2 ak.2 • u ak.1 (idx2 ak.2), sgn2 ak.2 • v ak.1 (idx2 ak.2)⟫ =
      ∑ a, ⟪u a, v a⟫
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, sgn2_mul_self, one_mul]
    rw [PiLp.inner_apply (u a) (v a)]
    exact Equiv.sum_comp idx2 (fun t => ⟪u a t, v a t⟫)

@[simp] theorem rows2Equiv_apply (w : Wv W2) (ak : Ix) :
    rows2Equiv w ak = sgn2 ak.2 • w ak.1 (idx2 ak.2) := rfl

@[simp] theorem rows2Equiv_symm_apply (B : L2F ℝ (cubeDomain 3) Ix) (a : Fin 3)
    (t : formIdx 3 2) : rows2Equiv.symm B a t = sgn2 (idx2.symm t) • B (a, idx2.symm t) := rfl

theorem rows2Equiv_symm_apply_idx2 (B : L2F ℝ (cubeDomain 3) Ix) (a k : Fin 3) :
    rows2Equiv.symm B a (idx2 k) = sgn2 k • B (a, k) := by
  simp

/-- The linear equivalence underlying `topEquiv`. -/
def topLin : WithLp 2 (W2 × Wv W2) ≃ₗ[ℝ] W2B ℝ (cubeDomain 3) where
  toFun p := WithLp.toLp 2 (starEquiv (WithLp.ofLp p).1, rows2Equiv (WithLp.ofLp p).2)
  invFun q := WithLp.toLp 2 (starEquiv.symm (WithLp.ofLp q).1, rows2Equiv.symm (WithLp.ofLp q).2)
  map_add' p q := by
    refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_) <;> simp
  map_smul' c p := by
    refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_) <;> simp
  left_inv p := by
    refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_) <;> simp
  right_inv q := by
    refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_) <;> simp

/-- **The top dictionary** `L²Λ² × (L²Λ²)³ ≃ L²(Q; ℝ³) × L²(Q; ℝ³ˣ³)`, `(M, ρ) ↦ (⋆M, ⋆ρ)`. -/
def topEquiv : WithLp 2 (W2 × Wv W2) ≃ₗᵢ[ℝ] W2B ℝ (cubeDomain 3) :=
  topLin.isometryOfInner fun p q => by
    change ⟪(WithLp.toLp 2 (starEquiv (WithLp.ofLp p).1, rows2Equiv (WithLp.ofLp p).2) :
        W2B ℝ (cubeDomain 3)), WithLp.toLp 2 (starEquiv (WithLp.ofLp q).1,
          rows2Equiv (WithLp.ofLp q).2)⟫ = ⟪p, q⟫
    rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
    simp

@[simp] theorem topEquiv_apply_fst (p : WithLp 2 (W2 × Wv W2)) :
    (WithLp.ofLp (topEquiv p)).1 = starEquiv (WithLp.ofLp p).1 := rfl

@[simp] theorem topEquiv_apply_snd (p : WithLp 2 (W2 × Wv W2)) :
    (WithLp.ofLp (topEquiv p)).2 = rows2Equiv (WithLp.ofLp p).2 := rfl

/-! ### `⋆ d = curl` on smooth `1`-forms -/

theorem extDerivOp_one_apply_idx2_zero (φ : formIdx 3 1 → R3 → ℝ) (x : R3) :
    sgn2 0 * (extDerivOp ℝ 3 1).apply φ (idx2 0) x =
      fderiv ℝ (φ (idx1 2)) x (coordDir 1) - fderiv ℝ (φ (idx1 1)) x (coordDir 2) := by
  have e : idx2 0 = ⟨{1, 2}, by decide⟩ := Subtype.ext (by decide)
  rw [e, extDerivOp_one_apply_pair φ (by decide : (1 : Fin 3) < 2) x,
    show idx1 1 = ⟨{1}, by simp⟩ from rfl, show idx1 2 = ⟨{2}, by simp⟩ from rfl]
  simp only [sgn2]
  norm_num

theorem extDerivOp_one_apply_idx2_one (φ : formIdx 3 1 → R3 → ℝ) (x : R3) :
    sgn2 1 * (extDerivOp ℝ 3 1).apply φ (idx2 1) x =
      fderiv ℝ (φ (idx1 0)) x (coordDir 2) - fderiv ℝ (φ (idx1 2)) x (coordDir 0) := by
  have e : idx2 1 = ⟨{0, 2}, by decide⟩ := Subtype.ext (by decide)
  rw [e, extDerivOp_one_apply_pair φ (by decide : (0 : Fin 3) < 2) x,
    show idx1 0 = ⟨{0}, by simp⟩ from rfl, show idx1 2 = ⟨{2}, by simp⟩ from rfl]
  simp only [sgn2, ite_true]
  ring

theorem extDerivOp_one_apply_idx2_two (φ : formIdx 3 1 → R3 → ℝ) (x : R3) :
    sgn2 2 * (extDerivOp ℝ 3 1).apply φ (idx2 2) x =
      fderiv ℝ (φ (idx1 1)) x (coordDir 0) - fderiv ℝ (φ (idx1 0)) x (coordDir 1) := by
  have e : idx2 2 = ⟨{0, 1}, by decide⟩ := Subtype.ext (by decide)
  rw [e, extDerivOp_one_apply_pair φ (by decide : (0 : Fin 3) < 1) x,
    show idx1 0 = ⟨{0}, by simp⟩ from rfl, show idx1 1 = ⟨{1}, by simp⟩ from rfl]
  simp only [sgn2]
  norm_num

theorem extDerivOp_one_apply_idx2 (φ : formIdx 3 1 → R3 → ℝ) (k : Fin 3) (x : R3) :
    sgn2 k * (extDerivOp ℝ 3 1).apply φ (idx2 k) x =
      fderiv ℝ (φ (idx1 (k + 2))) x (coordDir (k + 1)) -
        fderiv ℝ (φ (idx1 (k + 1))) x (coordDir (k + 2)) := by
  fin_cases k
  · exact extDerivOp_one_apply_idx2_zero φ x
  · exact extDerivOp_one_apply_idx2_one φ x
  · exact extDerivOp_one_apply_idx2_two φ x

/-- The row `a` of a matrix field, as a `1`-form: `(Φₐ)_{{b}} = Φ_{ab}`. -/
def rowForm (Φ : Ix → R3 → ℝ) (a : Fin 3) : formIdx 3 1 → R3 → ℝ :=
  fun t => Φ (a, idx1.symm t)

/-- The matrix field with rows the `1`-forms `ψₐ`: `Φ_{ab} = (ψₐ)_{{b}}`. -/
def matField (ψ : Fin 3 → formIdx 3 1 → R3 → ℝ) : Ix → R3 → ℝ :=
  fun ab => ψ ab.1 (idx1 ab.2)

theorem rowForm_matField (ψ : Fin 3 → formIdx 3 1 → R3 → ℝ) (a : Fin 3) :
    rowForm (matField ψ) a = ψ a := funext fun t => by simp [rowForm, matField]

theorem curlOp_apply_eq (Φ : Ix → R3 → ℝ) (a k : Fin 3) (x : R3) :
    (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).apply Φ (a, k) x =
      sgn2 k * (extDerivOp ℝ 3 1).apply (rowForm Φ a) (idx2 k) x := by
  rw [extDerivOp_one_apply_idx2, curlOp_apply]
  simp [rowForm]

theorem isTestField_rowForm {Φ : Ix → R3 → ℝ} (hΦ : IsTestField (cubeDomain 3) Φ) (a : Fin 3) :
    IsTestField (cubeDomain 3) (rowForm Φ a) := fun t => hΦ (a, idx1.symm t)

theorem isTestField_matField {ψ : Fin 3 → formIdx 3 1 → R3 → ℝ}
    (hψ : ∀ a, IsTestField (cubeDomain 3) (ψ a)) : IsTestField (cubeDomain 3) (matField ψ) :=
  fun ab => hψ ab.1 (idx1 ab.2)

theorem rowsEquiv_symm_testField {Φ : Ix → R3 → ℝ} (hΦ : IsTestField (cubeDomain 3) Φ)
    (a : Fin 3) : rowsEquiv.symm (testField hΦ) a = testField (isTestField_rowForm hΦ a) :=
  PiLp.ext fun t => by simp [rowForm]

theorem rows2Equiv_symm_testField_curl {Φ : Ix → R3 → ℝ} (hΦ : IsTestField (cubeDomain 3) Φ)
    (a : Fin 3) :
    rows2Equiv.symm (testField ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).isTestField_apply hΦ)) a =
      testField ((extDerivOp ℝ 3 1).isTestField_apply (isTestField_rowForm hΦ a)) := by
  refine PiLp.ext fun t => ?_
  obtain ⟨k, rfl⟩ := idx2.surjective t
  rw [rows2Equiv_symm_apply_idx2, testField_apply, testField_apply, ← toL2_smul]
  refine toL2_congr _ _ (funext fun x => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [curlOp_apply_eq, ← mul_assoc, sgn2_mul_self, one_mul]

theorem rowsEquiv_testField {ψ : Fin 3 → formIdx 3 1 → R3 → ℝ}
    (hψ : ∀ a, IsTestField (cubeDomain 3) (ψ a)) :
    rowsEquiv (WithLp.toLp 2 fun a => testField (hψ a)) = testField (isTestField_matField hψ) :=
  PiLp.ext fun ab => by simp [matField]

theorem rows2Equiv_testField {ψ : Fin 3 → formIdx 3 1 → R3 → ℝ}
    (hψ : ∀ a, IsTestField (cubeDomain 3) (ψ a)) :
    rows2Equiv (WithLp.toLp 2 fun a => testField ((extDerivOp ℝ 3 1).isTestField_apply (hψ a))) =
      testField ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).isTestField_apply
        (isTestField_matField hψ)) := by
  refine PiLp.ext fun ak => ?_
  obtain ⟨a, k⟩ := ak
  rw [rows2Equiv_apply, testField_apply, testField_apply, ← toL2_smul]
  refine toL2_congr _ _ (funext fun x => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [curlOp_apply_eq, rowForm_matField]

/-! ### The minimal row-wise curl is `d_min` row by row -/

/-- The minimal row-wise curl `curl : H̊(curl, Q; ℝ³ˣ³) → L²(Q; ℝ³ˣ³)`. -/
abbrev curlMin : L2F ℝ (cubeDomain 3) Ix →ₗ.[ℝ] L2F ℝ (cubeDomain 3) Ix :=
  (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal (cubeDomain 3)

/-- The test graph `{(φ, dφ) : φ ∈ C_c^∞(Q; Λ¹)}`. -/
def testGraph1 : Submodule ℝ (W1 × W2) := (extDerivOp ℝ 3 1).testGraph (cubeDomain 3)

theorem graph_D1 : (D1.graph : Set (W1 × W2)) =
    closure (testGraph1 : Set (W1 × W2)) := by
  rw [(extDerivOp ℝ 3 1).minimal_graph (isOpen_cubeDomain 3), Submodule.topologicalClosure_coe]
  rfl

theorem graph_curlMin : (curlMin.graph : Set (L2F ℝ (cubeDomain 3) Ix × L2F ℝ (cubeDomain 3) Ix)) =
    closure ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).testGraph (cubeDomain 3) :
      Set (L2F ℝ (cubeDomain 3) Ix × L2F ℝ (cubeDomain 3) Ix)) := by
  rw [(curlOp 3).minimal_graph (isOpen_cubeDomain 3), Submodule.topologicalClosure_coe]

theorem mem_curlMin_graph_iff {u : Wv W1} {w : Wv W2} :
    (rowsEquiv u, rows2Equiv w) ∈ curlMin.graph ↔ ∀ a, (u a, w a) ∈ D1.graph := by
  constructor
  · intro h a
    have h' : (rowsEquiv u, rows2Equiv w) ∈ closure
        ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).testGraph (cubeDomain 3) :
          Set (L2F ℝ (cubeDomain 3) Ix × L2F ℝ (cubeDomain 3) Ix)) := by
      rw [← graph_curlMin]; exact h
    have hc : Continuous fun p : L2F ℝ (cubeDomain 3) Ix × L2F ℝ (cubeDomain 3) Ix =>
        (rowsEquiv.symm p.1 a, rows2Equiv.symm p.2 a) :=
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => W1) a).continuous.comp
        (rowsEquiv.symm.continuous.comp continuous_fst)).prodMk
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => W2) a).continuous.comp
        (rows2Equiv.symm.continuous.comp continuous_snd))
    have hm := map_mem_closure hc h' (t := (testGraph1 : Set (W1 × W2))) (by
        rintro _ ⟨φ, hφ, rfl⟩
        refine ⟨rowForm φ a, isTestField_rowForm hφ a, ?_⟩
        simp only
        rw [rowsEquiv_symm_testField hφ, rows2Equiv_symm_testField_curl hφ])
    rw [← SetLike.mem_coe, graph_D1]
    simpa using hm
  · intro h
    have hpi : (fun a => (u a, w a)) ∈ closure (Set.pi univ fun _ : Fin 3 =>
        (testGraph1 : Set (W1 × W2))) := by
      rw [closure_pi_set]
      intro a _
      rw [← graph_D1]
      exact h a
    have hc : Continuous fun p : Fin 3 → W1 × W2 =>
        (rowsEquiv (WithLp.toLp 2 fun a => (p a).1), rows2Equiv (WithLp.toLp 2 fun a => (p a).2)) :=
      (rowsEquiv.continuous.comp ((PiLp.continuous_toLp 2 _).comp
        (continuous_pi fun a => (continuous_apply a).fst))).prodMk
      (rows2Equiv.continuous.comp ((PiLp.continuous_toLp 2 _).comp
        (continuous_pi fun a => (continuous_apply a).snd)))
    have hm := map_mem_closure hc hpi (t := ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).testGraph
      (cubeDomain 3) : Set (L2F ℝ (cubeDomain 3) Ix × L2F ℝ (cubeDomain 3) Ix))) (by
        intro p hp
        have hp' : ∀ a, ∃ ψ : formIdx 3 1 → R3 → ℝ, ∃ hψ : IsTestField (cubeDomain 3) ψ,
            p a = (testField hψ, testField ((extDerivOp ℝ 3 1).isTestField_apply hψ)) :=
          fun a => hp a (mem_univ a)
        choose ψ hψ hpψ using hp'
        refine ⟨matField ψ, isTestField_matField hψ, ?_⟩
        have e1 : (WithLp.toLp 2 fun a => (p a).1 : Wv W1) =
            WithLp.toLp 2 fun a => testField (hψ a) := by
          congr 1; funext a; rw [hpψ a]
        have e2 : (WithLp.toLp 2 fun a => (p a).2 : Wv W2) =
            WithLp.toLp 2 fun a => testField ((extDerivOp ℝ 3 1).isTestField_apply (hψ a)) := by
          congr 1; funext a; rw [hpψ a]
        simp only
        rw [e1, e2, rowsEquiv_testField hψ, rows2Equiv_testField hψ])
    rw [← SetLike.mem_coe, graph_curlMin]
    have e1 : (WithLp.toLp 2 fun a => u a : Wv W1) = u := rfl
    have e2 : (WithLp.toLp 2 fun a => w a : Wv W2) = w := rfl
    simpa only [e1, e2] using hm

theorem mem_curlMin_domain_iff {u : Wv W1} :
    rowsEquiv u ∈ curlMin.domain ↔ ∀ a, u a ∈ D1.domain := by
  constructor
  · intro h a
    have hg := curlMin.mem_graph ⟨_, h⟩
    rw [show curlMin ⟨_, h⟩ = rows2Equiv (rows2Equiv.symm (curlMin ⟨_, h⟩)) by simp] at hg
    exact LinearPMap.mem_domain_of_mem_graph (mem_curlMin_graph_iff.1 hg a)
  · intro h
    refine LinearPMap.mem_domain_of_mem_graph (y := rows2Equiv (WithLp.toLp 2 fun a => D1 ⟨_, h a⟩))
      (mem_curlMin_graph_iff.2 fun a => ?_)
    exact D1.mem_graph ⟨_, h a⟩

/-! ### `S¹ = 2 vskw` -/

theorem wsCoeff_one_idx2 (k i j : Fin 3) :
    wsCoeff (n := 3) 1 (idx2 k) (i, idx1 j) =
      if i = k + 1 ∧ j = k + 2 then sgn2 k else if i = k + 2 ∧ j = k + 1 then -sgn2 k else 0 := by
  rw [wsCoeff_eq]
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true }) [ExteriorFibre.sgn, sgn2]

theorem wsL2_one_apply_idx2 (u : Wv W1) (k : Fin 3) :
    wsL2 (Ω := cubeDomain 3) 1 u (idx2 k) =
      sgn2 k • (u (k + 1) (idx1 (k + 2)) - u (k + 2) (idx1 (k + 1))) := by
  rw [wsL2_apply, Fintype.sum_prod_type]
  simp_rw [← Equiv.sum_comp idx1 (fun t => wsCoeff (n := 3) 1 (idx2 k) (_, t) • u _ t)]
  simp only [wsCoeff_one_idx2]
  fin_cases k <;> simp [Fin.sum_univ_three, sgn2] <;> abel

theorem skwL_rowsEquiv (u : Wv W1) :
    skwL ℝ (cubeDomain 3) (rowsEquiv u) = starEquiv (wsL2 (Ω := cubeDomain 3) 1 u) := by
  refine PiLp.ext fun k => ?_
  rw [skwL_apply, starEquiv_apply, wsL2_one_apply_idx2, sgn2_smul_sgn2_smul, rowsEquiv_apply,
    rowsEquiv_apply]

/-! ### `Γ̄ = L²Λ⁰(Q)` -/

theorem formIdx_zero_eq (t : formIdx 3 0) : t = idx0 :=
  Subtype.ext (Finset.card_eq_zero.1 (by have := t.2; omega))

/-- The linear equivalence underlying `scalarEquiv`. -/
def scalarLin : W0 ≃ₗ[ℝ] L2 ℝ (cubeDomain 3) where
  toFun σ := σ idx0
  invFun v := WithLp.toLp 2 fun _ => v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv σ := PiLp.ext fun t => by rw [formIdx_zero_eq t]
  right_inv _ := rfl

/-- `L²Λ⁰(Q) ≃ L²(Q)`: `0`-forms are scalars. -/
def scalarEquiv : W0 ≃ₗᵢ[ℝ] L2 ℝ (cubeDomain 3) :=
  scalarLin.isometryOfInner fun σ τ => by
    change ⟪σ idx0, τ idx0⟫ = ∑ t, ⟪σ t, τ t⟫
    rw [Finset.sum_eq_single idx0 (fun t _ ht => absurd (formIdx_zero_eq t) ht) (by simp)]

theorem mem_hilbΓ_of_mem_segΓ {x : U0 × Wv U0} (hx : x ∈ bggSegment.Γ) :
    (D0.toGraphSpace x.1, toGraphVec0 x.2) ∈ bggHilb.Γ := by
  rw [Feec.BGG.Hilb.mem_Γ]
  have h : bggSegment.d0 x.1 = bggSegment.S0 x.2 := bggSegment.mem_Γ.1 hx
  refine LinearPMap.graphFst_injective D1 ?_
  change D1.graphFst (bggD0 (D0.toGraphSpace x.1)) = D1.graphFst (bggS0 (toGraphVec0 x.2))
  rw [graphFst_bggD0, graphFst_bggS0, ιt0_toGraphVec0, LinearPMap.graphSnd_toGraphSpace]
  exact congrArg Subtype.val h

theorem mem_segΓ_of_mem_hilbΓ {y : V0 × Vt0} (hy : y ∈ bggHilb.Γ) :
    (D0.graphDom y.1, rp y.2) ∈ bggSegment.Γ := by
  rw [bggSegment.mem_Γ]
  have h : bggD0 y.1 = bggS0 y.2 := (Feec.BGG.Hilb.mem_Γ bggHilb).1 hy
  refine Subtype.ext ?_
  change D0 (D0.graphDom y.1) = wsL2 (Ω := cubeDomain 3) 0 (incl0 (rp y.2))
  rw [LinearPMap.apply_graphDom, ← graphFst_bggD0, h, graphFst_bggS0, incl0_rp]

theorem Γbar_eq_top : bggHilb.Γbar = ⊤ := by
  have hsub : (scalarEquiv.symm '' ((hessMin ℝ (isOpen_cubeDomain 3)).domain :
      Set (L2 ℝ (cubeDomain 3)))) ⊆
      (bggHilb.Γ.map ((bggHilb.ι0 : V0 →ₗ[ℝ] W0) ∘ₗ LinearMap.fst ℝ V0 Vt0) : Set W0) := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨x, hx, hxv⟩ := (gamma_equiv_hessMin.2.1 v).1 hv
    refine ⟨_, mem_hilbΓ_of_mem_segΓ hx, ?_⟩
    change D0.graphFst (D0.toGraphSpace x.1) = scalarEquiv.symm v
    rw [LinearPMap.graphFst_toGraphSpace, ← hxv]
    exact (scalarEquiv.symm_apply_apply _).symm
  have hd : Dense (scalarEquiv.symm '' ((hessMin ℝ (isOpen_cubeDomain 3)).domain :
      Set (L2 ℝ (cubeDomain 3)))) :=
    scalarEquiv.symm.surjective.denseRange.dense_image scalarEquiv.symm.continuous
      (dense_hessMin_domain (isOpen_cubeDomain 3))
  rw [Feec.BGG.Hilb.Γbar, ← Submodule.dense_iff_topologicalClosure_eq_top]
  exact hd.mono hsub

/-- The first dictionary `Γ̄ ≃ L²(Q)`: `Γ̄ = L²Λ⁰(Q)`, read as scalars. -/
def zeroEquiv : bggHilb.Γbar ≃ₗᵢ[ℝ] L2 ℝ (cubeDomain 3) :=
  (LinearIsometryEquiv.ofTop (E := W0) bggHilb.Γbar Γbar_eq_top).trans scalarEquiv

/-! ### The differentials correspond -/

/-- The forms-model short complex `Γ̄ → (L²Λ¹)³ → L²Λ² × (L²Λ²)³` of (5.1) on the cube. -/
abbrev formsShort := bggHilb.toShort bggHilb_hyps bggS0_injective

theorem rowsEquiv_incl1_dt0 (φ : Wv U0) : rowsEquiv (incl1 (bggSegment.dt0 φ)) = hessOf φ := by
  refine PiLp.ext fun ij => ?_
  rfl

theorem rowsEquiv_ιt1_bggDt0 (φ : Vt0) : rowsEquiv (ιt1 (bggDt0 φ)) = hessOf (rp φ) := by
  refine PiLp.ext fun ij => ?_
  change D1.graphFst (bggD0 (φ ij.1)) (idx1 ij.2) = (D0 (D0.graphDom (φ ij.1))) (idxSingle ij.2)
  rw [graphFst_bggD0, LinearPMap.apply_graphDom]
  rfl

set_option maxHeartbeats 2000000 in
theorem mem_hessMin_graph_iff {v : L2 ℝ (cubeDomain 3)} {H : L2F ℝ (cubeDomain 3) Ix} :
    (v, H) ∈ (hessMin ℝ (isOpen_cubeDomain 3)).graph ↔
      (zeroEquiv.symm v, rowsEquiv.symm H) ∈ bggHilb.D0Γ.graph := by
  rw [bggHilb.D0Γ_graph bggS0_injective]
  constructor
  · intro h
    have h' := (LinearPMap.mem_graph_iff (hessMin ℝ (isOpen_cubeDomain 3))).1 h
    obtain ⟨y, hy⟩ := h'
    have hyv : (y : L2 ℝ (cubeDomain 3)) = v := hy.1
    have hyH : hessMin ℝ (isOpen_cubeDomain 3) y = H := hy.2
    have hw : v ∈ (hessMin ℝ (isOpen_cubeDomain 3)).domain := by rw [← hyv]; exact y.2
    have hex := ((gamma_equiv_hessMin.2.1 v).1 hw)
    obtain ⟨x, hxx⟩ := hex
    have hx : x ∈ bggSegment.Γ := hxx.1
    have hxv : toScalar ((x.1 : U0) : W0) = v := hxx.2
    have hdd := gamma_equiv_hessMin.2.2 x hx
    obtain ⟨hd, hhess⟩ := hdd
    have e : y = ⟨_, hd⟩ := Subtype.ext (hyv.trans hxv.symm)
    rw [e, hhess] at hyH
    refine ⟨⟨_, mem_hilbΓ_of_mem_segΓ hx⟩, Prod.ext (Subtype.ext ?_) ?_⟩
    · change D0.graphFst (D0.toGraphSpace x.1) = scalarEquiv.symm v
      rw [LinearPMap.graphFst_toGraphSpace, ← hxv]
      exact (scalarEquiv.symm_apply_apply _).symm
    · change ιt1 (bggDt0 (toGraphVec0 x.2)) = rowsEquiv.symm H
      rw [ιt1_bggDt0_toGraphVec0, ← hyH, ← rowsEquiv_incl1_dt0]
      exact (rowsEquiv.symm_apply_apply _).symm
  · intro h
    obtain ⟨y, hy⟩ := h
    have h1 : D0.graphFst (y : V0 × Vt0).1 = scalarEquiv.symm v :=
      congrArg Subtype.val (congrArg Prod.fst hy)
    have h2 : ιt1 (bggDt0 (y : V0 × Vt0).2) = rowsEquiv.symm H := congrArg Prod.snd hy
    have hx := mem_segΓ_of_mem_hilbΓ y.2
    have hg : (toScalar ((D0.graphDom (y : V0 × Vt0).1 : U0) : W0),
        hessOf (rp (y : V0 × Vt0).2)) ∈ (hessMin ℝ (isOpen_cubeDomain 3)).graph := by
      have hdd := hessMin_of_mem_Γ (bggSegment.mem_Γ.1 hx)
      exact (LinearPMap.mem_graph_iff _).2 ⟨⟨_, hdd.1⟩, rfl, hdd.2⟩
    have hv : toScalar ((D0.graphDom (y : V0 × Vt0).1 : U0) : W0) = v := by
      change toScalar (D0.graphFst (y : V0 × Vt0).1) = v
      rw [h1]
      exact scalarEquiv.apply_symm_apply v
    have hH : hessOf (rp (y : V0 × Vt0).2) = H :=
      (rowsEquiv_ιt1_bggDt0 (y : V0 × Vt0).2).symm.trans
        ((congrArg rowsEquiv h2).trans (rowsEquiv.apply_symm_apply H))
    rw [hv, hH] at hg
    exact hg

theorem ofLp_TL (u : Vt1) : WithLp.ofLp (bggHilb.TL u) = (bggS1 u, bggDt1 u) := rfl

/-- The graph-space point of `H̊Λ¹(Q)³` with given rows. -/
def ofRows (U : Wv W1) (h : ∀ a, U a ∈ D1.domain) : Vt1 :=
  WithLp.toLp 2 fun a => D1.toGraphSpace ⟨U a, h a⟩

theorem ιt1_ofRows (U : Wv W1) (h : ∀ a, U a ∈ D1.domain) : ιt1 (ofRows U h) = U :=
  PiLp.ext fun _ => rfl

set_option maxHeartbeats 2000000 in
theorem mem_bggComplex_d₁_graph_iff' {E : L2F ℝ (cubeDomain 3) Ix} {w : W2B ℝ (cubeDomain 3)} :
    (E, w) ∈ (bggComplex ℝ (isOpen_cubeDomain 3)).d₁.graph ↔
      (rowsEquiv.symm E, topEquiv.symm w) ∈ bggHilb.D1L.graph := by
  rw [mem_bggComplex_d₁_graph_iff, bggHilb.D1L_graph]
  constructor
  · rintro ⟨hc, hs⟩
    have hc' : (rowsEquiv (rowsEquiv.symm E), rows2Equiv (rows2Equiv.symm (WithLp.ofLp w).2)) ∈
        curlMin.graph := by
      rw [rowsEquiv.apply_symm_apply, rows2Equiv.apply_symm_apply]; exact hc
    have hrows := mem_curlMin_graph_iff.1 hc'
    have hdom : ∀ a, rowsEquiv.symm E a ∈ D1.domain := fun a =>
      LinearPMap.mem_domain_of_mem_graph (hrows a)
    refine ⟨ofRows _ hdom, Prod.ext (ιt1_ofRows _ hdom) ?_⟩
    refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_)
    · change bggS1 (ofRows _ hdom) = starEquiv.symm (WithLp.ofLp w).1
      have e1 : bggS1 (ofRows _ hdom) = wsL2 (Ω := cubeDomain 3) 1 (rowsEquiv.symm E) := by
        change wsL2 (Ω := cubeDomain 3) 1 (ιt1 (ofRows _ hdom)) = _
        rw [ιt1_ofRows]
      have e2 : (WithLp.ofLp w).1 = starEquiv (wsL2 (Ω := cubeDomain 3) 1 (rowsEquiv.symm E)) := by
        rw [hs, ← skwL_rowsEquiv, rowsEquiv.apply_symm_apply]
      rw [e1, e2]
      exact (starEquiv.symm_apply_apply _).symm
    · change bggDt1 (ofRows _ hdom) = rows2Equiv.symm (WithLp.ofLp w).2
      refine PiLp.ext fun a => ?_
      change D1 ⟨rowsEquiv.symm E a, hdom a⟩ = rows2Equiv.symm (WithLp.ofLp w).2 a
      obtain ⟨z, hz1, hz2⟩ := (LinearPMap.mem_graph_iff _).1 (hrows a)
      exact (congrArg D1 (Subtype.ext hz1.symm)).trans hz2
  · rintro ⟨u, hu⟩
    have h1 : ιt1 u = rowsEquiv.symm E := congrArg Prod.fst hu
    have h2 : bggHilb.TL u = topEquiv.symm w := congrArg Prod.snd hu
    have hE : E = rowsEquiv (ιt1 u) := by rw [h1, rowsEquiv.apply_symm_apply]
    have hw : w = topEquiv (bggHilb.TL u) := by rw [h2, topEquiv.apply_symm_apply]
    have hw2 : (WithLp.ofLp w).2 = rows2Equiv (bggDt1 u) := by
      rw [hw, topEquiv_apply_snd, ofLp_TL]
    have hw1 : (WithLp.ofLp w).1 = starEquiv (bggS1 u) := by
      rw [hw, topEquiv_apply_fst, ofLp_TL]
    refine ⟨?_, ?_⟩
    · rw [hE, hw2]
      exact mem_curlMin_graph_iff.2 fun a => LinearPMap.mem_graphL2.1 (u a).2
    · rw [hw1, hE, skwL_rowsEquiv]
      rfl

/-! ### The two Hilbert complexes are unitarily equivalent -/

section Transport

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-- The forms-model Hilbert complex `Γ̄ → (L²Λ¹)³ → L²Λ² × (L²Λ²)³` of (5.1) on the cube. -/
abbrev formsComplex := bggHilb.toHilbertComplex bggHilb_hyps bggS0_injective

/-- The matrix-model Hilbert complex of `Feec.Models.BoundedDomain.bggComplex` on `Q`. -/
abbrev matrixComplex := (bggComplex ℝ (isOpen_cubeDomain 3)).toHilbertComplex

/-- **The total dictionary**: `(zeroEquiv, rowsEquiv, topEquiv)`, degreewise. -/
def totalEquiv : ∀ i : Fin 3,
    ShortHilbertComplex.W3 bggHilb.Γbar (Wv W1) (WithLp 2 (W2 × Wv W2)) i ≃ₗᵢ[ℝ]
      ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix)
        (W2B ℝ (cubeDomain 3)) i
  | 0 => zeroEquiv
  | 1 => rowsEquiv
  | 2 => topEquiv

/-- The degreewise dictionary as continuous linear equivalences. -/
abbrev totalCLE (i : Fin 3) := (totalEquiv i).toContinuousLinearEquiv

theorem matrixComplex_d01 : matrixComplex.d 0 1 =
    HilbertComplex.transportD formsComplex totalCLE (fun _ _ => 1) 0 1 := by
  refine LinearPMap.eq_of_eq_graph (Submodule.ext fun p => ?_)
  rw [HilbertComplex.mem_transportD_one_graph_iff]
  exact mem_hessMin_graph_iff

theorem matrixComplex_d12 : matrixComplex.d 1 2 =
    HilbertComplex.transportD formsComplex totalCLE (fun _ _ => 1) 1 2 := by
  refine LinearPMap.eq_of_eq_graph (Submodule.ext fun p => ?_)
  rw [HilbertComplex.mem_transportD_one_graph_iff]
  exact mem_bggComplex_d₁_graph_iff'

/-- The matrix model is the transport of the forms model: the Hilbert complex of `bggComplex` on
`Q` equals the transport of `bggHilb.toHilbertComplex` along `totalEquiv`. -/
theorem matrixComplex_eq_map : matrixComplex = formsComplex.map totalEquiv := by
  refine HilbertComplex.ext_d (funext fun i => funext fun j => ?_)
  change matrixComplex.d i j = HilbertComplex.transportD formsComplex totalCLE (fun _ _ => 1) i j
  fin_cases i <;> fin_cases j
  · exact (HilbertComplex.transportD_eq_zero rfl).symm
  · exact matrixComplex_d01
  · exact (HilbertComplex.transportD_eq_zero rfl).symm
  · exact (HilbertComplex.transportD_eq_zero rfl).symm
  · exact (HilbertComplex.transportD_eq_zero rfl).symm
  · exact matrixComplex_d12
  · exact (HilbertComplex.transportD_eq_zero rfl).symm
  · exact (HilbertComplex.transportD_eq_zero rfl).symm
  · exact (HilbertComplex.transportD_eq_zero rfl).symm

/-- The total unitary `(zeroEquiv, rowsEquiv, topEquiv)` from the forms to the matrix model. -/
abbrev totalE := HilbertComplex.totalIso totalEquiv

theorem wave_intertwines :
    LinearPMap.Intertwines (totalE.toContinuousLinearEquiv : _ →L[ℝ] _) formsComplex.wave
      matrixComplex.wave :=
  HilbertComplex.wave_map_of_eq matrixComplex_eq_map

theorem wave_intertwines_symm :
    LinearPMap.Intertwines (totalE.symm.toContinuousLinearEquiv : _ →L[ℝ] _) matrixComplex.wave
      formsComplex.wave :=
  HilbertComplex.wave_map_symm_of_eq matrixComplex_eq_map

/-- **The wave groups are conjugate**: `e (e^{tL} x) = e^{tL'} (e x)`. -/
theorem waveGroup_conj (t : ℝ) (x) :
    totalE (formsComplex.waveGroup.S t x) = matrixComplex.waveGroup.S t (totalE x) :=
  HilbertComplex.waveGroup_map_of_eq matrixComplex_eq_map t x

/-- **Strong solutions correspond**: `U` is a strong solution of the forms-model Hodge wave
equation `U' = L U + F` iff `e ∘ U` is one of the matrix model with forcing `e ∘ F`. -/
theorem isStrongSolution_iff {I : Set ℝ} {F U : ℝ → PiLp 2
      (ShortHilbertComplex.W3 bggHilb.Γbar (Wv W1) (WithLp 2 (W2 × Wv W2)))} :
    Evolution.IsStrongSolution formsComplex.wave I F U ↔
      Evolution.IsStrongSolution matrixComplex.wave I (fun t => totalE (F t))
        (fun t => totalE (U t)) := by
  constructor
  · exact fun h => h.map wave_intertwines
  · intro h
    have := h.map wave_intertwines_symm
    simpa using this

end Transport

end Feec.EinsteinBianchi.MatrixModel
