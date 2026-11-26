module

public import Feec.HilbertComplex.Approximation.RitzResolvent
public import Feec.Semigroup.Impedance

/-!
# Conforming Galerkin schemes for impedance problems

For an impedance triple, Galerkin spaces `Vₕ ⊆ V`, `Wₕ ⊆ H₂` with `c Vₕ ⊆ Wₕ` give a dissipative
scheme on `ι Vₕ ⊕₂ Wₕ`, with the `dissipFEEC` verdict under the approximation property.

## Main results

* `ImpedanceTriple.GalerkinData.galerkin_verdict`: a dense core and the `dissipFEEC` verdict.
* `ImpedanceTriple.GalerkinData.norm_sq_galerkin_sol`: the discrete energy identity.

## References

* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology Metric

@[expose] public noncomputable section

universe u

namespace Feec.HilbertComplex

end Feec.HilbertComplex

/-! ### Conforming Galerkin schemes for impedance triples -/

namespace Feec.ImpedanceTriple

open Feec.HilbertComplex

variable {V H₁ H₂ Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  (T : ImpedanceTriple ℝ V H₁ H₂ Y)

/-- Galerkin data: finite-dimensional `Vₕ ⊆ V` and closed `Wₕ ⊆ H₂` with `c Vₕ ⊆ Wₕ`. -/
structure GalerkinData (κ : Type*) where
  /-- the filter along which the spaces are refined -/
  l : Filter κ
  /-- the discrete energy spaces -/
  Vh : κ → Submodule ℝ V
  [finiteDimensional : ∀ h, FiniteDimensional ℝ (Vh h)]
  /-- the discrete spaces of the second field -/
  Wh : κ → Submodule ℝ H₂
  isClosed_Wh : ∀ h, IsClosed (Wh h : Set H₂)
  c_mem : ∀ h, ∀ v ∈ Vh h, T.c v ∈ Wh h

attribute [instance] GalerkinData.finiteDimensional

variable {T} {κ : Type*} (G : GalerkinData T κ)

namespace GalerkinData

/-- The discrete field space `Eₕ = ι Vₕ`. -/
def Eh (h : κ) : Submodule ℝ H₁ := (G.Vh h).map T.ι.toLinearMap

instance (h : κ) : FiniteDimensional ℝ (G.Eh h) := by unfold Eh; infer_instance

instance (h : κ) : CompleteSpace (G.Wh h) := (G.isClosed_Wh h).completeSpace_coe

/-- `ι : Vₕ ≃ Eₕ`. -/
def ιh (h : κ) : G.Vh h ≃L[ℝ] G.Eh h :=
  (Submodule.equivMapOfInjective T.ι.toLinearMap T.injective (G.Vh h)).toContinuousLinearEquiv

omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace H₂] [CompleteSpace Y] in
@[simp] theorem coe_ιh (h : κ) (v : G.Vh h) : ((G.ιh h v : G.Eh h) : H₁) = T.ι v := rfl

/-- The discrete differential `Cₕ : Eₕ → Wₕ`, `ι v ↦ c v`. -/
def Ch (h : κ) : G.Eh h →L[ℝ] G.Wh h :=
  (T.c ∘L (G.Vh h).subtypeL ∘L (G.ιh h).symm.toContinuousLinearMap).codRestrict (G.Wh h)
    fun e => G.c_mem h _ ((G.ιh h).symm e).2

/-- The discrete trace `Γₕ : Eₕ → Y`, `ι v ↦ γ v`. -/
def Γh (h : κ) : G.Eh h →L[ℝ] Y :=
  T.γ ∘L (G.Vh h).subtypeL ∘L (G.ιh h).symm.toContinuousLinearMap

/-- The discrete state space `Xₕ = Eₕ ⊕₂ Wₕ`. -/
abbrev Xh (h : κ) := WithLp 2 (G.Eh h × G.Wh h)

/-- **The Galerkin generator** `Lₕ (e, P) = (-Cₕ* P - Γₕ* Γₕ e, Cₕ e)`. -/
def Lh (h : κ) : G.Xh h →L[ℝ] G.Xh h :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (G.Eh h) (G.Wh h)).symm.toContinuousLinearMap ∘L
    ((-((ContinuousLinearMap.adjoint (G.Ch h)) ∘L WithLp.sndL 2 ℝ (G.Eh h) (G.Wh h)) -
      (ContinuousLinearMap.adjoint (G.Γh h) ∘L G.Γh h) ∘L WithLp.fstL 2 ℝ (G.Eh h) (G.Wh h)).prod
      (G.Ch h ∘L WithLp.fstL 2 ℝ (G.Eh h) (G.Wh h)))

omit [CompleteSpace V] [CompleteSpace H₁] in
theorem inner_Lh (h : κ) (x : G.Xh h) : ⟪G.Lh h x, x⟫_ℝ = -‖G.Γh h x.fst‖ ^ 2 := by
  rw [WithLp.prod_inner_apply]
  simp only [Lh, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    WithLp.prodContinuousLinearEquiv_symm_apply, ContinuousLinearMap.prod_apply,
    sub_apply, neg_apply, WithLp.sndL_apply,
    WithLp.fstL_apply]
  simp only [inner_sub_left, inner_neg_left, ContinuousLinearMap.adjoint_inner_left]
  change -⟪x.snd, G.Ch h x.fst⟫_ℝ - ⟪G.Γh h x.fst, G.Γh h x.fst⟫_ℝ +
    ⟪G.Ch h x.fst, x.snd⟫_ℝ = _
  rw [real_inner_self_eq_norm_sq, real_inner_comm x.snd]
  ring

omit [CompleteSpace V] [CompleteSpace H₁] in
theorem Lh_dissipative (h : κ) (x : G.Xh h) : RCLike.re ⟪G.Lh h x, x⟫_ℝ ≤ 0 := by
  rw [RCLike.re_to_real, G.inner_Lh]; exact neg_nonpos.2 (sq_nonneg _)

omit [CompleteSpace V] [CompleteSpace H₁] in
theorem Lh_fst (h : κ) (x : G.Xh h) :
    (G.Lh h x).fst = -(ContinuousLinearMap.adjoint (G.Ch h) x.snd) -
      ContinuousLinearMap.adjoint (G.Γh h) (G.Γh h x.fst) := rfl

omit [CompleteSpace V] [CompleteSpace H₁] in
theorem Lh_snd (h : κ) (x : G.Xh h) : (G.Lh h x).snd = G.Ch h x.fst := rfl

omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace H₂] [CompleteSpace Y] in
@[simp] theorem coe_Ch_ιh (h : κ) (v : G.Vh h) : ((G.Ch h (G.ιh h v) : G.Wh h) : H₂) = T.c v := by
  change T.c ((G.ιh h).symm (G.ιh h v) : V) = T.c v
  rw [ContinuousLinearEquiv.symm_apply_apply]

omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace H₂] [CompleteSpace Y] in
@[simp] theorem Γh_ιh (h : κ) (v : G.Vh h) : G.Γh h (G.ιh h v) = T.γ v := by
  simp [Γh]

/-! #### Reading and projection maps -/

/-- **The reading map** `ιₕ : Eₕ ⊕₂ Wₕ → H₁ ⊕₂ H₂`, the inclusion. -/
def incl (h : κ) : G.Xh h →L[ℝ] WithLp 2 (H₁ × H₂) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ H₁ H₂).symm.toContinuousLinearMap ∘L
    (((G.Eh h).subtypeL ∘L WithLp.fstL 2 ℝ (G.Eh h) (G.Wh h)).prod
      ((G.Wh h).subtypeL ∘L WithLp.sndL 2 ℝ (G.Eh h) (G.Wh h)))

/-- **The projection** `πₕ = (P_{Eₕ}, P_{Wₕ})`, componentwise orthogonal projections. -/
def proj (h : κ) : WithLp 2 (H₁ × H₂) →L[ℝ] G.Xh h :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (G.Eh h) (G.Wh h)).symm.toContinuousLinearMap ∘L
    (((G.Eh h).orthogonalProjectionOnto ∘L WithLp.fstL 2 ℝ H₁ H₂).prod
      ((G.Wh h).orthogonalProjectionOnto ∘L WithLp.sndL 2 ℝ H₁ H₂))

omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace H₂] [CompleteSpace Y] in
@[simp] theorem incl_fst (h : κ) (x : G.Xh h) : (G.incl h x).fst = x.fst := rfl
omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace H₂] [CompleteSpace Y] in
@[simp] theorem incl_snd (h : κ) (x : G.Xh h) : (G.incl h x).snd = x.snd := rfl
omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace Y] in
@[simp] theorem proj_fst (h : κ) (z : WithLp 2 (H₁ × H₂)) :
    (G.proj h z).fst = (G.Eh h).orthogonalProjectionOnto z.fst := rfl
omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace Y] in
@[simp] theorem proj_snd (h : κ) (z : WithLp 2 (H₁ × H₂)) :
    (G.proj h z).snd = (G.Wh h).orthogonalProjectionOnto z.snd := rfl

omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace Y] in
theorem proj_incl (h : κ) (x : G.Xh h) : G.proj h (G.incl h x) = x :=
  withLp_prod_ext (by simp) (by simp)

omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace H₂] [CompleteSpace Y] in
theorem norm_incl_apply (h : κ) (x : G.Xh h) : ‖G.incl h x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2,
    WithLp.prod_norm_sq_eq_of_L2]
  simp

omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace Y] in
theorem norm_proj_apply_le (h : κ) (z : WithLp 2 (H₁ × H₂)) : ‖G.proj h z‖ ≤ ‖z‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2,
    WithLp.prod_norm_sq_eq_of_L2, proj_fst, proj_snd]
  have h1 := (G.Eh h).norm_orthogonalProjectionOnto_apply_le z.fst
  have h2 := (G.Wh h).norm_orthogonalProjectionOnto_apply_le z.snd
  gcongr

variable (K : Submodule ℝ (WithLp 2 (H₁ × H₂))) (hK : IsClosed (K : Set (WithLp 2 (H₁ × H₂))))

/-- The conforming Galerkin scheme, a dissipative FEEC discretization of the impedance operator. -/
def galerkin : DissipFEEC T.op κ where
  isMDissipative := T.isMDissipative_op
  K := K
  isClosed_K := hK
  l := G.l
  X := G.Xh
  L := G.Lh
  dissipative := G.Lh_dissipative
  incl := G.incl
  proj := G.proj
  proj_incl := G.proj_incl
  bound := ⟨1, fun h => ⟨ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [G.norm_incl_apply, one_mul], ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
    rw [one_mul]; exact G.norm_proj_apply_le h z⟩⟩

/-! #### The discrete resolvent is the Galerkin projection of the exact one -/

variable (T) in
/-- The energy-space element of `(1 - A)⁻¹ z`. -/
def resWitness (z : WithLp 2 (H₁ × H₂)) : V :=
  T.witness (T.isMDissipative_op.isResolvent_one.toDomain z)

/-- The Galerkin solution `(ι vₕ, P_{Wₕ} g + c vₕ)`, `vₕ` the `V`-projection of the exact `v`. -/
def galerkinRes (h : κ) (z : WithLp 2 (H₁ × H₂)) : G.Xh h :=
  WithLp.toLp 2 (G.ιh h ((G.Vh h).orthogonalProjectionOnto (resWitness T z)),
    (G.Wh h).orthogonalProjectionOnto z.snd +
      G.Ch h (G.ιh h ((G.Vh h).orthogonalProjectionOnto (resWitness T z))))

omit [CompleteSpace Y] in
theorem res_eq (z : WithLp 2 (H₁ × H₂)) :
    (Operator.resolvent T.op 1 z).fst = T.ι (resWitness T z) ∧
    (Operator.resolvent T.op 1 z).snd = z.snd + T.c (resWitness T z) ∧
    ∀ v' : V, ⟪z.fst, T.ι v'⟫_ℝ = ⟪resWitness T z, v'⟫_ℝ + ⟪z.snd, T.c v'⟫_ℝ := by
  have hR := T.isMDissipative_op.isResolvent_one
  set u := hR.toDomain z
  have hsub : (u : WithLp 2 (H₁ × H₂)) - T.op u = z := by
    have := hR.sub_apply_toDomain z; rwa [one_smul] at this
  have h1 : (u : WithLp 2 (H₁ × H₂)).fst - (T.op u).fst = z.fst := by rw [← hsub]; rfl
  have h2 : (u : WithLp 2 (H₁ × H₂)).snd - (T.op u).snd = z.snd := by rw [← hsub]; rfl
  have hι := T.ι_witness u
  have hc := T.c_witness u
  have hw := T.isWeak_witness u
  refine ⟨hι.symm, ?_, fun v' => ?_⟩
  · change (u : WithLp 2 (H₁ × H₂)).snd = _
    rw [resWitness, hc, ← h2]; abel
  · rw [← h1, inner_sub_left, hw v', ← hι, T.inner_eq, resWitness, ← h2, inner_sub_left, ← hc]
    ring

theorem galerkinRes_sub (h : κ) (z : WithLp 2 (H₁ × H₂)) :
    G.galerkinRes h z - G.Lh h (G.galerkinRes h z) = G.proj h z := by
  set vh := (G.Vh h).orthogonalProjectionOnto (resWitness T z)
  obtain ⟨-, -, hz⟩ := res_eq (T := T) z
  refine withLp_prod_ext ?_ ?_
  · rw [WithLp.sub_fst, Lh_fst, proj_fst]
    refine ext_inner_right ℝ fun e' => ?_
    obtain ⟨v', rfl⟩ := (G.ιh h).surjective e'
    have hP : ⟪(G.Wh h).orthogonalProjectionOnto z.snd, G.Ch h (G.ιh h v')⟫_ℝ =
        ⟪z.snd, T.c v'⟫_ℝ := by
      rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right, coe_Ch_ιh]
    have hV : ⟪(vh : V), (v' : V)⟫_ℝ = ⟪resWitness T z, v'⟫_ℝ := by
      rw [← Submodule.coe_inner, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right, coe_ιh, hz v', ← hV, ← hP,
      T.inner_eq, inner_sub_left, inner_sub_left, inner_neg_left,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
    change ⟪G.ιh h vh, G.ιh h v'⟫_ℝ - (-⟪(G.Wh h).orthogonalProjectionOnto z.snd +
      G.Ch h (G.ιh h vh), G.Ch h (G.ιh h v')⟫_ℝ - ⟪G.Γh h (G.ιh h vh), G.Γh h (G.ιh h v')⟫_ℝ) = _
    rw [Γh_ιh, Γh_ιh, inner_add_left, Submodule.coe_inner (G.Eh h), coe_ιh, coe_ιh,
      Submodule.coe_inner (G.Wh h) (G.Ch h (G.ιh h vh)), coe_Ch_ιh, coe_Ch_ιh]
    ring
  · rw [WithLp.sub_snd, Lh_snd, proj_snd]
    change (G.Wh h).orthogonalProjectionOnto z.snd + G.Ch h (G.ιh h vh) - G.Ch h (G.ιh h vh) = _
    abel


theorem discreteRes_galerkin (h : κ) (z : WithLp 2 (H₁ × H₂)) :
    (G.galerkin K hK).discreteRes h (G.proj h z) = G.galerkinRes h z := by
  rw [← G.galerkinRes_sub h z]
  exact boundedRes_apply_sub (G.Lh_dissipative h) _

omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace H₂] [CompleteSpace Y] in
theorem norm_ι_le_and_norm_c_le (v : V) : ‖T.ι v‖ ≤ ‖v‖ ∧ ‖T.c v‖ ≤ ‖v‖ := by
  have e := T.inner_eq v v
  simp only [real_inner_self_eq_norm_sq] at e
  have h1 : 0 ≤ ‖T.γ v‖ ^ 2 := sq_nonneg _
  exact ⟨(sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by nlinarith [sq_nonneg ‖T.c v‖]),
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by nlinarith [sq_nonneg ‖T.ι v‖])⟩

omit [InnerProductSpace ℝ H₁] [InnerProductSpace ℝ H₂] [CompleteSpace H₁] [CompleteSpace H₂] in
theorem norm_withLp_le (x : WithLp 2 (H₁ × H₂)) : ‖x‖ ≤ ‖x.fst‖ + ‖x.snd‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), WithLp.prod_norm_sq_eq_of_L2]
  nlinarith [norm_nonneg x.fst, norm_nonneg x.snd]

omit [CompleteSpace Y] in
theorem norm_incl_galerkinRes_sub_le (h : κ) (z : WithLp 2 (H₁ × H₂)) :
    ‖G.incl h (G.galerkinRes h z) - Operator.resolvent T.op 1 z‖ ≤
      2 * ‖((G.Vh h).starProjection (resWitness T z)) - resWitness T z‖ +
        ‖(G.Wh h).starProjection z.snd - z.snd‖ := by
  obtain ⟨h1, h2, -⟩ := res_eq (T := T) z
  set v := resWitness T z
  set w := (G.Vh h).starProjection v - v
  refine (norm_withLp_le _).trans ?_
  have ef : (G.incl h (G.galerkinRes h z) - Operator.resolvent T.op 1 z).fst = T.ι w := by
    rw [WithLp.sub_fst, h1, incl_fst]
    change T.ι ((G.Vh h).orthogonalProjectionOnto v : V) - T.ι v = _
    rw [← _root_.map_sub]; rfl
  have es : (G.incl h (G.galerkinRes h z) - Operator.resolvent T.op 1 z).snd =
      ((G.Wh h).starProjection z.snd - z.snd) + T.c w := by
    rw [WithLp.sub_snd, h2, incl_snd]
    change ((G.Wh h).orthogonalProjectionOnto z.snd : H₂) +
      ((G.Ch h (G.ιh h ((G.Vh h).orthogonalProjectionOnto v)) : G.Wh h) : H₂) - _ = _
    rw [coe_Ch_ιh, _root_.map_sub]
    simp only [Submodule.starProjection_apply]
    abel
  rw [ef, es]
  have a := (norm_ι_le_and_norm_c_le (T := T) w)
  have b := norm_add_le ((G.Wh h).starProjection z.snd - z.snd) (T.c w)
  linarith [a.1, a.2]

/-- The approximation property: `Vₕ` approximates `V` and `Wₕ` approximates `H₂`. -/
def Approximates : Prop :=
  (∀ v : V, Tendsto (fun h => infDist v (G.Vh h : Set V)) G.l (𝓝 0)) ∧
    ∀ g : H₂, Tendsto (fun h => infDist g (G.Wh h : Set H₂)) G.l (𝓝 0)

omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace H₂] in
theorem tendsto_starProjection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {U : κ → Submodule ℝ E} [∀ h, (U h).HasOrthogonalProjection] {l : Filter κ} {x : E}
    (hU : Tendsto (fun h => infDist x (U h : Set E)) l (𝓝 0)) :
    Tendsto (fun h => (U h).starProjection x) l (𝓝 x) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine hU.congr fun h => ?_
  rw [dist_comm, Submodule.dist_starProjection_eq_infDist]

variable {G} in
omit [CompleteSpace Y] in
theorem tendsto_incl_galerkinRes (hG : G.Approximates) (z : WithLp 2 (H₁ × H₂)) :
    Tendsto (fun h => G.incl h (G.galerkinRes h z)) G.l
      (𝓝 (Operator.resolvent T.op 1 z)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 := tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_starProjection (hG.1 (resWitness T z)))
  have h2 := tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_starProjection (hG.2 z.snd))
  have h3 : Tendsto (fun h => 2 * ‖(G.Vh h).starProjection (resWitness T z) - resWitness T z‖ +
      ‖(G.Wh h).starProjection z.snd - z.snd‖) G.l (𝓝 0) := by
    simpa using (h1.const_mul 2).add h2
  exact squeeze_zero (fun _ => norm_nonneg _) (fun h => G.norm_incl_galerkinRes_sub_le h z) h3

variable {G} in
omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace Y] in
theorem tendsto_incl_proj (hG : G.Approximates) (z : WithLp 2 (H₁ × H₂)) :
    Tendsto (fun h => G.incl h (G.proj h z)) G.l (𝓝 z) := by
  have hE : Tendsto (fun h => (G.Eh h).starProjection z.fst) G.l (𝓝 z.fst) := by
    refine tendsto_starProjection (Metric.tendsto_nhds.2 fun ε hε => ?_)
    obtain ⟨v, hv⟩ : ∃ v, dist z.fst (T.ι v) < ε / 2 :=
      (Metric.denseRange_iff.1 T.denseRange) z.fst _ (half_pos hε)
    have hc := Metric.tendsto_nhds.1 (tendsto_starProjection (hG.1 v)) _ (half_pos hε)
    filter_upwards [hc] with h hh
    rw [Real.dist_eq, sub_zero, abs_of_nonneg infDist_nonneg]
    have hmem : T.ι ((G.Vh h).starProjection v) ∈ (G.Eh h : Set H₁) :=
      ⟨_, (G.Vh h).starProjection_apply_mem v, rfl⟩
    calc infDist z.fst (G.Eh h : Set H₁) ≤ dist z.fst (T.ι ((G.Vh h).starProjection v)) :=
          infDist_le_dist_of_mem hmem
      _ ≤ dist z.fst (T.ι v) + dist (T.ι v) (T.ι ((G.Vh h).starProjection v)) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by
          refine add_lt_add hv (lt_of_le_of_lt ?_ hh)
          rw [dist_eq_norm, dist_eq_norm, ← _root_.map_sub, norm_sub_rev]
          exact (norm_ι_le_and_norm_c_le (T := T) _).1
      _ = ε := add_halves ε
  have hW := tendsto_starProjection (hG.2 z.snd)
  rw [tendsto_iff_norm_sub_tendsto_zero] at hE hW ⊢
  refine squeeze_zero (fun _ => norm_nonneg _) (fun h => (norm_withLp_le _).trans le_rfl) ?_
  simpa using hE.add hW

variable {G} in
/-- The Galerkin core `R(1) D(A)`. -/
def galerkinCore (hG : G.Approximates) : (G.galerkin K hK).Core :=
  DissipFEEC.Core.ofResolvent (G.galerkin K hK)
    (fun z => (tendsto_incl_galerkinRes hG z).congr fun h =>
      (congrArg (G.incl h) (G.discreteRes_galerkin K hK h z)).symm)
    (fun z => tendsto_incl_proj hG z)


/-- **The Galerkin verdict**: under the approximation property, the core `R(1) D(A)` is dense and
the conforming Galerkin scheme has the full `dissipFEEC` verdict. [Pazy1983], §3.4 -/
theorem galerkin_verdict (hG : G.Approximates) :
    (G.galerkinCore K hK hG).Data.topologicalClosure = ⊤ ∧
      (G.galerkin K hK).Verdict (G.galerkinCore K hK hG) :=
  ⟨DissipFEEC.resData_closure T.isMDissipative_op, dissipFEEC _ _⟩

theorem galerkin_sol (h : κ) (x : G.Xh h) (t : ℝ) :
    (G.galerkin K hK).sol h x t = G.incl h ((C0Group.ofBounded (G.Lh h)).S t x) := rfl

omit [CompleteSpace V] [CompleteSpace H₁] in
/-- **The discrete energy identity**: `‖xₕ(t)‖² = ‖xₕ(0)‖² - 2 ∫₀ᵗ ‖Γₕ eₕ(s)‖² ds` for `t ≥ 0`
along the semi-discrete Galerkin flow `e^{t Lₕ}`. -/
theorem norm_sq_galerkin_sol (h : κ) (x : G.Xh h) {t : ℝ} (ht : 0 ≤ t) :
    ‖G.incl h ((C0Group.ofBounded (G.Lh h)).S t x)‖ ^ 2 = ‖G.incl h x‖ ^ 2 -
      2 * ∫ s in (0 : ℝ)..t, ‖G.Γh h ((C0Group.ofBounded (G.Lh h)).S s x).fst‖ ^ 2 := by
  set S := (C0Group.ofBounded (G.Lh h)).toC0Semigroup
  have hx : x ∈ S.generator.domain := C0Group.mem_domain_generator_ofBounded (G.Lh h) x
  have e := S.norm_sq_S_apply ⟨x, hx⟩ ht
  have hint : ∫ s in (0 : ℝ)..t, 2 * RCLike.re ⟪S.S s (S.generator ⟨x, hx⟩), S.S s x⟫_ℝ =
      ∫ s in (0 : ℝ)..t, -(2 * ‖G.Γh h ((C0Group.ofBounded (G.Lh h)).S s x).fst‖ ^ 2) := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    have hg : S.generator ⟨x, hx⟩ = G.Lh h x :=
      C0Group.generator_ofBounded_apply (G.Lh h) ⟨x, hx⟩
    have hc : S.S s (G.Lh h x) = G.Lh h (S.S s x) :=
      (congrArg (fun M : G.Xh h →L[ℝ] G.Xh h => M x)
        (ContinuousLinearMap.commute_exp_ofReal_smul (G.Lh h) s).eq).symm
    have hi := G.inner_Lh h (S.S s x)
    rw [hg, hc, RCLike.re_to_real, hi, mul_neg]
    rfl
  rw [G.norm_incl_apply, G.norm_incl_apply]
  change ‖S.S t x‖ ^ 2 = _
  rw [e, hint, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
  ring


/-! #### Existence: Galerkin spaces from dense sequences -/

section DenseSeq

open TopologicalSpace

variable [SeparableSpace V] [SeparableSpace H₂]

variable (T) in
/-- Galerkin spaces from dense sequences of `V` and `H₂`, along `atTop`. -/
def ofDenseSeq : GalerkinData T ℕ where
  l := atTop
  Vh n := Submodule.span ℝ (Set.range fun i : Fin n => denseSeq V i)
  finiteDimensional n := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  Wh n := (Submodule.span ℝ (Set.range fun i : Fin n => denseSeq H₂ i)) ⊔
    (Submodule.span ℝ (Set.range fun i : Fin n => denseSeq V i)).map T.c.toLinearMap
  isClosed_Wh n := by
    have : FiniteDimensional ℝ (Submodule.span ℝ (Set.range fun i : Fin n => denseSeq V i)) :=
      FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
    have : FiniteDimensional ℝ (Submodule.span ℝ (Set.range fun i : Fin n => denseSeq H₂ i)) :=
      FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
    exact Submodule.closed_of_finiteDimensional _
  c_mem n v hv := Submodule.mem_sup_right ⟨v, hv, rfl⟩

omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace H₂] in
theorem tendsto_infDist_span_denseSeq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SeparableSpace E] {U : ℕ → Submodule ℝ E}
    (hU : ∀ n, ∀ i : Fin n, denseSeq E i ∈ U n) (x : E) :
    Tendsto (fun n => infDist x (U n : Set E)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨i, hi⟩ : ∃ i, dist x (denseSeq E i) < ε :=
    (Metric.denseRange_iff.1 (denseRange_denseSeq E)) x ε hε
  refine ⟨i + 1, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg infDist_nonneg]
  exact (infDist_le_dist_of_mem (hU n ⟨i, by omega⟩)).trans_lt hi

omit [CompleteSpace V] [CompleteSpace H₁] [CompleteSpace H₂] [CompleteSpace Y] in
theorem approximates_ofDenseSeq : (ofDenseSeq T).Approximates :=
  ⟨tendsto_infDist_span_denseSeq fun _ i => Submodule.subset_span ⟨i, rfl⟩,
    tendsto_infDist_span_denseSeq fun _ i =>
      Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)⟩

end DenseSeq


end GalerkinData

end Feec.ImpedanceTriple
