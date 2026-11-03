module

public import Feec.Models.Cube.ParitySmoother
public import Feec.Models.Cube.DeRhamPartialFEM

/-!
# Parity smoothing estimates on the Freudenthal meshes of the cube

The parity smoother `R^J_ρ` (`Feec.Models.Cube.ParitySmoother`) composed with the canonical
interpolant `Π_h` of the polynomial families `S` gives commuting maps `Q_N = Π_h R^J` of the
discrete partially-homogeneous complexes `V_{h,Γ_J} = polyPartial n S N J ⊆ HΛ_J(Q)`. For kernels
of radius `γ h_N / 32` they are bounded uniformly in `N` and close to the identity on
`V_{h,Γ_J}`, hence yield uniformly bounded cochain projections `π_N = J_N⁻¹ Q_N`
([AFW2010], §5.5; [ChristiansenWinther2008]) for every class `J`, without dilations.

## Main definitions

* `FEM.paritySmoothForm`: the smoothed form field `ρ ⋆ ext_J u`;
  `LocalElement.paritySmoothedCommutingMap`, `FEM.paritySmoothed n S N J ρ`: the commuting maps.
* `FEM.parKernel n γ`: the product kernels of radius `γ h_N / 32`.
* `FEM.ParitySmoothingEstimates n J S ρ C`: uniform `L²` bound and closeness `½` on `V_{h,Γ_J}`;
  `ParitySmoothingEstimates.proj`: the smoothed projections.

## Main results

* `FEM.paritySmoothingEstimates_parKernel`, `FEM.paritySmoothing_exists`: the estimates hold for
  every class `J` and every admissible sequence `S`.
* `FEM.exists_uniform_cochainProjection_part`: uniformly bounded (`L²` and graph norms) cochain
  projections onto `V_{h,Γ_J}`; the homogeneous classes `J = ∅` and `J = univ` are alternatives
  to the dilation smoothers `pMax`, `pMin`.
* `FEM.ParitySmoothingEstimates.norm_sub_proj_le_grad`: `‖y - π_N y‖ ≤ C h_N Σₛ ‖∇ yₛ‖` when
  `ext_J y` has `H¹` coefficients.
* `FEM.ParitySmoothingEstimates.norm_sub_proj_le_smooth`: the high-order rate
  `‖w - π_N w‖ ≤ (1 + 2C) A_k h_N^{s+1} sup_{cl Q} ‖D^{s+1} w‖` for `C^{s+1}` forms whose tangential
  components vanish on the faces normal to `J` (`FEM.exists_mem_polyPartial_le_smooth`: the
  canonical interpolant lies in `V_{h,Γ_J}`), up to the polynomial order.
  The `L²`-based form `‖y - π_N y‖ ≲ h_N^m ‖Dᵐ ext_J y‖_{L²}` for `m ≥ 2` is not formalized.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010], §5.5
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped ContDiff ENNReal

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex ExteriorFibre
open Feec.Models.Cube.ParitySmoother
open Feec.Models.Cube.DeRhamIdent (dPart HQpartZ)

variable {n : ℕ}

/-! ### The smoothed form field of the parity smoother -/

section SmoothForm

variable {Ω : Set (Fin n → ℝ)} (ρ : ReflKernel n) (J : Finset (Fin n))

/-- The coefficients `ρ ⋆ ext_{c(J, s)} u_s` of the parity-smoothed form. -/
def parCoeff {k : ℤ} (u : L2F ℝ Ω (formIdx n k)) (s : formIdx n k) : (Fin n → ℝ) → ℝ :=
  smoothFun ρ (pvec J s.1) ((u s : L2 ℝ Ω) : (Fin n → ℝ) → ℝ)

theorem integrableOn_Q_of_eq (hΩ : Ω = Geometry.Q (Fin n)) (f : L2 ℝ Ω) :
    IntegrableOn (f : (Fin n → ℝ) → ℝ) (Geometry.Q (Fin n)) := by
  subst hΩ; exact integrableOn_L2 f

theorem contDiff_parCoeff (hΩ : Ω = Geometry.Q (Fin n)) {k : ℤ} (u : L2F ℝ Ω (formIdx n k))
    (s : formIdx n k) : ContDiff ℝ ∞ (parCoeff ρ J u s) :=
  contDiff_smoothFun ρ _ (integrableOn_Q_of_eq hΩ _)

/-- **The parity-smoothed `k`-form** `x ↦ Σₛ (ρ ⋆ ext_{c(J,s)} uₛ)(x) dxₛ`, a smooth form field on
`ℝⁿ`, as a linear map `L²(Ω; Λᵏ) → C¹Λᵏ` (for `Ω = Q`). -/
def paritySmoothForm (hΩ : Ω = Geometry.Q (Fin n)) (k : ℤ) :
    L2F ℝ Ω (formIdx n k) →ₗ[ℝ] c1Forms n where
  toFun u := ⟨fun x t => formExt (parCoeff ρ J u) t x,
    mem_c1Forms.2 (contDiff_pi.2 fun t =>
      (contDiff_formExt (contDiff_parCoeff ρ J hΩ u) t).of_le (by exact_mod_cast le_top))⟩
  map_add' u v := by
    subst hΩ
    refine Subtype.ext (funext fun x => funext fun t => ?_)
    change formExt (parCoeff ρ J (u + v)) t x =
      formExt (parCoeff ρ J u) t x + formExt (parCoeff ρ J v) t x
    unfold formExt
    split_ifs with h
    · simp only [parCoeff, PiLp.add_apply]
      rw [smoothFun_congr_ae ρ _ (Lp.coeFn_add _ _),
        smoothFun_add ρ _ (integrableOn_L2 _) (integrableOn_L2 _)]
      rfl
    · simp
  map_smul' a u := by
    subst hΩ
    refine Subtype.ext (funext fun x => funext fun t => ?_)
    change formExt (parCoeff ρ J (a • u)) t x = a * formExt (parCoeff ρ J u) t x
    unfold formExt
    split_ifs with h
    · simp only [parCoeff, PiLp.smul_apply]
      rw [smoothFun_congr_ae ρ _ (Lp.coeFn_smul _ _), smoothFun_smul]
      rfl
    · simp

theorem paritySmoothForm_apply (hΩ : Ω = Geometry.Q (Fin n)) (k : ℤ) (u : L2F ℝ Ω (formIdx n k))
    (x : Fin n → ℝ) (t : Finset (Fin n)) :
    (paritySmoothForm ρ J hΩ k u : FormField n) x t = formExt (parCoeff ρ J u) t x := rfl

theorem isDeg_paritySmoothForm (hΩ : Ω = Geometry.Q (Fin n)) (k : ℕ)
    (u : L2F ℝ Ω (formIdx n k)) (x : Fin n → ℝ) :
    IsDeg k ((paritySmoothForm ρ J hΩ k u : FormField n) x) := by
  intro t ht
  rw [paritySmoothForm_apply]
  unfold formExt
  split_ifs with h
  · exact absurd (by exact_mod_cast h) ht
  · rfl

theorem formComp_paritySmoothForm (hΩ : Ω = Geometry.Q (Fin n)) (k : ℕ)
    (u : L2F ℝ Ω (formIdx n k)) :
    formComp (k := (k : ℤ)) (paritySmoothForm ρ J hΩ k u : FormField n) = parCoeff ρ J u := by
  funext s x
  change formExt (parCoeff ρ J u) s.1 x = _
  rw [formExt_val]

theorem coord_mem_Icc_of_mem_closure {x : Fin n → ℝ} (hx : x ∈ closure (Geometry.Q (Fin n)))
    (j : Fin n) : x j ∈ Icc (0 : ℝ) (1 / 2) := by
  have hsub : closure (Geometry.Q (Fin n)) ⊆ univ.pi fun _ => Icc (0 : ℝ) (1 / 2) :=
    closure_minimal (fun y hy i _ => Ioo_subset_Icc_self (Geometry.mem_Q.1 hy i))
      (isClosed_set_pi fun _ _ => isClosed_Icc)
  exact hsub hx j (mem_univ j)

/-- **`d` of the parity-smoothed form is the parity-smoothed form of `d_J u`** at every point of
`cl Ω` (`Feec.Models.Cube.ParitySmoother.extD_smoothFun_eq`). -/
theorem extDeriv_paritySmoothForm (hΩ : Ω = Geometry.Q (Fin n)) (k : ℕ)
    (u : (dPart Ω J (k : ℤ)).domain) {x : Fin n → ℝ} (hx : x ∈ closure Ω) :
    extDeriv (paritySmoothForm ρ J hΩ k u : FormField n) x =
      (paritySmoothForm ρ J hΩ ((k : ℤ) + 1) (dPart Ω J (k : ℤ) u) : FormField n) x := by
  subst hΩ
  funext t
  by_cases ht : (#t : ℤ) = (k : ℤ) + 1
  · have h1 := extDerivOp_apply_formComp
      (isDeg_paritySmoothForm ρ J rfl k (u : L2F ℝ (Geometry.Q (Fin n)) (formIdx n k)))
      ⟨t, ht⟩ x
    rw [formComp_paritySmoothForm] at h1
    rw [← h1, extDerivOp_apply, paritySmoothForm_apply, formExt_of_card _ ht]
    exact extD_smoothFun_eq ρ J k u ⟨t, ht⟩ (coord_mem_Icc_of_mem_closure hx)
  · have h0 := IsDeg.extDeriv
      (isDeg_paritySmoothForm ρ J rfl k (u : L2F ℝ (Geometry.Q (Fin n)) (formIdx n k))) x t
      (fun h => ht (by exact_mod_cast h))
    rw [h0, paritySmoothForm_apply]
    simp [formExt, ht]

/-- **The tangential components of the parity-smoothed form vanish on the faces normal to `J`.** -/
theorem paritySmoothForm_eq_zero_of_face (hΩ : Ω = Geometry.Q (Fin n)) {k : ℤ}
    (u : L2F ℝ Ω (formIdx n k)) {j : Fin n} (hjJ : j ∈ J) {x : Fin n → ℝ}
    (hx : x j = 0 ∨ x j = 1 / 2) {t : Finset (Fin n)} (ht : j ∉ t) :
    (paritySmoothForm ρ J hΩ k u : FormField n) x t = 0 := by
  rw [paritySmoothForm_apply]
  unfold formExt
  split_ifs with h
  · exact smoothFun_eq_zero ρ (isParity_pvec J t) _ (pvec_of_mem_of_notMem hjJ ht) hx
  · rfl

end SmoothForm

/-! ### The smoothed canonical interpolant -/

/-- **Tangential traces on a face inside a hyperplane** `{x_j = c}`: a form whose components not
containing `j` vanish on the hyperplane has zero tangential trace on the simplex of `g`. -/
theorem tangentialTraceEq_zero_of_hyperplane {k : ℕ} {w : FormField n}
    {g : Finset (Fin n → ℝ)} {j : Fin n} {c : ℝ} (hg : ∀ v ∈ g, v j = c)
    (hw : ∀ x : Fin n → ℝ, x j = c → ∀ t, j ∉ t → w x t = 0) :
    ∀ x ∈ convexHull ℝ (g : Set (Fin n → ℝ)), TangentialTraceEq g k (w x) 0 := by
  intro x hx V hV
  have hconv : Convex ℝ {v : Fin n → ℝ | v j = c} := by
    intro a ha b hb p q hp hq hpq
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
    rw [ha, hb, ← add_mul, hpq, one_mul]
  have hxj : x j = c := convexHull_min (fun v hv => hg v hv) hconv hx
  have hspan : vectorSpan ℝ (g : Set (Fin n → ℝ)) ≤
      LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j) := by
    rw [vectorSpan_def]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    simp [hg a ha, hg b hb]
  have hVj : V j = 0 := funext fun l => by simpa using hspan (hV l)
  rw [pullback_zero, Pi.zero_apply, pullback_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  by_cases hjt : j ∈ t
  · rw [wedgeProd_eq_sgn_smul_wedge_erase V hjt, hVj, wedge_zero_left, smul_zero, Pi.zero_apply,
      mul_zero]
  · rw [hw x hxj t hjt, zero_mul]

end Feec.Models.Cube.FEM

namespace Feec.FiniteElement.LocalElement

open Feec.Domain Feec.Mesh Feec.HilbertComplex ExteriorFibre
open Feec.Models.Cube Feec.Models.Cube.ParitySmoother Feec.Models.Cube.FEM
open Feec.Models.Cube.DeRhamIdent (dPart HQpartZ)

variable {n : ℕ}
variable (E : LocalElement n) (M : SimplicialMesh n) (ρ : ReflKernel n) (J : Finset (Fin n))

/-- **The parity-smoothed interpolant has vanishing DOFs on the faces normal to `J`**:
`Π_h R u ∈ Λ_{h,Γ_J}ᵏ`. -/
theorem globalInterp_paritySmoothForm_mem (hM : M.domain = Geometry.Q (Fin n)) (k : ℕ)
    (u : L2F ℝ M.domain (formIdx n k)) :
    (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms
      (paritySmoothForm ρ J hM k u)) : E.Piecewise M k) ∈
        E.globalSpacePartial M (partialFaces n J) k := by
  refine ⟨(E.globalInterp M k _).2, fun T g hg ⟨F, ⟨j, hjJ, hF⟩, hgF⟩ i => ?_⟩
  rw [LocalElement.localDof_globalInterp _ _ _ _ _ _ hg]
  have hc : ∃ c : ℝ, (c = 0 ∨ c = 1 / 2) ∧ ∀ v ∈ g, v j = c := by
    rcases hF with h | h
    · exact ⟨0, Or.inl rfl, fun v hv => h v (hgF hv)⟩
    · exact ⟨1 / 2, Or.inr rfl, fun v hv => h v (hgF hv)⟩
  obtain ⟨c, hc, hgc⟩ := hc
  have h0 : E.dof g k i (Submodule.inclusion c1Forms_le_contForms
      (paritySmoothForm ρ J hM k u)) = E.dof g k i 0 :=
    E.dof_congr i (tangentialTraceEq_zero_of_hyperplane hgc fun x hx t ht =>
      paritySmoothForm_eq_zero_of_face ρ J hM u hjJ (by rw [hx]; exact hc) ht)
  rw [h0, map_zero]

/-- **The parity-smoothed canonical interpolant** `Q = Π_h R : L²(Ω; Λᵏ) → V_{h,Γ_J}ᵏ`; zero in
negative degrees. -/
def paritySmoothedInterp (hM : M.domain = Geometry.Q (Fin n)) :
    ∀ k : ℤ, L2F ℝ M.domain (formIdx n k) →ₗ[ℝ] L2F ℝ M.domain (formIdx n k)
  | Int.ofNat k => E.glue M k ∘ₗ (E.globalSpace M k).subtype ∘ₗ E.globalInterp M k ∘ₗ
      Submodule.inclusion c1Forms_le_contForms ∘ₗ paritySmoothForm ρ J hM k
  | Int.negSucc _ => 0

theorem paritySmoothedInterp_natCast (hM : M.domain = Geometry.Q (Fin n)) (k : ℕ)
    (u : L2F ℝ M.domain (formIdx n k)) :
    E.paritySmoothedInterp M ρ J hM k u = E.glue M k (E.globalInterp M k
      (Submodule.inclusion c1Forms_le_contForms (paritySmoothForm ρ J hM k u)) :
        E.Piecewise M k) := rfl

theorem paritySmoothedInterp_mem (hM : M.domain = Geometry.Q (Fin n)) (k : ℤ)
    (u : L2F ℝ M.domain (formIdx n k)) :
    E.paritySmoothedInterp M ρ J hM k u ∈ E.VPartial M (partialFaces n J) k := by
  rcases k with k | k
  · exact ⟨⟨_, E.globalInterp_paritySmoothForm_mem M ρ J hM k u⟩, rfl⟩
  · exact Submodule.zero_mem _

/-- **`d_J Q u = Q d_J u`**: the canonical interpolant commutes with `d` on smooth forms
(`globalInterp_extDeriv`), sees only `cl Ω` (`globalInterp_congr`), and the parity smoother
commutes with `d_J` there (`extDeriv_paritySmoothForm`). -/
theorem dPart_paritySmoothedInterp [NeZero n] (hM : M.domain = Geometry.Q (Fin n)) (k : ℕ)
    (u : (dPart M.domain J (k : ℤ)).domain) :
    ∃ h : E.paritySmoothedInterp M ρ J hM k u ∈ (dPart M.domain J (k : ℤ)).domain,
      dPart M.domain J (k : ℤ) ⟨_, h⟩ =
        E.paritySmoothedInterp M ρ J hM ((k : ℤ) + 1) (dPart M.domain J (k : ℤ) u) := by
  set w := paritySmoothForm ρ J hM k (u : L2F ℝ M.domain (formIdx n k))
  obtain ⟨h, hval⟩ := glue_mem_dPart E hM J k
    ⟨_, E.globalInterp_paritySmoothForm_mem M ρ J hM k (u : L2F ℝ M.domain (formIdx n k))⟩
  refine ⟨h, hval.trans ?_⟩
  have h1 : E.dPiecewise M k
      (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w) : E.Piecewise M k) =
      (E.dGlobal M k (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w)) :
        E.Piecewise M (k + 1)) := rfl
  change E.glue M ((k : ℤ) + 1) (E.dPiecewise M k
    (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w) : E.Piecewise M k)) = _
  rw [h1, ← globalInterp_extDeriv]
  have h2 : E.globalInterp M (k + 1) (extDerivC1 w) = E.globalInterp M (k + 1)
      (Submodule.inclusion c1Forms_le_contForms
        (paritySmoothForm ρ J hM ((k + 1 : ℕ) : ℤ) (dPart M.domain J (k : ℤ) u))) :=
    E.globalInterp_congr M (k + 1) fun x hx => extDeriv_paritySmoothForm ρ J hM k u hx
  rw [h2]
  rfl

/-- **The parity-smoothed interpolant as a commuting map** into the finite element subcomplex
`V_{h,Γ_J} ⊆ HΛ_J(Ω)` (`Ω = Q`): `d Q = Q d` in every degree. -/
def paritySmoothedCommutingMap [NeZero n] (hM : M.domain = Geometry.Q (Fin n)) :
    (subcomplexPart E M hM J).CommutingMap where
  Q := E.paritySmoothedInterp M ρ J hM
  mem i x := E.paritySmoothedInterp_mem M ρ J hM i x
  comm i j x := by
    by_cases hij : i + 1 = j
    · subst hij
      have hd := DeRhamIdent.HQpartZ_d (isOpen_of_eq_Q hM) hM.le J i
      rcases i with k | k
      · rw [LinearPMap.apply_eq_of_eq' hd, LinearPMap.apply_eq_of_eq' hd x]
        obtain ⟨h, hv⟩ := E.dPart_paritySmoothedInterp M ρ J hM k ⟨x.1, hd ▸ x.2⟩
        exact hv
      · have hsub := LocalElement.subsingleton_L2F_negSucc M.domain (n := n) k
        have h0 : ∀ y : ((HQpartZ (isOpen_of_eq_Q hM) hM.le J).d (Int.negSucc k)
            (Int.negSucc k + 1)).domain, (HQpartZ (isOpen_of_eq_Q hM) hM.le J).d _ _ y = 0 := by
          intro y
          have : y = 0 := Subtype.ext (Subsingleton.elim _ _)
          rw [this, LinearPMap.map_zero]
        rw [h0, h0]
        exact (E.paritySmoothedInterp M ρ J hM _).map_zero.symm
    · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hij),
        HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hij)]
      exact (E.paritySmoothedInterp M ρ J hM j).map_zero.symm

end Feec.FiniteElement.LocalElement

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex ExteriorFibre
open Feec.Models.Cube.ParitySmoother
open Feec.Models.Cube.DeRhamIdent (dPart HQpartZ)

variable {n : ℕ}

/-! ### The parity mollifier at the mesh scale -/

theorem parRadius_pos {γ : ℝ} (hγ : 0 < γ) (N : ℕ) : 0 < γ * hN N / 32 := by
  have := hN_pos N; positivity

theorem parRadius_lt {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) : γ * hN N / 32 < 1 / 2 := by
  have h1 := hN_le N
  have h0 := hN_pos N
  nlinarith

variable (n) in
/-- **The parity mollifier on the level-`(N + 1)` mesh**: the product kernel of radius
`ε_N = γ h_N / 32`. -/
def parKernel (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) : ReflKernel n :=
  prodKernel (γ * hN N / 32) (parRadius_pos hγ N) (parRadius_lt hγ hγ1 N)

theorem parKernel_radius {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) :
    (parKernel n γ hγ hγ1 N).radius = γ * hN N / 32 := rfl

theorem parKernel_le {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) (x : Fin n → ℝ) :
    parKernel n γ hγ hγ1 N x ≤ (32 / (γ * hN N)) ^ n := by
  refine (prodKernel_le _ _ _ x).trans (le_of_eq ?_)
  congr 1; field_simp

/-! ### The uniform `L²` bound -/

namespace Poly

variable (S : PolySeq)

end Poly

theorem integrableOn_sq_Q_of_eq {Ω : Set (Fin n → ℝ)} (hΩ : Ω = Geometry.Q (Fin n))
    (f : L2 ℝ Ω) :
    IntegrableOn (fun z => (f : (Fin n → ℝ) → ℝ) z ^ 2) (Geometry.Q (Fin n)) := by
  subst hΩ; exact integrableOn_sq_L2 f

/-- **The pointwise bound of the parity-smoothed field by the local mass** on a mesh simplex:
`|R x (y)ₛ|² ≤ 3ⁿ (32 / (γ h_N))ⁿ m_T(x)`. -/
theorem abs_paritySmoothForm_le (J : Finset (Fin n)) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {N : ℕ} {k : ℤ} (x : L2F ℝ (mesh n N).domain (formIdx n k))
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ (mesh n N).simplices) {y : Fin n → ℝ}
    (hy : y ∈ T.closedInterior) (s : Finset (Fin n)) :
    |(paritySmoothForm (parKernel n γ hγ hγ1 N) J (mesh_domain_eq_Q N) k x : FormField n) y s| ≤
      √(3 ^ n * (32 / (γ * hN N)) ^ n * locMass x T) := by
  have hD : (mesh n N).domain = Geometry.Q (Fin n) := mesh_domain_eq_Q N
  have hyc : y ∈ closure (Geometry.Q (Fin n)) := by
    rw [← hD]; exact (mesh n N).closedInterior_subset_closure hT hy
  have hyI := coord_mem_Icc_of_mem_closure hyc
  rw [paritySmoothForm_apply]
  unfold formExt
  split_ifs with hs
  · set s' : formIdx n k := ⟨s, hs⟩
    set f := ((x s' : L2 ℝ (mesh n N).domain) : (Fin n → ℝ) → ℝ)
    have h1 := sq_smoothFun_le_ball (parKernel n γ hγ hγ1 N) (isParity_pvec J s)
      (integrableOn_Q_of_eq hD (x s')) (integrableOn_sq_Q_of_eq hD (x s')) hyI
      (parKernel_le hγ hγ1 N)
    have h2 : ∫ t in Metric.closedBall y (parKernel n γ hγ hγ1 N).radius,
        (Geometry.Q (Fin n)).indicator f t ^ 2 ≤ locMass x T := by
      have hsub : Metric.closedBall y (parKernel n γ hγ hγ1 N).radius ⊆
          Metric.cthickening (2 * hN N) T.closedInterior := by
        refine (Metric.closedBall_subset_cthickening hy _).trans
          (Metric.cthickening_mono ?_ _)
        rw [parKernel_radius]
        have := hN_pos N
        nlinarith
      have e : (Geometry.Q (Fin n)).indicator f = (mesh n N).domain.indicator f := by rw [hD]
      rw [e]
      refine (setIntegral_mono_set (integrable_sq_indicator _).integrableOn
        (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall hsub)).trans ?_
      exact Finset.single_le_sum (f := fun s'' : formIdx n k =>
        ∫ t in Metric.cthickening (2 * hN N) T.closedInterior,
          ((mesh n N).domain.indicator ((x s'' : L2 ℝ (mesh n N).domain) :
            (Fin n → ℝ) → ℝ) t) ^ 2)
        (fun s'' _ => setIntegral_nonneg Metric.isClosed_cthickening.measurableSet
          fun _ _ => sq_nonneg _) (Finset.mem_univ s')
    rw [← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt (h1.trans ?_)
    have := hN_pos N
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  · simp only [Pi.zero_apply, abs_zero]; exact Real.sqrt_nonneg _

/-- **The uniform `L²` bound of the parity-smoothed interpolants** `Q_N = Π_h R_N` of an
admissible sequence, every class `J`: `‖Q_N x‖ ≤ C ‖x‖` for all `N`, all degrees and all `x`,
with `C` depending only on `n`, `S` and `γ`. -/
theorem exists_norm_paritySmoothedInterp_le (S : PolySeq) (J : Finset (Fin n)) {γ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ C, 0 ≤ C ∧ ∀ (N k : ℕ) (x : L2F ℝ (mesh n N).domain (formIdx n k)),
      ‖(polyElement n S).paritySmoothedInterp (mesh n N) (parKernel n γ hγ hγ1 N) J
        (mesh_domain_eq_Q N) k x‖ ≤ C * ‖x‖ := by
  choose B hB0 hB using fun k : ℕ => Poly.exists_dofBound (n := n) S k
  choose D hD0 hD using fun k : ℕ => Poly.exists_coeffBound (n := n) S k
  have hK : ∀ k, 0 ≤ 2 ^ n * (B k * Module.finrank ℝ (S.space n k) * D k) ^ 2 *
      (3 ^ n * (32 / γ) ^ n) * ((6 ^ n * n.factorial : ℕ) : ℝ) := fun k => by
    have := hB0 k; have := hD0 k; positivity
  refine ⟨_, Real.sqrt_nonneg _, fun N k x => norm_le_sqrt_sum_of_sq_le hK fun _ => ?_⟩
  rw [(polyElement n S).paritySmoothedInterp_natCast, mul_assoc]
  have hh := hN_pos N
  refine norm_sq_glue_le_locMass _ x _ (by have := hB0 k; have := hD0 k; positivity)
    fun T hT => ?_
  have hL := locMass_nonneg x T
  refine (Poly.sum_integral_sq_globalInterp_le S (hB k) (hB0 k) (hD k) hT (Real.sqrt_nonneg _)
    fun y hy s => abs_paritySmoothForm_le J hγ hγ1 x hT hy s).trans (le_of_eq ?_)
  have hr2 : √(3 ^ n * (32 / (γ * hN N)) ^ n * locMass x T) ^ 2 =
      3 ^ n * (32 / (γ * hN N)) ^ n * locMass x T := Real.sq_sqrt (by positivity)
  rw [show (32 / γ) ^ n = hN N ^ n * (32 / (γ * hN N)) ^ n by rw [← mul_pow]; congr 1; field_simp]
  linear_combination (2 ^ n * hN N ^ n * (B k * Module.finrank ℝ (S.space n k) * D k) ^ 2) * hr2

/-! ### Faces of the mesh near the faces of the cube -/

/-- **A good point of a face near `{y_i = 0}`**: if a point of a face `g` of a mesh simplex with
barycentric weights `≥ γ` has `i`-th coordinate `< γ h_N / 2`, then the whole face lies in
`{y_i = 0}` (`coord_eq_zero_of_near`). -/
theorem face_coord_eq_zero {N : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T) {m : ℕ}
    (hg : #g = m + 1) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2) {ξ : Fin m → ℝ}
    (hμ : ∀ a, γ ≤ refBary ξ a) {i : Fin n}
    (hx : simplexMap (lexEnum g m) ξ i < γ * hN N / 2) : ∀ v ∈ g, v i = 0 := by
  intro v hv
  obtain ⟨a, rfl⟩ : v ∈ Set.range (lexEnum g m) := by rw [range_lexEnum hg]; exact hv
  exact coord_eq_zero_of_near hT (fun a => hgT (lexEnum_mem hg a)) hγ hγ2 hμ (sum_refBary ξ)
    (by rw [← simplexMap_eq_sum]; exact hx) a

/-- **A good point of a face near `{y_i = ½}`**: the upper analogue of `face_coord_eq_zero`. -/
theorem face_coord_eq_half {N : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T) {m : ℕ}
    (hg : #g = m + 1) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2) {ξ : Fin m → ℝ}
    (hμ : ∀ a, γ ≤ refBary ξ a) {i : Fin n}
    (hx : 1 / 2 - γ * hN N / 2 < simplexMap (lexEnum g m) ξ i) : ∀ v ∈ g, v i = 1 / 2 := by
  intro v hv
  obtain ⟨a, rfl⟩ : v ∈ Set.range (lexEnum g m) := by rw [range_lexEnum hg]; exact hv
  exact coord_eq_half_of_near hT (fun a => hgT (lexEnum_mem hg a)) hγ hγ2 hμ (sum_refBary ξ)
    (by rw [← simplexMap_eq_sum]; exact hx) a

/-- A pullback only sees the components whose rows are nonzero. -/
theorem pullback_congr_of_rows {ι κ : Type*} [LinearOrder ι] [Fintype ι] [LinearOrder κ]
    (B : ι → κ → ℝ) {α β : Finset ι → ℝ} (h : ∀ s, α s = β s ∨ ∃ i ∈ s, B i = 0) :
    pullback B α = pullback B β := by
  unfold pullback
  refine Finset.sum_congr rfl fun s _ => ?_
  rcases h s with h | ⟨i, hi, hB⟩
  · rw [h]
  · rw [wedgeProd_eq_zero_of_mem hi hB, smul_zero, smul_zero]

/-! ### The integrand of the DOF error -/

section Integrand

variable {Ω : Set (Fin n → ℝ)} (ρ : ReflKernel n) (J : Finset (Fin n))

/-- The parity extensions of the components of an `L²` `k`-form at a point, indexed by all
subsets. -/
def parField {k : ℤ} (v : L2F ℝ Ω (formIdx n k)) (t : Fin n → ℝ) : Finset (Fin n) → ℝ :=
  formExt fun r : formIdx n k => parExt (pvec J r.1) ((v r : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) t

/-- **The DOF integrand of `v - R v` as a mollified average**:
`Σₛ (α - R v (x))ₛ cₛ = ∫ ρ(x - t) Σₛ (α - ext v (t))ₛ cₛ dt`. -/
theorem sum_sub_paritySmoothForm_mul_eq (hΩ : Ω = Geometry.Q (Fin n)) {k : ℕ}
    (v : L2F ℝ Ω (formIdx n k)) (α c : Finset (Fin n) → ℝ) (x : Fin n → ℝ) :
    ∑ s, (α s - (paritySmoothForm ρ J hΩ k v : FormField n) x s) * c s =
      ∫ t, ρ (x - t) * ∑ s, (α s - parField J v t s) * c s := by
  classical
  have hR : ∀ s, (paritySmoothForm ρ J hΩ k v : FormField n) x s =
      ∫ t, parField J v t s * ρ (x - t) := by
    intro s
    rw [paritySmoothForm_apply]
    unfold formExt parField
    split_ifs with h
    · rw [parCoeff, smoothFun_apply]
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      simp only [formExt, h, dite_true]
    · simp only [formExt, h, dite_false, zero_mul, integral_zero, Pi.zero_apply]
  have hI : ∀ s, Integrable fun t => parField J v t s * ρ (x - t) := by
    intro s
    unfold parField formExt
    split_ifs with h
    · exact integrable_parExt_mul_comp_sub ρ _ (integrableOn_Q_of_eq hΩ _) x
    · simp
  have hρ := ρ.integrable_comp_sub x
  have hρ1 := ρ.integral_comp_sub x
  have hterm : ∀ s, Integrable fun t => ρ (x - t) * ((α s - parField J v t s) * c s) := by
    intro s
    refine ((hρ.const_mul (α s * c s)).sub ((hI s).const_mul (c s))).congr
      (ae_of_all _ fun t => ?_)
    simp only [Pi.sub_apply]; ring
  calc ∑ s, (α s - (paritySmoothForm ρ J hΩ k v : FormField n) x s) * c s
      = ∑ s, ∫ t, ρ (x - t) * ((α s - parField J v t s) * c s) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [hR s]
        have e : (fun t => ρ (x - t) * ((α s - parField J v t s) * c s)) =
            fun t => (α s * c s) * ρ (x - t) - c s * (parField J v t s * ρ (x - t)) := by
          funext t; ring
        rw [e, integral_sub (hρ.const_mul _) ((hI s).const_mul _), integral_const_mul,
          integral_const_mul, hρ1]
        ring
    _ = ∫ t, ∑ s, ρ (x - t) * ((α s - parField J v t s) * c s) :=
        (integral_finsetSum _ fun s _ => hterm s).symm
    _ = _ := by simp_rw [Finset.mul_sum]

theorem integrable_comp_sub_mul_parField (hΩ : Ω = Geometry.Q (Fin n)) {k : ℕ}
    (v : L2F ℝ Ω (formIdx n k)) (α c : Finset (Fin n) → ℝ) (x : Fin n → ℝ) :
    Integrable fun t => ρ (x - t) * ∑ s, (α s - parField J v t s) * c s := by
  classical
  have hI : ∀ s, Integrable fun t => parField J v t s * ρ (x - t) := by
    intro s
    unfold parField formExt
    split_ifs with h
    · exact integrable_parExt_mul_comp_sub ρ _ (integrableOn_Q_of_eq hΩ _) x
    · simp
  have hρ := ρ.integrable_comp_sub x
  refine (integrable_finsetSum Finset.univ fun s _ =>
    (hρ.const_mul (α s * c s)).sub ((hI s).const_mul (c s))).congr (ae_of_all _ fun t => ?_)
  simp only [Pi.sub_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

end Integrand


theorem pieceSign_pvec_eq {J s : Finset (Fin n)} {p : Fin n → Fin 3} (hs : ∀ i ∈ s, p i = 1) :
    pieceSign (pvec J s) p = pieceSign (pvec J ∅) p := by
  unfold pieceSign
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : p i = 1
  · simp [pieceSgn, hi]
  · have : i ∉ s := fun h => hi (hs i h)
    simp [pieceSgn, hi, pvec, this]

theorem exists_mem_of_pieceSign_ne_one {J : Finset (Fin n)} {p : Fin n → Fin 3}
    (h : pieceSign (pvec J ∅) p ≠ 1) : ∃ i, p i ≠ 1 ∧ i ∈ J := by
  by_contra hcon
  push Not at hcon
  apply h
  unfold pieceSign
  refine Finset.prod_eq_one fun i _ => ?_
  by_cases hi : p i = 1
  · simp [pieceSgn, hi]
  · simp [pieceSgn, hi, pvec, hcon i hi]

theorem simplexMatrix_row_eq_zero {m : ℕ} {g : Finset (Fin n → ℝ)} (hg : #g = m + 1) {i : Fin n}
    {c : ℝ} (hgc : ∀ v ∈ g, v i = c) : simplexMatrix (lexEnum g m) i = 0 :=
  funext fun l => by simp [simplexMatrix, hgc _ (lexEnum_mem hg _)]

theorem coord_mem_pieceIoo_of_pieceMap {t : Fin n → ℝ} {p : Fin n → Fin 3}
    (ht : pieceMap p t ∈ Geometry.Q (Fin n)) (i : Fin n) : t i ∈ pieceIoo (p i) :=
  (pieceMap_mem_Q_iff p t).1 ht i

/-! ### The closeness estimate on `V_{h,Γ_J}` -/

namespace Poly

variable (S : PolySeq) (J : Finset (Fin n))

open Classical in
/-- **The pointwise estimate of the DOF integrand of `v - Q_N v`** (`v ∈ V_{h,Γ_J}`) for the
parity smoother: at a point `x = F_q(ξ)` of a face `g` of `T` and for any coefficient vector `c`
that only sees the trace on `g`,
`h^{n/2} |Σₛ (v_T - R v)(x)ₛ cₛ| ≤ (Σₛ |cₛ|) A m_T(v)^{1/2} · (2 or γ)`, with the factor `γ`
when all barycentric coordinates of `ξ` are `≥ γ`. A sample `t` of the smoother at `x` is
folded onto `z = fold t ∈ Q` (`‖x - z‖ ≤ ‖x - t‖`), which lies in a simplex `T'` containing
`g`; on the reflected coordinates `g` lies in a face of the cube (`face_coord_eq_zero`,
`face_coord_eq_half`), so the trace on `g` only sees the components unchanged up to a common
sign `σ`; if `σ = -1` the face is normal to `J`, where the traces of `v` vanish. There is no
dilation defect. -/
theorem sqrt_mul_abs_integrand_par {N k : ℕ} {A : ℝ} (hA0 : 0 ≤ A) (hA : InvBound S n k A)
    {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hγ2 : γ ≤ 1 / 2)
    {u : (polyElement n S).Piecewise (mesh n N) k}
    (hu : u ∈ (polyElement n S).globalSpacePartial (mesh n N) (partialFaces n J) k)
    (T : (mesh n N).simplices)
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n)) {m : ℕ}
    (hg : #g = m + 1) {ξ : Fin m → ℝ} (hξ : ξ ∈ FiniteElement.refSimplex m)
    (c : Finset (Fin n) → ℝ)
    (hc : ∀ α β : Finset (Fin n) → ℝ, IsDeg k α → IsDeg k β →
      pullback (simplexMatrix (lexEnum g m)) α = pullback (simplexMatrix (lexEnum g m)) β →
        ∑ s, α s * c s = ∑ s, β s * c s) :
    √(hN N) ^ n * |∑ s, (((u T : (polyElement n S).space T k) : FormField n)
        (simplexMap (lexEnum g m) ξ) s -
      (paritySmoothForm (parKernel n γ hγ hγ1 N) J (mesh_domain_eq_Q N) k
        ((polyElement n S).glue (mesh n N) k u) : FormField n)
        (simplexMap (lexEnum g m) ξ) s) * c s| ≤
      (∑ s, |c s|) * A *
        √(locMass ((polyElement n S).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)) *
        (if ξ ∈ nearBdry m γ then 2 else γ) := by
  classical
  set h := hN N
  have hh : 0 < h := hN_pos N
  set ρ := parKernel n γ hγ hγ1 N
  have hD : (mesh n N).domain = Geometry.Q (Fin n) := mesh_domain_eq_Q N
  set v := (polyElement n S).glue (mesh n N) k u
  set q := lexEnum g m
  set x := simplexMap q ξ
  set uT : FormField n := ((u T : (polyElement n S).space T k) : FormField n)
  have huT : uT ∈ S.space n k := (u T).2
  set L := locMass v (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have hL0 : 0 ≤ L := locMass_nonneg _ _
  set R := (∑ s, |c s|) * A * √L * (if ξ ∈ nearBdry m γ then 2 else γ)
  have hsq : 0 < √h ^ n := pow_pos (Real.sqrt_pos.2 hh) n
  have hxT : x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior :=
    simplexMap_lexEnum_mem hgT hg hξ
  have hxQc : x ∈ closure (Geometry.Q (Fin n)) := by
    rw [← hD]; exact (mesh n N).closedInterior_subset_closure T.2 hxT
  have hxI := coord_mem_Icc_of_mem_closure hxQc
  have hTinv := hA N T.2 uT huT
  have hLT : formL2Sq (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior uT ≤ L :=
    sum_integral_sq_le_locMass (polyElement n S) u T (self_subset_cthickening _ (by positivity))
  have hsqLT : √(formL2Sq (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior uT) ≤ √L :=
    Real.sqrt_le_sqrt hLT
  have hTs : ∀ y ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ∀ s,
      √h ^ n * |uT y s| ≤ A * √L := fun y hy s => by
    have h1 : |uT y s| ≤ ‖uT y‖ := by
      have := norm_le_pi_norm (uT y) s; rwa [Real.norm_eq_abs] at this
    exact (mul_le_mul_of_nonneg_left h1 hsq.le).trans ((hTinv.1 y hy).trans
      (mul_le_mul_of_nonneg_left hsqLT hA0))
  -- the integrand as a mollified average
  rw [sum_sub_paritySmoothForm_mul_eq ρ J hD v (uT x) c x]
  set G : (Fin n → ℝ) → ℝ := fun t => ∑ s, (uT x s - parField J v t s) * c s
  have hρ0 : ∀ t, 0 ≤ ρ (x - t) := fun t => ρ.nonneg _
  have hρi := ρ.integrable_comp_sub x
  have hρ1 := ρ.integral_comp_sub x
  have hρG : Integrable fun t => ρ (x - t) * G t :=
    integrable_comp_sub_mul_parField ρ J hD v (uT x) c x
  -- a.e. sample: the folded point lies in the interior of a simplex
  have hae := ae_glue_eq_local (polyElement n S) u (isOpen_mesh_domain n N).measurableSet
  have hae2 : ∀ᵐ t ∂volume, t ∈ Geometry.Q (Fin n) → ∃ T' : (mesh n N).simplices,
      t ∈ interior (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior ∧
        ∀ s : formIdx n k, (Geometry.Q (Fin n)).indicator
          ((v s : L2 ℝ (mesh n N).domain) : (Fin n → ℝ) → ℝ) t =
          ((u T' : (polyElement n S).space T' k) : FormField n) t s.1 := by
    filter_upwards [hae] with t ht htQ
    obtain ⟨T', h1, h2⟩ := ht (hD ▸ htQ)
    refine ⟨T', h1, fun s => ?_⟩
    set F := ((v s : L2 ℝ (mesh n N).domain) : (Fin n → ℝ) → ℝ)
    have e := congrArg (fun S' : Set (Fin n → ℝ) => S'.indicator F t) hD
    rw [← e]
    exact h2 s
  have hae' := ae_exists_pieceMap hae2
  have hb : ∀ᵐ t ∂volume, ρ (x - t) ≠ 0 → |G t| ≤ R / √h ^ n := by
    filter_upwards [hae'] with t ht hρt
    have hdist : ‖x - t‖ < ρ.radius := by
      by_contra hcon; push Not at hcon
      exact hρt (ρ.eq_zero_of_le _ hcon)
    have htU : t ∈ bigCube n := closedBall_subset_bigCube hxI ρ.radius_lt
      (by rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]; exact hdist.le)
    obtain ⟨p, hpt, T', hzT', hval⟩ := ht htU
    set z := pieceMap p t
    have hzx : ‖x - z‖ < γ * h / 32 := by
      have h1 := norm_sub_le_norm_pieceMap_sub hxI hpt p
      rw [pieceMap_pieceMap] at h1
      rw [norm_sub_rev]
      calc ‖z - x‖ ≤ ‖t - x‖ := h1
        _ = ‖x - t‖ := norm_sub_rev _ _
        _ < ρ.radius := hdist
        _ = γ * h / 32 := parKernel_radius hγ hγ1 N
    rw [le_div_iff₀ hsq, mul_comm]
    set u' : FormField n := ((u T' : (polyElement n S).space T' k) : FormField n)
    have hu' : u' ∈ S.space n k := (u T').2
    set β : Finset (Fin n) → ℝ := fun s => pieceSign (pvec J s) p * u' z s
    have hGt : G t = ∑ s, (uT x s - β s) * c s := by
      refine Finset.sum_congr rfl fun s _ => ?_
      congr 2
      by_cases hs' : (#s : ℤ) = (k : ℤ)
      · simp only [parField, formExt_of_card _ hs', β]
        rw [parExt_eq_of_pieceMap_mem hpt, ← hval ⟨s, hs'⟩, Set.indicator_of_mem hpt]
      · have h0 : parField J v t s = 0 := by simp [parField, formExt, hs']
        rw [h0]
        simp only [β, PolyKind.isDeg_of_mem_space hu' z s (fun h' => hs' (by rw [h'])),
          mul_zero]
    have hzT'c : z ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior := interior_subset hzT'
    have hT'sub : (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior ⊆
        Metric.cthickening (2 * h) (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior := by
      intro y hy
      obtain ⟨m', σ', hmσ'⟩ := mem_mesh_simplices.1 T'.2
      have hdy : ‖y - z‖ ≤ h := by
        rw [← hmσ'] at hy hzT'c; exact norm_sub_le_of_mem_cubeSimplex hy hzT'c
      refine Metric.mem_cthickening_of_dist_le y x _ _ hxT ?_
      rw [dist_eq_norm]
      calc ‖y - x‖ = ‖(y - z) + (z - x)‖ := by congr 1; abel
        _ ≤ ‖y - z‖ + ‖z - x‖ := norm_add_le _ _
        _ ≤ h + γ * h / 32 := by rw [norm_sub_rev z x]; exact add_le_add hdy hzx.le
        _ ≤ 2 * h := by nlinarith
    have hL' : formL2Sq (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior u' ≤ L :=
      sum_integral_sq_le_locMass (polyElement n S) u T' hT'sub
    have hT'inv := hA N T'.2 u' hu'
    have hsqL' : √(formL2Sq (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior u') ≤ √L :=
      Real.sqrt_le_sqrt hL'
    have hT's : ∀ y ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ∀ s,
        √h ^ n * |u' y s| ≤ A * √L := fun y hy s => by
      have h1 : |u' y s| ≤ ‖u' y‖ := by
        have := norm_le_pi_norm (u' y) s; rwa [Real.norm_eq_abs] at this
      exact (mul_le_mul_of_nonneg_left h1 hsq.le).trans ((hT'inv.1 y hy).trans
        (mul_le_mul_of_nonneg_left hsqL' hA0))
    rw [hGt]
    by_cases hbad : ξ ∈ nearBdry m γ
    · -- near the boundary of the face: inverse estimates only
      have hR : R = (∑ s, |c s|) * A * √L * 2 := by simp only [R, hbad, ite_true]
      rw [hR]
      calc √h ^ n * |∑ s, (uT x s - β s) * c s|
          ≤ √h ^ n * ∑ s, (|uT x s| + |u' z s|) * |c s| := by
            refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun s _ => ?_)) hsq.le
            rw [abs_mul]
            refine mul_le_mul_of_nonneg_right ((abs_sub _ _).trans (le_of_eq ?_)) (abs_nonneg _)
            simp only [β, abs_mul, abs_pieceSign (isParity_pvec J s), one_mul]
        _ = ∑ s, (√h ^ n * |uT x s| + √h ^ n * |u' z s|) * |c s| := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => by ring
        _ ≤ ∑ s, (A * √L + A * √L) * |c s| :=
            Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right
              (add_le_add (hTs x hxT s) (hT's z hzT'c s)) (abs_nonneg _)
        _ = (∑ s, |c s|) * A * √L * 2 := by
            rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
            refine Finset.sum_congr rfl fun s _ => by ring
    · -- away from the boundary of the face
      have hR : R = (∑ s, |c s|) * A * √L * γ := by simp only [R, hbad, ite_false]
      rw [hR]
      have hμ : ∀ a, γ ≤ refBary ξ a := by
        intro a; by_contra hlt; push Not at hlt; exact hbad ⟨a, hlt⟩
      have hx : x = ∑ a, refBary ξ a • q a := simplexMap_eq_sum q ξ
      have hgT' : g ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n) :=
        subset_vertexSet_of_near_lex T.2 T'.2 hgT hg hγ hγ2 hμ (sum_refBary ξ) hzT'c
          (by rw [← hx]; nlinarith [norm_nonneg (x - z)])
      have hxT' : x ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior :=
        simplexMap_lexEnum_mem hgT' hg hξ
      -- the reflected coordinates: the face lies in a face of the cube
      have hface : ∀ i, p i ≠ 1 → (∀ w ∈ g, w i = 0) ∨ ∀ w ∈ g, w i = 1 / 2 := by
        intro i hi
        have hti := coord_mem_pieceIoo_of_pieceMap hpt i
        have hxti : |x i - t i| < γ * h / 32 := by
          have := norm_le_pi_norm (x - t) i
          rw [Real.norm_eq_abs, Pi.sub_apply] at this
          have h2 : ρ.radius = γ * h / 32 := parKernel_radius hγ hγ1 N
          linarith
        rw [abs_lt] at hxti
        have hpi : p i = 0 ∨ p i = 2 := by
          rcases (show p i = 0 ∨ p i = 1 ∨ p i = 2 by omega) with h' | h' | h'
          · exact Or.inl h'
          · exact absurd h' hi
          · exact Or.inr h'
        rcases hpi with h' | h'
        · left
          rw [h'] at hti
          simp only [pieceIoo, Set.mem_Ioo] at hti
          exact face_coord_eq_zero T.2 hgT hg hγ hγ2 hμ (by nlinarith [hti.2])
        · right
          rw [h'] at hti
          simp only [pieceIoo, Set.mem_Ioo] at hti
          exact face_coord_eq_half T.2 hgT hg hγ hγ2 hμ (by nlinarith [hti.1])
      set σ := pieceSign (pvec J ∅) p
      have hσ : σ = 1 ∨ σ = -1 := by
        have := abs_pieceSign (isParity_pvec J ∅) p
        rcases abs_eq (zero_le_one) |>.1 this with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
      have hβσ : pullback (simplexMatrix q) β = pullback (simplexMatrix q) (σ • u' z) := by
        refine pullback_congr_of_rows _ fun s => ?_
        by_cases hs : ∀ i ∈ s, p i = 1
        · left
          simp only [β, Pi.smul_apply, smul_eq_mul, pieceSign_pvec_eq hs, σ]
        · right
          push Not at hs
          obtain ⟨i, his, hpi⟩ := hs
          rcases hface i hpi with h' | h'
          · exact ⟨i, his, simplexMatrix_row_eq_zero hg h'⟩
          · exact ⟨i, his, simplexMatrix_row_eq_zero hg h'⟩
      have hdegz := PolyKind.isDeg_of_mem_space hu' z
      have hβdeg : IsDeg k β := fun s hs => by simp only [β, hdegz s hs, mul_zero]
      have hσdeg : IsDeg k (σ • u' z) := fun s hs => by simp [hdegz s hs]
      have hcβ : ∑ s, β s * c s = σ * ∑ s, u' z s * c s := by
        rw [hc _ _ hβdeg hσdeg hβσ, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul]; ring
      -- the difference of the folded sample and the value at `x`, on `T'`
      have hkey : |∑ s, (uT x s - β s) * c s| = |∑ s, (u' x s - u' z s) * c s| := by
        have e1 : ∑ s, (uT x s - β s) * c s = ∑ s, uT x s * c s - ∑ s, β s * c s := by
          rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun s _ => by ring
        have e2 : ∑ s, (u' x s - u' z s) * c s = ∑ s, u' x s * c s - ∑ s, u' z s * c s := by
          rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun s _ => by ring
        rw [e1, e2, hcβ]
        rcases hσ with h1 | h1
        · have htr : ∑ s, uT x s * c s = ∑ s, u' x s * c s :=
            hc _ _ (PolyKind.isDeg_of_mem_space huT x) (PolyKind.isDeg_of_mem_space hu' x)
              (pullback_eq_of_mem_globalSpace hu.1 T T' hgT hgT' hg ξ)
          rw [htr, h1, one_mul]
        · -- `σ = -1`: the face is normal to `J`, where the traces vanish
          obtain ⟨i, hpi, hiJ⟩ := exists_mem_of_pieceSign_ne_one (J := J) (p := p)
            (by rw [show pieceSign (pvec J ∅) p = σ from rfl, h1]; norm_num)
          have hgΓ : ∃ F ∈ partialFaces n J, g ⊆ F := ⟨g, ⟨i, hiJ, hface i hpi⟩, subset_rfl⟩
          have hzero : ∀ (T'' : (mesh n N).simplices),
              g ⊆ vertexSet (T'' : Affine.Simplex ℝ (Fin n → ℝ) n) →
              ∑ s, ((u T'' : (polyElement n S).space T'' k) : FormField n) x s * c s = 0 := by
            intro T'' hgT''
            have hpb := S.pullback_eq_of_dof_eq hgT'' hg (u T'').2 (Submodule.zero_mem _)
              (fun g' hg' j => by
                rw [show (⟨(0 : FormField n), S.space_le_contForms n k (Submodule.zero_mem _)⟩ :
                  contForms n) = 0 from rfl, map_zero]
                obtain ⟨F, hF, hgF⟩ := hgΓ
                exact hu.2 T'' g' (hg'.trans hgT'') ⟨F, hF, hg'.trans hgF⟩ j) ξ
            have h00 := hc _ _ (PolyKind.isDeg_of_mem_space (u T'').2 x) (fun s _ => rfl) hpb
            rw [h00]; simp
          rw [hzero T hgT, hzero T' hgT', h1]
          rw [show (0 : ℝ) - -1 * ∑ s, u' z s * c s = -(0 - ∑ s, u' z s * c s) by ring, abs_neg]
      rw [hkey]
      have hLip : ∀ s, √h ^ n * h * |u' x s - u' z s| ≤ A * ‖x - z‖ * √L := fun s => by
        have h1 : |u' x s - u' z s| ≤ ‖u' x - u' z‖ := by
          have := norm_le_pi_norm (u' x - u' z) s; rwa [Real.norm_eq_abs, Pi.sub_apply] at this
        refine (mul_le_mul_of_nonneg_left h1 (by positivity)).trans ((hT'inv.2 x hxT' z hzT'c).trans
          (mul_le_mul_of_nonneg_left hsqL' (by positivity)))
      calc √h ^ n * |∑ s, (u' x s - u' z s) * c s|
          ≤ √h ^ n * ∑ s, |u' x s - u' z s| * |c s| := by
            refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
              (le_of_eq (Finset.sum_congr rfl fun s _ => abs_mul _ _))) hsq.le
        _ = ∑ s, ((√h ^ n * h * |u' x s - u' z s|) / h) * |c s| := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => by field_simp
        _ ≤ ∑ s, ((A * (γ * h) * √L) / h) * |c s| := by
            refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right
              (div_le_div_of_nonneg_right ((hLip s).trans ?_) hh.le) (abs_nonneg _)
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hA0)
              (Real.sqrt_nonneg _)
            nlinarith
        _ = (∑ s, |c s|) * A * √L * γ := by
            rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
            refine Finset.sum_congr rfl fun s _ => by field_simp
  have hmain := abs_integral_mul_le_of_ae hρ0 hρi hρ1 hρG hb
  rw [le_div_iff₀ hsq, mul_comm] at hmain
  exact hmain


/-- **The DOF error of `Q_N` on `V_{h,Γ_J}`** for the parity smoother: for `v ∈ V_{h,Γ_J}`, a face
`g` of `T` and a degree of freedom `i` of `g`,
`h^{n/2} |ℓ_{g,i}(v_T - R v)| ≤ 3 (n + 1) D A γ hᵏ m_T(v)^{1/2}`. -/
theorem sqrt_mul_abs_dof_err_par {N k : ℕ} {A D : ℝ} (hA0 : 0 ≤ A) (hA : InvBound S n k A)
    (hD : CoeffBound S n k D) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hγ2 : γ ≤ 1 / 2)
    {u : (polyElement n S).Piecewise (mesh n N) k}
    (hu : u ∈ (polyElement n S).globalSpacePartial (mesh n N) (partialFaces n J) k)
    (T : (mesh n N).simplices)
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n))
    (i : S.DofIdx g k) :
    √(hN N) ^ n * |S.dof g k i ⟨((u T : (polyElement n S).space T k) : FormField n),
        S.space_le_contForms n k (u T).2⟩ -
      S.dof g k i (Submodule.inclusion c1Forms_le_contForms
        (paritySmoothForm (parKernel n γ hγ hγ1 N) J (mesh_domain_eq_Q N) k
          ((polyElement n S).glue (mesh n N) k u)))| ≤
      3 * (n + 1) * D * A * γ * hN N ^ k *
        √(locMass ((polyElement n S).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)) := by
  classical
  have hne := i.2
  set m := #g - 1
  have hg : #g = m + 1 := (Nat.succ_pred_eq_of_pos (card_pos.2 hne)).symm
  have hkm : k ≤ m := by have := card_le_of_dofIdx S i; omega
  have hmn : m ≤ n := by
    have := Finset.card_le_card hgT
    rw [card_vertexSet] at this; omega
  set q := lexEnum g m
  set η := (S.testBasis k m i.1 : FormField m)
  set uT : FormField n := ((u T : (polyElement n S).space T k) : FormField n)
  have huT : uT ∈ S.space n k := (u T).2
  set w : c1Forms n := paritySmoothForm (parKernel n γ hγ hγ1 N) J (mesh_domain_eq_Q N) k
    ((polyElement n S).glue (mesh n N) k u)
  set L := locMass ((polyElement n S).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
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
  set Mc := D * hN N ^ k
  have hMc : ∀ ξ ∈ FiniteElement.refSimplex m, ∑ s, |dofCoeff q η k ξ s| ≤ Mc :=
    fun ξ hξ => hD N T.2 hgT i ξ hξ
  have hMc0 : 0 ≤ Mc := by
    have h0 : (0 : Fin m → ℝ) ∈ FiniteElement.refSimplex m := fun a => by
      refine Fin.cases ?_ (fun l => ?_) a
      · simp
      · simp [refBary]
    exact (Finset.sum_nonneg fun s _ => abs_nonneg _).trans (hMc 0 h0)
  set c := Mc * A * √L
  have hc0 : 0 ≤ c := by positivity
  rw [herr]
  refine (mul_abs_integral_refSimplex_le hFc (pow_nonneg (Real.sqrt_nonneg _) n)
    (by positivity : 0 ≤ 2 * c) (by positivity : 0 ≤ γ / 2) hγ.le hγ1 fun ξ hξ =>
      (sqrt_mul_abs_integrand_par S J hA0 hA hγ hγ1 hγ2 hu T hgT hg hξ (dofCoeff q η k ξ)
        (fun α β hα hβ hαβ => sum_mul_dofCoeff_eq_of_pullback_eq q η ξ hα hβ hαβ)).trans
      ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (hMc ξ hξ) hA0) (Real.sqrt_nonneg _)) (by split_ifs <;> positivity)).trans
        (le_of_eq (by split_ifs <;> ring)))).trans ?_
  have hm' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  calc 2 * c * (γ / 2 + (m + 1) * γ) ≤ c * (3 * (n + 1) * γ) := by
        nlinarith [mul_le_mul_of_nonneg_left hm' (mul_nonneg hc0 hγ.le),
          mul_nonneg (mul_nonneg hc0 hγ.le) (Nat.cast_nonneg (α := ℝ) n)]
    _ = _ := by simp only [c, Mc]; ring

/-- **The local `L²` error of `Q_N` on `V_{h,Γ_J}`** for the parity smoother:
`‖v - Q_N v‖²_{L²(T)} ≲ γ² m_T(v)`. -/
theorem sum_integral_sq_sub_interp_par {N k : ℕ} {A B D : ℝ} (hA0 : 0 ≤ A)
    (hA : InvBound S n k A) (hB0 : 0 ≤ B) (hB : DofBound S n k B) (hD0 : 0 ≤ D)
    (hD : CoeffBound S n k D) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hγ2 : γ ≤ 1 / 2)
    {u : (polyElement n S).Piecewise (mesh n N) k}
    (hu : u ∈ (polyElement n S).globalSpacePartial (mesh n N) (partialFaces n J) k)
    (T : (mesh n N).simplices) :
    ∑ s : formIdx n k, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      ((((u T : (polyElement n S).space T k) : FormField n) -
        ((((polyElement n S).globalInterp (mesh n N) k
          (Submodule.inclusion c1Forms_le_contForms
            (paritySmoothForm (parKernel n γ hγ hγ1 N) J (mesh_domain_eq_Q N) k
              ((polyElement n S).glue (mesh n N) k u))) :
            (polyElement n S).Piecewise (mesh n N) k) T : (polyElement n S).space T k) :
              FormField n)) y s.1) ^ 2 ≤
      2 ^ n * (B * Module.finrank ℝ (S.space n k) * (3 * (n + 1) * D * A) * γ) ^ 2 *
        locMass ((polyElement n S).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n) := by
  set h := hN N
  have hh : 0 < h := hN_pos N
  set w := paritySmoothForm (parKernel n γ hγ hγ1 N) J (mesh_domain_eq_Q N) k
    ((polyElement n S).glue (mesh n N) k u)
  set Pw : (polyElement n S).space T k := (((polyElement n S).globalInterp (mesh n N) k
    (Submodule.inclusion c1Forms_le_contForms w) : (polyElement n S).Piecewise (mesh n N) k) T)
  set uT : FormField n := ((u T : (polyElement n S).space T k) : FormField n)
  have huT : uT ∈ S.space n k := (u T).2
  have hPw : (Pw : FormField n) ∈ S.space n k := Pw.2
  set z : FormField n := uT - (Pw : FormField n)
  have hz : z ∈ S.space n k := Submodule.sub_mem _ huT hPw
  set L := locMass ((polyElement n S).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have hL0 : 0 ≤ L := locMass_nonneg _ _
  set C₁ := 3 * (n + 1) * D * A
  have hC₁ : 0 ≤ C₁ := by positivity
  have hsq : 0 < √h ^ n := pow_pos (Real.sqrt_pos.2 hh) n
  set D' := C₁ * γ * √L / √h ^ n
  have hD'0 : 0 ≤ D' := by positivity
  have hdof : ∀ g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n), ∀ i : S.DofIdx g k,
      |S.dof g k i ⟨z, S.space_le_contForms n k hz⟩| ≤ h ^ k * D' := by
    intro g hgT i
    have e1 : S.dof g k i ⟨(Pw : FormField n), S.space_le_contForms n k hPw⟩ =
        S.dof g k i (Submodule.inclusion c1Forms_le_contForms w) :=
      (polyElement n S).localDof_globalInterp (mesh n N) k
        (Submodule.inclusion c1Forms_le_contForms w) T g hgT i
    have e : S.dof g k i ⟨z, S.space_le_contForms n k hz⟩ =
        S.dof g k i ⟨uT, S.space_le_contForms n k huT⟩ -
          S.dof g k i (Submodule.inclusion c1Forms_le_contForms w) := by
      rw [← e1, ← map_sub]; rfl
    rw [e]
    have h1 := sqrt_mul_abs_dof_err_par S J hA0 hA hD hγ hγ1 hγ2 hu T hgT i
    have e2 : h ^ k * D' = C₁ * γ * h ^ k * √L / √h ^ n := by
      simp only [D']; ring
    rw [e2, le_div_iff₀ hsq, mul_comm]
    calc √h ^ n * |S.dof g k i ⟨uT, S.space_le_contForms n k huT⟩ -
          S.dof g k i (Submodule.inclusion c1Forms_le_contForms w)|
        ≤ 3 * (n + 1) * D * A * γ * hN N ^ k * √L := h1
      _ = C₁ * γ * h ^ k * √L := by simp only [C₁, h]
  have hzb : ∀ y ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ∀ s,
      |z y s| ≤ B * Module.finrank ℝ (S.space n k) * D' :=
    fun y hy s => abs_le_of_abs_dof_le S hB hB0 T.2 hz hdof hy s
  set P := (Module.finrank ℝ (S.space n k) : ℝ)
  have hhn : h ^ n = (√h ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hh.le]
  calc ∑ s : formIdx n k, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
        (z y s.1) ^ 2
      ≤ 2 ^ n * (h ^ n * (B * P * D') ^ 2) :=
        sum_integral_sq_le_of_abs_le T.2 (PolyKind.contDiff_of_mem_space hz).continuous hzb
    _ = 2 ^ n * (B * P * C₁ * γ) ^ 2 * (√L) ^ 2 := by
        rw [hhn]; simp only [D']; field_simp
    _ = 2 ^ n * (B * P * C₁ * γ) ^ 2 * L := by rw [Real.sq_sqrt hL0]

/-- **`Q_N` is close to the identity on `V_{h,Γ_J}`** for the parity smoother:
`‖v - Q_N v‖² ≤ 2ⁿ (B dim(P) C₁ γ)² 6ⁿ n! ‖v‖²`, `C₁ = 3 (n + 1) D A`. -/
theorem norm_sq_sub_paritySmoothedInterp_le {N k : ℕ} {A B D : ℝ} (hA0 : 0 ≤ A)
    (hA : InvBound S n k A) (hB0 : 0 ≤ B) (hB : DofBound S n k B) (hD0 : 0 ≤ D)
    (hD : CoeffBound S n k D) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hγ2 : γ ≤ 1 / 2)
    {u : (polyElement n S).Piecewise (mesh n N) k}
    (hu : u ∈ (polyElement n S).globalSpacePartial (mesh n N) (partialFaces n J) k) :
    ‖(polyElement n S).glue (mesh n N) k u - (polyElement n S).paritySmoothedInterp (mesh n N)
        (parKernel n γ hγ hγ1 N) J (mesh_domain_eq_Q N) k
        ((polyElement n S).glue (mesh n N) k u)‖ ^ 2 ≤
      2 ^ n * (B * Module.finrank ℝ (S.space n k) * (3 * (n + 1) * D * A) * γ) ^ 2 *
        ((6 ^ n * n.factorial : ℕ) * ‖(polyElement n S).glue (mesh n N) k u‖ ^ 2) := by
  set v := (polyElement n S).glue (mesh n N) k u
  have hQ := (polyElement n S).paritySmoothedInterp_natCast (mesh n N) (parKernel n γ hγ hγ1 N)
    J (mesh_domain_eq_Q N) k v
  set Pw := (polyElement n S).globalInterp (mesh n N) k (Submodule.inclusion c1Forms_le_contForms
    (paritySmoothForm (parKernel n γ hγ hγ1 N) J (mesh_domain_eq_Q N) k v))
  set d : (polyElement n S).Piecewise (mesh n N) k :=
    u - (Pw : (polyElement n S).Piecewise (mesh n N) k)
  have hsub : v - (polyElement n S).paritySmoothedInterp (mesh n N) (parKernel n γ hγ hγ1 N) J
      (mesh_domain_eq_Q N) k v = (polyElement n S).glue (mesh n N) k d := by
    rw [hQ, map_sub]
  rw [hsub]
  exact norm_sq_glue_le_locMass _ v d (by positivity)
    fun T hT => sum_integral_sq_sub_interp_par S J hA0 hA hB0 hB hD0 hD hγ hγ1 hγ2 hu ⟨T, hT⟩

variable (n) in
/-- **The parity smoothing scale, for all small `γ`**: there is `γ₀ ∈ (0, ½]`, depending only on
`n` and the sequence `S`, such that for every `γ ∈ (0, γ₀]`, every class `J` and every global
field of `Λ_{h,Γ_J}`, `‖v - Q_N v‖ ≤ ½ ‖v‖`. -/
theorem exists_gamma₀_par :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 / 2 ∧ ∀ γ : ℝ, ∀ (hγ : 0 < γ) (hγ1 : γ ≤ 1), γ ≤ γ₀ →
      ∀ (J : Finset (Fin n)) (N k : ℕ) (u : (polyElement n S).Piecewise (mesh n N) k),
      u ∈ (polyElement n S).globalSpacePartial (mesh n N) (partialFaces n J) k →
        ‖(polyElement n S).glue (mesh n N) k u - (polyElement n S).paritySmoothedInterp
          (mesh n N) (parKernel n γ hγ hγ1 N) J (mesh_domain_eq_Q N) k
          ((polyElement n S).glue (mesh n N) k u)‖ ≤
          1 / 2 * ‖(polyElement n S).glue (mesh n N) k u‖ := by
  classical
  choose A hA0 hA using fun k : ℕ => exists_invBound (n := n) S k
  choose B hB0 hB using fun k : ℕ => exists_dofBound (n := n) S k
  choose D hD0 hD using fun k : ℕ => exists_coeffBound (n := n) S k
  set x : ℕ → ℝ := fun k => B k * Module.finrank ℝ (S.space n k) * (3 * (n + 1) * D k * A k)
  have hx0 : ∀ k, 0 ≤ x k := fun k => by
    have := hA0 k; have := hB0 k; have := hD0 k; positivity
  set Sx := ∑ k ∈ Finset.range (n + 1), x k
  have hS : 0 ≤ Sx := Finset.sum_nonneg fun k _ => hx0 k
  set K : ℝ := 2 ^ n * ((6 ^ n * n.factorial : ℕ) : ℝ)
  have hK : 1 ≤ K := one_le_cov
  set γ₀ := 1 / (2 * (1 + Sx * K))
  have hpos : 0 < 1 + Sx * K := by nlinarith
  have hγ₀ : 0 < γ₀ := by positivity
  have hγ₀2 : γ₀ ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  refine ⟨γ₀, hγ₀, hγ₀2, fun γ hγ hγ1 hγγ₀ J N k u hu => ?_⟩
  have hγ2 : γ ≤ 1 / 2 := hγγ₀.trans hγ₀2
  by_cases hk : n < k
  · have := subsingleton_L2F_of_lt (Ω := (mesh n N).domain) hk
    rw [Subsingleton.elim ((polyElement n S).glue (mesh n N) k u) 0]; simp
  push Not at hk
  have hxk : x k ≤ Sx := Finset.single_le_sum (fun k _ => hx0 k) (Finset.mem_range.2 (by omega))
  have h := norm_sq_sub_paritySmoothedInterp_le S J (hA0 k) (hA k) (hB0 k) (hB k) (hD0 k)
    (hD k) hγ hγ1 hγ2 hu
  have hq := sq_le_quarter_of_le hS hK (hx0 k) hxk hγ.le hγγ₀
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) (h.trans ?_)
  calc 2 ^ n * (B k * Module.finrank ℝ (S.space n k) * (3 * (n + 1) * D k * A k) * γ) ^ 2 *
        (((6 ^ n * n.factorial : ℕ) : ℝ) * ‖(polyElement n S).glue (mesh n N) k u‖ ^ 2)
      = K * (x k * γ) ^ 2 * ‖(polyElement n S).glue (mesh n N) k u‖ ^ 2 := by
        simp only [K, x]; ring
    _ ≤ 1 / 4 * ‖(polyElement n S).glue (mesh n N) k u‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hq (sq_nonneg _)
    _ = (1 / 2 * ‖(polyElement n S).glue (mesh n N) k u‖) ^ 2 := by ring

end Poly


/-! ### The parity smoothing estimates on the cube -/

/-- A commuting map into a subcomplex of `HΛ_J(Ω)`, transported along `Ω = Ω'`. -/
def commutingMapOfEqPart {Ω Ω' : Set (Fin n → ℝ)} (h : Ω = Ω') (hΩ : IsOpen Ω)
    (hΩQ : Ω ⊆ Geometry.Q (Fin n)) (hΩ' : IsOpen Ω') (hΩQ' : Ω' ⊆ Geometry.Q (Fin n))
    (J : Finset (Fin n)) {S : (HQpartZ hΩ hΩQ J).Subcomplex} (Q : S.CommutingMap) :
    (partialSubcomplexOfEq h hΩ hΩQ hΩ' hΩQ' J S).CommutingMap := by
  subst h; exact Q

/-- Estimates of a commuting map transport along an equality of domains. -/
theorem commutingMapOfEqPart_estimates {Ω Ω' : Set (Fin n → ℝ)} (h : Ω = Ω') (hΩ : IsOpen Ω)
    (hΩQ : Ω ⊆ Geometry.Q (Fin n)) (hΩ' : IsOpen Ω') (hΩQ' : Ω' ⊆ Geometry.Q (Fin n))
    (J : Finset (Fin n)) {S : (HQpartZ hΩ hΩQ J).Subcomplex} (Q : S.CommutingMap)
    {C θ : ℝ} (hb : ∀ i x, ‖Q.Q i x‖ ≤ C * ‖x‖)
    (hc : ∀ i, ∀ v ∈ S.V i, ‖v - Q.Q i v‖ ≤ θ * ‖v‖) :
    (∀ i x, ‖(commutingMapOfEqPart h hΩ hΩQ hΩ' hΩQ' J Q).Q i x‖ ≤ C * ‖x‖) ∧
    (∀ i, ∀ v ∈ (partialSubcomplexOfEq h hΩ hΩQ hΩ' hΩQ' J S).V i,
      ‖v - (commutingMapOfEqPart h hΩ hΩQ hΩ' hΩQ' J Q).Q i v‖ ≤ θ * ‖v‖) := by
  subst h; exact ⟨hb, hc⟩

variable [NeZero n]

variable (n) in
/-- **The parity-smoothed interpolant** `Q_N = Π_h R^J` of the complex `polyPartial n S N J`, as a
commuting map. -/
def paritySmoothed (S : PolySeq) (N : ℕ) (J : Finset (Fin n)) (ρ : ReflKernel n) :
    (polyPartial n S N J).CommutingMap :=
  commutingMapOfEqPart (mesh_domain n N) _ _ (isOpen_cubeDomain n) (cubeDomain_subset_Q n) J
    ((polyElement n S).paritySmoothedCommutingMap (mesh n N) ρ J (mesh_domain_eq_Q N))

variable (n) in
/-- **The parity smoothing estimates** ([AFW2010], §5.5; [ChristiansenWinther2008]) for the class
`J` and the admissible sequence `S`: for the kernels `ρ N`, the parity-smoothed interpolants
`Q_N = Π_h R^J_{ρ N}` of `V_{h,Γ_J} = polyPartial n S N J` are bounded in `L²` uniformly in `N`, and
`‖v - Q_N v‖ ≤ ½ ‖v‖` on `V_{h,Γ_J}`. -/
structure ParitySmoothingEstimates (J : Finset (Fin n)) (S : PolySeq) (ρ : ℕ → ReflKernel n)
    (C : ℝ) : Prop where
  half_le : 1 / 2 ≤ C
  bound : ∀ N i x, ‖(paritySmoothed n S N J (ρ N)).Q i x‖ ≤ C * ‖x‖
  close : ∀ N i, ∀ v ∈ (polyPartial n S N J).V i,
    ‖v - (paritySmoothed n S N J (ρ N)).Q i v‖ ≤ 1 / 2 * ‖v‖

/-- **The parity smoothing estimates hold on the Freudenthal meshes of the cube, for every class
`J` and every admissible sequence `S`**: for every `γ ∈ (0, γ₀]` (`γ₀` depending only on `n`
and `S`) and the product kernels of radius `γ h_N / 32` (`parKernel`). -/
theorem paritySmoothingEstimates_parKernel (S : PolySeq) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 / 2 ∧ ∀ (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1), γ ≤ γ₀ →
      ∀ J : Finset (Fin n), ∃ C, ParitySmoothingEstimates n J S (parKernel n γ hγ hγ1) C := by
  obtain ⟨γ₀, hγ₀, hγ₀2, hclose⟩ := Poly.exists_gamma₀_par n S
  refine ⟨γ₀, hγ₀, hγ₀2, fun γ hγ hγ1 hγγ₀ J => ?_⟩
  obtain ⟨C, hC0, hbound⟩ := exists_norm_paritySmoothedInterp_le S J hγ hγ1
  refine ⟨max C (1 / 2), ?_⟩
  have hest : ∀ N, (∀ i x, ‖(paritySmoothed n S N J (parKernel n γ hγ hγ1 N)).Q i x‖ ≤
      max C (1 / 2) * ‖x‖) ∧ (∀ i, ∀ v ∈ (polyPartial n S N J).V i,
        ‖v - (paritySmoothed n S N J (parKernel n γ hγ hγ1 N)).Q i v‖ ≤ 1 / 2 * ‖v‖) := by
    intro N
    refine commutingMapOfEqPart_estimates (mesh_domain n N) _ _ (isOpen_cubeDomain n)
      (cubeDomain_subset_Q n) J _ (fun i x => ?_) (fun i v hv => ?_)
    · change ‖(polyElement n S).paritySmoothedInterp (mesh n N) (parKernel n γ hγ hγ1 N) J
        (mesh_domain_eq_Q N) i x‖ ≤ _
      rcases i with k | k
      · exact (hbound N k x).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
    · change ‖v - (polyElement n S).paritySmoothedInterp (mesh n N) (parKernel n γ hγ hγ1 N) J
        (mesh_domain_eq_Q N) i v‖ ≤ _
      rcases i with k | k
      · obtain ⟨u, rfl⟩ := hv
        exact hclose γ hγ hγ1 hγγ₀ J N k u.1 u.2
      · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
  exact ⟨le_max_right _ _, fun N => (hest N).1, fun N => (hest N).2⟩

/-- **The parity smoothing estimates hold** for every class `J` and every admissible sequence `S`,
as a bare existence statement over the kernels. -/
theorem paritySmoothing_exists (J : Finset (Fin n)) (S : PolySeq) :
    ∃ (ρ : ℕ → ReflKernel n) (C : ℝ), ParitySmoothingEstimates n J S ρ C := by
  obtain ⟨γ₀, hγ₀, hγ₀2, h⟩ := paritySmoothingEstimates_parKernel (n := n) S
  obtain ⟨C, hC⟩ := h γ₀ hγ₀ (by linarith) le_rfl J
  exact ⟨_, C, hC⟩

namespace ParitySmoothingEstimates

variable {J : Finset (Fin n)} {S : PolySeq} {ρ : ℕ → ReflKernel n} {C : ℝ}

/-- **The smoothed projection** `π_N = J_N⁻¹ Q_N` onto `V_{h,Γ_J}`. -/
def proj (hE : ParitySmoothingEstimates n J S ρ C) (N : ℕ) :
    (polyPartial n S N J).CochainProjection :=
  (paritySmoothed n S N J (ρ N)).toCochainProjection (θ := 1 / 2) (by norm_num) (hE.close N)

theorem two_mul_nonneg (hE : ParitySmoothingEstimates n J S ρ C) : 0 ≤ 2 * C := by
  linarith [hE.half_le]

variable (hE : ParitySmoothingEstimates n J S ρ C)
include hE

/-- **Uniform `L²` bound**: `‖π_N x‖ ≤ 2 C ‖x‖` for every `N`. -/
theorem norm_proj_le (N : ℕ) (i : ℤ) (x : L2F ℝ (cubeDomain n) (formIdx n i)) :
    ‖(hE.proj N).π i x‖ ≤ 2 * C * ‖x‖ :=
  (paritySmoothed n S N J (ρ N)).norm_toCochainProjection_le_two_mul (hE.close N)
    (hE.bound N i) x

/-- **Uniform discrete Poincaré inequality** on `V_{h,Γ_J}`: `‖x‖ ≤ 2 C (2π)⁻¹ ‖d_J x‖` for
`x ∈ V_{h,Γ_J}ⁱ ⊥ 𝔷ₕⁱ` ([AFW2010], Thm 3.6, with the Poincaré inequality of `HΛ_J(Q)`). -/
theorem norm_le_of_forall_inner_eq_zero {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (N : ℕ)
    {x : L2F ℝ (cubeDomain n) (formIdx n i)} (hx : x ∈ (polyPartial n S N J).V i)
    (hxo : ∀ y ∈ (polyPartial n S N J).cyclesW i, inner ℝ y x = 0) :
    ‖x‖ ≤ 2 * C * (2 * Real.pi)⁻¹ *
      ‖(complexPart n J).d i j ⟨x, (polyPartial n S N J).le_domain i j hx⟩‖ :=
  (hE.proj N).norm_le_of_forall_inner_eq_zero hij
    (norm_le_of_mem_orthogonal_cycles_part J hij) hE.two_mul_nonneg (hE.norm_proj_le N i) hx hxo

end ParitySmoothingEstimates

/-- **Uniformly bounded cochain projections onto `V_{h,Γ_J}`** (unconditionally, every class `J`,
every admissible sequence): one constant bounds all of them in `L²` and in the graph norms of
`HΛ_J(Q)`. -/
theorem exists_uniform_cochainProjection_part (S : PolySeq) (J : Finset (Fin n)) :
    ∃ C : ℝ, ∀ N, ∃ π : (polyPartial n S N J).CochainProjection,
      (∀ i x, ‖π.π i x‖ ≤ C * ‖x‖) ∧ ∀ i j, π.IsGraphBounded i j C := by
  obtain ⟨ρ, C, hE⟩ := paritySmoothing_exists J S
  exact ⟨2 * C, fun N => ⟨hE.proj N, hE.norm_proj_le N, fun i j =>
    (hE.proj N).isGraphBounded_of_norm_le (hE.norm_proj_le N i) (hE.norm_proj_le N j)⟩⟩

/-! ### The homogeneous classes `J = ∅` and `J = univ` -/


/-! ### The `H¹` approximation of the parity-smoothed projections -/

section H1

omit [NeZero n] in
/-- The scalar `H¹` estimate on a domain equal to `Q`: if `w` represents `ρ ⋆ ext_{c(J', ∅)} f`
on `Θ = Q`, then `‖f - w‖ ≤ r √(n 3ⁿ) ‖∇f‖`. -/
theorem norm_sub_le_grad_of_eq_Q (ρ : ReflKernel n) (J' : Finset (Fin n)) {Θ : Set (Fin n → ℝ)}
    (hΘ : Θ = Geometry.Q (Fin n)) (f : L2 ℝ Θ)
    (hf : zeroForm f ∈ (dPart Θ J' ((0 : ℕ) : ℤ)).domain) (w : L2 ℝ Θ)
    (hw : (w : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict Θ]
      smoothFun ρ (pvec J' ∅) (f : (Fin n → ℝ) → ℝ)) :
    ‖f - w‖ ≤ ρ.radius * √(n * 3 ^ n) * ‖dPart Θ J' ((0 : ℕ) : ℤ) ⟨zeroForm f, hf⟩‖ := by
  subst hΘ
  have hw' : w = scalarSmooth ρ (pvec J' ∅) (isParity_pvec J' ∅) f :=
    Lp.ext (hw.trans (coeFn_scalarSmooth ρ _ _ f).symm)
  rw [hw']
  exact norm_sub_scalarSmooth_le_grad ρ J' ⟨zeroForm f, hf⟩

omit [NeZero n] in
/-- **The parity smoother commutes with the gradient of the coefficients** at the points of
`cl Ω`: `∂ⱼ (ρ ⋆ ext_{c(J,s)} yₛ) = ρ ⋆ ext_{c(J ∆ s, {j})} (∂ⱼ yₛ)` for `yₛ ∈ H¹_{J ∆ s}`
(`extDeriv_paritySmoothForm` for the `0`-form `yₛ` in the class `J ∆ s`). -/
theorem partialDeriv_parCoeff_eq (ρ : ReflKernel n) (J : Finset (Fin n)) {Ω : Set (Fin n → ℝ)}
    (hΩ : Ω = Geometry.Q (Fin n)) {k : ℤ} (y : L2F ℝ Ω (formIdx n k)) (s : formIdx n k)
    (hy : zeroForm (y s) ∈ (dPart Ω (symmDiff J s.1) ((0 : ℕ) : ℤ)).domain)
    {x : Fin n → ℝ} (hx : x ∈ closure Ω) (j : Fin n) :
    partialDeriv j (parCoeff ρ J y s) x =
      (paritySmoothForm ρ (symmDiff J s.1) hΩ (((0 : ℕ) : ℤ) + 1)
        (dPart Ω (symmDiff J s.1) ((0 : ℕ) : ℤ) ⟨zeroForm (y s), hy⟩) : FormField n) x {j} := by
  have h := extDeriv_paritySmoothForm ρ (symmDiff J s.1) hΩ 0 ⟨zeroForm (y s), hy⟩ hx
  have h2 := congrFun h {j}
  rw [extDeriv_apply_singleton] at h2
  rw [← h2]
  congr 1
  funext z
  change parCoeff ρ J y s z = formExt (parCoeff ρ (symmDiff J s.1) (zeroForm (y s))) ∅ z
  rw [formExt_of_card _ (by simp)]
  simp only [parCoeff, zeroForm_apply]
  rw [pvec_symmDiff_empty]

namespace Poly

variable (S : PolySeq)

omit [NeZero n] in
/-- **The interpolation error of the parity-smoothed field in terms of a gradient**: if the
partial derivatives of the smoothed coefficients are the parity-smoothed fields (of classes
`Jg s`) of `L²` `1`-forms `g s`, then `‖R y - Π_h R y‖² ≲ h_N² Σₛ ‖g s‖²` (the pointwise
interpolation error `h_N sup_T ‖D (R y)‖`, the local-mass bound of the smoothed field, bounded
overlap). -/
theorem sq_norm_formL2_sub_paritySmoothedInterp_le {N k : ℕ} {B D : ℝ} (hB : DofBound S n k B)
    (hB0 : 0 ≤ B) (hD : CoeffBound S n k D) (hD0 : 0 ≤ D) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (J : Finset (Fin n)) (y : L2F ℝ (mesh n N).domain (formIdx n k))
    (Jg : formIdx n k → Finset (Fin n))
    (g : formIdx n k → L2F ℝ (mesh n N).domain (formIdx n (((0 : ℕ) : ℤ) + 1)))
    (hcomm : ∀ s : formIdx n k, ∀ x ∈ closure (mesh n N).domain, ∀ j : Fin n,
      partialDeriv j (parCoeff (parKernel n γ hγ hγ1 N) J y s) x =
        (paritySmoothForm (parKernel n γ hγ hγ1 N) (Jg s) (mesh_domain_eq_Q N)
          (((0 : ℕ) : ℤ) + 1) (g s) : FormField n) x {j}) :
    ‖formL2 (isOpen_mesh_domain n N).measurableSet (mesh n N).isBounded_domain k
        (Submodule.inclusion c1Forms_le_contForms
          (paritySmoothForm (parKernel n γ hγ hγ1 N) J (mesh_domain_eq_Q N) k y)) -
      (polyElement n S).paritySmoothedInterp (mesh n N) (parKernel n γ hγ hγ1 N) J
        (mesh_domain_eq_Q N) k y‖ ^ 2
      ≤ 2 ^ n * (1 + B * Module.finrank ℝ (S.space n k) * D) ^ 2 * n ^ 2 * 2 ^ n * 3 ^ n *
        (32 / γ) ^ n * ((6 ^ n * n.factorial : ℕ) : ℝ) * hN N ^ 2 * ∑ s, ‖g s‖ ^ 2 := by
  classical
  set h := hN N
  have hh : 0 < h := hN_pos N
  set ρ := parKernel n γ hγ hγ1 N
  set F : c1Forms n := paritySmoothForm ρ J (mesh_domain_eq_Q N) k y
  have hFc1 : ContDiff ℝ 1 (F : FormField n) := mem_c1Forms.1 F.2
  set u := (polyElement n S).globalInterp (mesh n N) k (Submodule.inclusion c1Forms_le_contForms F)
  have hQ := (polyElement n S).paritySmoothedInterp_natCast (mesh n N) ρ J (mesh_domain_eq_Q N) k y
  set Mρ : ℝ := (32 / (γ * h)) ^ n
  have hMρ0 : 0 ≤ Mρ := by positivity
  set P := (Module.finrank ℝ (S.space n k) : ℝ)
  set Ci := 1 + B * P * D
  have hCi : 0 ≤ Ci := by positivity
  set L : formIdx n k → Affine.Simplex ℝ (Fin n → ℝ) n → ℝ := fun s T => locMass (g s) T
  have hL0 : ∀ s T, 0 ≤ L s T := fun s T => locMass_nonneg _ _
  -- the derivative bound on a simplex
  have hder : ∀ T ∈ (mesh n N).simplices, ∀ x ∈ T.closedInterior,
      ‖iteratedFDeriv ℝ (0 + 1) (F : FormField n) x‖ ≤
        n * ∑ s, √(3 ^ n * Mρ * L s T) := by
    intro T hT x hx
    have hxc : x ∈ closure (mesh n N).domain := (mesh n N).closedInterior_subset_closure hT hx
    rw [zero_add, norm_iteratedFDeriv_one]
    refine (norm_fderiv_le_sum_partialDeriv ((hFc1.differentiable one_ne_zero) x)).trans ?_
    have hterm : ∀ j : Fin n, ∀ s : formIdx n k,
        |partialDeriv j (fun z => (F : FormField n) z s.1) x| ≤ √(3 ^ n * Mρ * L s T) := by
      intro j s
      have hF : (fun z => (F : FormField n) z s.1) = parCoeff ρ J y s := by
        funext z
        change formExt (parCoeff ρ J y) s.1 z = _
        rw [formExt_val]
      rw [hF, hcomm s x hxc j]
      exact abs_paritySmoothForm_le (Jg s) hγ hγ1 (g s) hT hx {j}
    calc ∑ j, ∑ t, |partialDeriv j (fun z => (F : FormField n) z t) x|
        = ∑ j, ∑ s : formIdx n k, |partialDeriv j (fun z => (F : FormField n) z s.1) x| := by
          refine Finset.sum_congr rfl fun j _ => sum_eq_sum_formIdx fun t ht => ?_
          have : (fun z => (F : FormField n) z t) = fun _ => 0 := by
            funext z; exact isDeg_paritySmoothForm ρ J (mesh_domain_eq_Q N) k y z t ht
          rw [this]; simp [partialDeriv]
      _ ≤ ∑ _j : Fin n, ∑ s : formIdx n k, √(3 ^ n * Mρ * L s T) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun s _ => hterm j s
      _ = n * ∑ s, √(3 ^ n * Mρ * L s T) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the local `L²` error on a simplex
  have hloc : ∀ T ∈ (mesh n N).simplices, ∑ s : formIdx n k, ∫ x in T.closedInterior,
      ((F : FormField n) x s.1 - (polyElement n S).extendPW (mesh n N)
        (u : (polyElement n S).Piecewise (mesh n N) k) T x s.1) ^ 2 ≤
      2 ^ n * Ci ^ 2 * n ^ 2 * 2 ^ n * 3 ^ n * (32 / γ) ^ n * h ^ 2 * ∑ s, L s T := by
    intro T hT
    set MT := n * ∑ s, √(3 ^ n * Mρ * L s T)
    have hMT0 : 0 ≤ MT := by positivity
    have hpt : ∀ x ∈ T.closedInterior, ∀ t : Finset (Fin n),
        |(F : FormField n) x t - (polyElement n S).extendPW (mesh n N)
          (u : (polyElement n S).Piecewise (mesh n N) k) T x t| ≤ Ci * (h ^ (0 + 1) * MT) := by
      intro x hx t
      rw [(polyElement n S).extendPW_of_mem (mesh n N) _ hT]
      exact abs_sub_globalInterp_le S (polySpace_zero_le_space S k) hB hB0 hD ⟨T, hT⟩
        (s := 0) (hFc1.of_le le_rfl) (isDeg_paritySmoothForm ρ J (mesh_domain_eq_Q N) k y)
        (hder T hT) hx t
    obtain ⟨m, σ, hmσ⟩ := mem_mesh_simplices.1 hT
    have hcont : ∀ s : formIdx n k, Continuous fun x => ((F : FormField n) x s.1 -
        (polyElement n S).extendPW (mesh n N) (u : (polyElement n S).Piecewise (mesh n N) k)
          T x s.1) ^ 2 :=
      fun s => (((continuous_apply s.1).comp hFc1.continuous).sub ((continuous_apply s.1).comp
        ((polyElement n S).contDiff_extendPW (mesh n N) _ hT).continuous)).pow 2
    have hs1 : ∀ s : formIdx n k, ∫ x in T.closedInterior, ((F : FormField n) x s.1 -
        (polyElement n S).extendPW (mesh n N) (u : (polyElement n S).Piecewise (mesh n N) k)
          T x s.1) ^ 2 ≤ h ^ n * (Ci * (h ^ (0 + 1) * MT)) ^ 2 := by
      intro s
      have := integral_cubeSimplex_le m σ (hcont s) (fun x hx => by
        rw [hmσ] at hx
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hpt x hx s.1) 2) (fun x => sq_nonneg _)
      rwa [hmσ] at this
    have hCS : (∑ s : formIdx n k, √(3 ^ n * Mρ * L s T)) ^ 2 ≤
        2 ^ n * ∑ s, 3 ^ n * Mρ * L s T := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (formIdx n k)))
        (f := fun s => √(3 ^ n * Mρ * L s T))
      refine this.trans ?_
      rw [Finset.card_univ]
      refine mul_le_mul (card_formIdx_le _) (le_of_eq (Finset.sum_congr rfl fun s _ => ?_))
        (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      exact Real.sq_sqrt (by have := hL0 s T; positivity)
    calc ∑ s : formIdx n k, ∫ x in T.closedInterior, ((F : FormField n) x s.1 -
          (polyElement n S).extendPW (mesh n N) (u : (polyElement n S).Piecewise (mesh n N) k)
            T x s.1) ^ 2
        ≤ ∑ _s : formIdx n k, h ^ n * (Ci * (h ^ (0 + 1) * MT)) ^ 2 :=
          Finset.sum_le_sum fun s _ => hs1 s
      _ = Fintype.card (formIdx n k) * (h ^ n * (Ci * (h ^ (0 + 1) * MT)) ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ 2 ^ n * (h ^ n * (Ci * (h ^ (0 + 1) * MT)) ^ 2) :=
          mul_le_mul_of_nonneg_right (card_formIdx_le _) (by positivity)
      _ = 2 ^ n * Ci ^ 2 * n ^ 2 * h ^ 2 * h ^ n *
            (∑ s : formIdx n k, √(3 ^ n * Mρ * L s T)) ^ 2 := by
          simp only [MT]; ring
      _ ≤ 2 ^ n * Ci ^ 2 * n ^ 2 * h ^ 2 * h ^ n * (2 ^ n * ∑ s, 3 ^ n * Mρ * L s T) := by
          gcongr
      _ = 2 ^ n * Ci ^ 2 * n ^ 2 * 2 ^ n * 3 ^ n * (h ^ n * Mρ) * h ^ 2 * ∑ s, L s T := by
          rw [← Finset.mul_sum]; ring
      _ = 2 ^ n * Ci ^ 2 * n ^ 2 * 2 ^ n * 3 ^ n * (32 / γ) ^ n * h ^ 2 * ∑ s, L s T := by
          rw [show h ^ n * Mρ = (32 / γ) ^ n by
            simp only [Mρ]; rw [← mul_pow]; congr 1; field_simp]
  -- assembly over the simplices
  rw [hQ]
  refine (norm_sq_formL2_sub_glue_le (polyElement n S) (mesh n N)
    (isOpen_mesh_domain n N).measurableSet k _ _).trans ?_
  set K' := 2 ^ n * Ci ^ 2 * n ^ 2 * 2 ^ n * 3 ^ n * (32 / γ) ^ n * h ^ 2
  have hK' : 0 ≤ K' := by positivity
  calc ∑ T ∈ (mesh n N).simplices, ∑ s : formIdx n k, ∫ x in T.closedInterior,
        (((Submodule.inclusion c1Forms_le_contForms F : contForms n) : FormField n) x s.1 -
          (polyElement n S).extendPW (mesh n N) (u : (polyElement n S).Piecewise (mesh n N) k)
            T x s.1) ^ 2
      ≤ ∑ T ∈ (mesh n N).simplices, K' * ∑ s, L s T := Finset.sum_le_sum fun T hT => hloc T hT
    _ = K' * ∑ s, ∑ T ∈ (mesh n N).simplices, L s T := by rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ K' * ∑ s, ((6 ^ n * n.factorial : ℕ) : ℝ) * ‖g s‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => sum_locMass_le N (g s)) hK'
    _ = _ := by rw [← Finset.mul_sum]; simp only [K', Ci, P]; ring

end Poly


variable (n) in
/-- The constant of the `H¹` approximation of degree `k` of the sequence `S` by the parity
smoother at scale `γ = 1`: `√(n 3ⁿ) / 32 + √K₂` (`Poly.sq_norm_formL2_sub_paritySmoothedInterp_le`). -/
def h1ConstPar (S : PolySeq) (k : ℕ) : ℝ :=
  √(n * 3 ^ n) / 32 + √(2 ^ n * (1 + dofConst n S k * Module.finrank ℝ (S.space n k) *
    coeffConst n S k) ^ 2 * n ^ 2 * 2 ^ n * 3 ^ n * (32 / 1) ^ n *
      ((6 ^ n * n.factorial : ℕ) : ℝ))

omit [NeZero n] in
theorem h1ConstPar_nonneg (S : PolySeq) (k : ℕ) : 0 ≤ h1ConstPar n S k := by
  unfold h1ConstPar; positivity

omit [NeZero n] in
/-- **`H¹` approximation by `V_{h,Γ_J}`, on the mesh domain**: for `y ∈ L²(Ω; Λᵏ)` whose
coefficients `yₛ` lie in `H¹` with vanishing trace on the faces normal to `J ∆ s` (the parity
extension `ext_J y` has `H¹` coefficients), the parity-smoothed interpolant `v = Π_h R y` satisfies
`‖y - v‖ ≤ K h_N Σₛ ‖∇ yₛ‖`, `K = h1ConstPar` independent of `N`. -/
theorem exists_mem_VPartial_near_grad (S : PolySeq) (J : Finset (Fin n)) (N k : ℕ)
    (y : L2F ℝ (mesh n N).domain (formIdx n k))
    (hy : ∀ s : formIdx n k, zeroForm (y s) ∈
      (dPart (mesh n N).domain (symmDiff J s.1) ((0 : ℕ) : ℤ)).domain) :
    ∃ v ∈ (polyElement n S).VPartial (mesh n N) (partialFaces n J) k,
      ‖y - v‖ ≤ h1ConstPar n S k * hN N * ∑ s : formIdx n k,
        ‖dPart (mesh n N).domain (symmDiff J s.1) ((0 : ℕ) : ℤ) ⟨zeroForm (y s), hy s⟩‖ := by
  have hM := mesh_domain_eq_Q (n := n) N
  set ρ := parKernel n 1 one_pos le_rfl N
  set g : formIdx n k → L2F ℝ (mesh n N).domain (formIdx n (((0 : ℕ) : ℤ) + 1)) := fun s =>
    dPart (mesh n N).domain (symmDiff J s.1) ((0 : ℕ) : ℤ) ⟨zeroForm (y s), hy s⟩
  set h := hN N
  have hh : 0 < h := hN_pos N
  have hr : ρ.radius = h / 32 := by rw [parKernel_radius]; simp only [one_mul, h]
  set Fl := formL2 (isOpen_mesh_domain n N).measurableSet (mesh n N).isBounded_domain k
    (Submodule.inclusion c1Forms_le_contForms (paritySmoothForm ρ J hM k y))
  set Qy := (polyElement n S).paritySmoothedInterp (mesh n N) ρ J hM k y
  -- term A: mollification
  have hTA : ∀ s, ‖y s - Fl s‖ ≤ h / 32 * √(n * 3 ^ n) * ‖g s‖ := by
    intro s
    rw [← hr]
    refine norm_sub_le_grad_of_eq_Q ρ (symmDiff J s.1) hM (y s) (hy s) (Fl s) ?_
    filter_upwards [coeFn_formL2 (isOpen_mesh_domain n N).measurableSet
      (mesh n N).isBounded_domain (k : ℤ) (Submodule.inclusion c1Forms_le_contForms
        (paritySmoothForm ρ J hM k y)) s] with x hx
    rw [hx]
    change formExt (parCoeff ρ J y) s.1 x = _
    rw [formExt_val, parCoeff, pvec_symmDiff_empty]
  -- term B: interpolation of the smoothed field
  have hTB := Poly.sq_norm_formL2_sub_paritySmoothedInterp_le S (dofBound_dofConst S k)
    (dofConst_nonneg S k) (coeffBound_coeffConst S k) (coeffConst_nonneg S k) one_pos le_rfl J y
    (fun s => symmDiff J s.1) g fun s x hx j => partialDeriv_parCoeff_eq ρ J hM y s (hy s) hx j
  set K₂ := 2 ^ n * (1 + dofConst n S k * Module.finrank ℝ (S.space n k) *
    coeffConst n S k) ^ 2 * n ^ 2 * 2 ^ n * 3 ^ n * (32 / 1) ^ n *
      ((6 ^ n * n.factorial : ℕ) : ℝ)
  have hK₂ : 0 ≤ K₂ := by
    have := dofConst_nonneg (n := n) S k; have := coeffConst_nonneg (n := n) S k; positivity
  have hTB' : ‖Fl - Qy‖ ≤ √K₂ * h * ∑ s, ‖g s‖ := by
    have h1 : ‖Fl - Qy‖ ≤ √(K₂ * h ^ 2 * ∑ s, ‖g s‖ ^ 2) := by
      rw [← Real.sqrt_sq (norm_nonneg (Fl - Qy))]
      exact Real.sqrt_le_sqrt (by simpa only [K₂] using hTB)
    refine h1.trans ?_
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hK₂, Real.sqrt_sq hh.le]
    gcongr
    exact sqrt_sum_sq_le_sum _ fun s => norm_nonneg _
  refine ⟨Qy, (polyElement n S).paritySmoothedInterp_mem (mesh n N) ρ J hM k y, ?_⟩
  have hA : ‖y - Fl‖ ≤ h / 32 * √(n * 3 ^ n) * ∑ s, ‖g s‖ := by
    refine (L2F.norm_le_sum_norm _).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun s _ => by rw [PiLp.sub_apply]; exact hTA s
  calc ‖y - Qy‖ = ‖(y - Fl) + (Fl - Qy)‖ := by congr 1; abel
    _ ≤ ‖y - Fl‖ + ‖Fl - Qy‖ := norm_add_le _ _
    _ ≤ h / 32 * √(n * 3 ^ n) * ∑ s, ‖g s‖ + √K₂ * h * ∑ s, ‖g s‖ := add_le_add hA hTB'
    _ = h1ConstPar n S k * h * ∑ s, ‖g s‖ := by simp only [h1ConstPar, K₂]; ring

/-- **`H¹` approximation by `polyPartial`, on the cube**: for `y ∈ L²(Q; Λᵏ)` with
`yₛ ∈ H¹_{J ∆ s}(Q)`, some `v ∈ V_{h,Γ_J}ᵏ` satisfies `‖y - v‖ ≤ K h_N Σₛ ‖∇ yₛ‖`. -/
theorem exists_mem_polyPartial_near_grad (S : PolySeq) (J : Finset (Fin n)) (N k : ℕ)
    (y : L2F ℝ (cubeDomain n) (formIdx n k))
    (hy : ∀ s : formIdx n k, zeroForm (y s) ∈
      (dPart (cubeDomain n) (symmDiff J s.1) ((0 : ℕ) : ℤ)).domain) :
    ∃ v ∈ (polyPartial n S N J).V k,
      ‖y - v‖ ≤ h1ConstPar n S k * meshSize N * ∑ s : formIdx n k,
        ‖dPart (cubeDomain n) (symmDiff J s.1) ((0 : ℕ) : ℤ) ⟨zeroForm (y s), hy s⟩‖ := by
  rw [← hN_eq_meshSize]
  have key : ∀ (Ω' : Set (Fin n → ℝ)) (h : (mesh n N).domain = Ω') (hΩ' : IsOpen Ω')
      (hΩQ' : Ω' ⊆ Geometry.Q (Fin n)) (y : L2F ℝ Ω' (formIdx n k))
      (hy : ∀ s : formIdx n k, zeroForm (y s) ∈
        (dPart Ω' (symmDiff J s.1) ((0 : ℕ) : ℤ)).domain),
      ∃ v ∈ (partialSubcomplexOfEq h (isOpen_of_eq_Q (mesh_domain_eq_Q N))
          (mesh_domain_eq_Q N).le hΩ' hΩQ' J
          (subcomplexPart (polyElement n S) (mesh n N) (mesh_domain_eq_Q N) J)).V k,
        ‖y - v‖ ≤ h1ConstPar n S k * hN N * ∑ s : formIdx n k,
          ‖dPart Ω' (symmDiff J s.1) ((0 : ℕ) : ℤ) ⟨zeroForm (y s), hy s⟩‖ := by
    rintro Ω' rfl hΩ' hΩQ' y hy
    exact exists_mem_VPartial_near_grad S J N k y hy
  exact key _ (mesh_domain n N) (isOpen_cubeDomain n) (cubeDomain_subset_Q n) y hy

/-- **`H¹` approximation of the parity-smoothed projections** (the estimate needed by the BGG
discretization, for every class `J`): under `ParitySmoothingEstimates`, for `y ∈ L²(Q; Λᵏ)` whose
coefficients are `H¹` with vanishing traces on the faces normal to `J ∆ s` (i.e. `ext_J y` has
`H¹` coefficients), `‖y - π_N y‖ ≤ (1 + 2C) K h_N Σₛ ‖∇ yₛ‖`, `K = h1ConstPar n S k`. -/
theorem ParitySmoothingEstimates.norm_sub_proj_le_grad {J : Finset (Fin n)} {S : PolySeq}
    {ρ : ℕ → ReflKernel n} {C : ℝ} (hE : ParitySmoothingEstimates n J S ρ C) (N k : ℕ)
    (y : L2F ℝ (cubeDomain n) (formIdx n k))
    (hy : ∀ s : formIdx n k, zeroForm (y s) ∈
      (dPart (cubeDomain n) (symmDiff J s.1) ((0 : ℕ) : ℤ)).domain) :
    ‖y - (hE.proj N).π k y‖ ≤ (1 + 2 * C) * h1ConstPar n S k * meshSize N *
      ∑ s : formIdx n k,
        ‖dPart (cubeDomain n) (symmDiff J s.1) ((0 : ℕ) : ℤ) ⟨zeroForm (y s), hy s⟩‖ := by
  obtain ⟨v, hv, hyv⟩ := exists_mem_polyPartial_near_grad S J N k y hy
  refine (norm_sub_π_le_of_mem (hE.proj N) (hE.norm_proj_le N k) hv).trans ?_
  have := hE.two_mul_nonneg
  calc (1 + 2 * C) * ‖y - v‖ ≤ (1 + 2 * C) * (h1ConstPar n S k * meshSize N *
        ∑ s : formIdx n k,
          ‖dPart (cubeDomain n) (symmDiff J s.1) ((0 : ℕ) : ℤ) ⟨zeroForm (y s), hy s⟩‖) :=
        mul_le_mul_of_nonneg_left hyv (by linarith)
    _ = _ := by ring

end H1

/-! ### High-order rates for smooth data -/

section HighOrder

omit [NeZero n] in
/-- **Interpolants of forms with vanishing tangential components on the faces normal to `J`** have
vanishing DOFs there (any element family): `Π_h w ∈ Λ_{h,Γ_J}ᵏ`. -/
theorem globalInterp_mem_globalSpacePartial_of_face (E : LocalElement n) (M : SimplicialMesh n)
    (J : Finset (Fin n)) (k : ℕ) (w : contForms n)
    (hw : ∀ x : Fin n → ℝ, ∀ j ∈ J, (x j = 0 ∨ x j = 1 / 2) → ∀ t : Finset (Fin n), j ∉ t →
      (w : FormField n) x t = 0) :
    (E.globalInterp M k w : E.Piecewise M k) ∈ E.globalSpacePartial M (partialFaces n J) k := by
  refine ⟨(E.globalInterp M k _).2, fun T g hg ⟨F, ⟨j, hjJ, hF⟩, hgF⟩ i => ?_⟩
  rw [LocalElement.localDof_globalInterp _ _ _ _ _ _ hg]
  have hc : ∃ c : ℝ, (c = 0 ∨ c = 1 / 2) ∧ ∀ v ∈ g, v j = c := by
    rcases hF with h | h
    · exact ⟨0, Or.inl rfl, fun v hv => h v (hgF hv)⟩
    · exact ⟨1 / 2, Or.inr rfl, fun v hv => h v (hgF hv)⟩
  obtain ⟨c, hc, hgc⟩ := hc
  have h0 : E.dof g k i w = E.dof g k i 0 :=
    E.dof_congr i (tangentialTraceEq_zero_of_hyperplane hgc fun x hx t ht =>
      hw x j hjJ (by rw [hx]; exact hc) t ht)
  rw [h0, map_zero]

omit [NeZero n] in
/-- **High-order interpolation in `V_{h,Γ_J}`, on the mesh domain**: for a `C^{s+1}` degree-`k`
form `w` whose tangential components vanish on the faces normal to `J`, with
`‖D^{s+1} w‖ ≤ L` on `cl Q` and `P_sΛᵏ ⊆ P(T)ᵏ`, the canonical interpolant
`v = Π_h w ∈ V_{h,Γ_J}ᵏ` satisfies `‖w - v‖ ≤ A_k h_N^{s+1} L` (`A_k = polyInterpConst`). -/
theorem exists_mem_VPartial_le_smooth (S : PolySeq) (J : Finset (Fin n)) (N k s : ℕ)
    (hs : polySpace n s k ≤ S.space n k) {w : FormField n} (hw : ContDiff ℝ (s + 1) w)
    (hdeg : ∀ x, IsDeg k (w x))
    (hJ : ∀ x : Fin n → ℝ, ∀ j ∈ J, (x j = 0 ∨ x j = 1 / 2) → ∀ t : Finset (Fin n), j ∉ t →
      w x t = 0)
    {L : ℝ} (hL : ∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ L) :
    ∃ v ∈ (polyElement n S).VPartial (mesh n N) (partialFaces n J) k,
      ‖formL2 (isOpen_mesh_domain n N).measurableSet (mesh n N).isBounded_domain k
          ⟨w, hw.continuous⟩ - v‖ ≤ polyInterpConst n S k * (meshSize N ^ (s + 1) * L) := by
  set u := (polyElement n S).globalInterp (mesh n N) k ⟨w, hw.continuous⟩
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL _ (subset_closure (center_mem_cubeDomain n)))
  have hB1 : 0 ≤ (1 + dofConst n S k * Module.finrank ℝ (S.space n k) * coeffConst n S k) *
      (meshSize N ^ (s + 1) * L) := by
    have := dofConst_nonneg (n := n) S k; have := coeffConst_nonneg (n := n) S k
    have := (meshSize_pos N).le; positivity
  refine ⟨(polyElement n S).glue (mesh n N) k (u : (polyElement n S).Piecewise (mesh n N) k),
    ⟨⟨_, globalInterp_mem_globalSpacePartial_of_face (polyElement n S) (mesh n N) J k _ hJ⟩,
      rfl⟩, ?_⟩
  have h := norm_formL2_sub_glue_le_of_forall (polyElement n S) (mesh n N)
    (isOpen_mesh_domain n N).measurableSet k ⟨w, hw.continuous⟩
    (u : (polyElement n S).Piecewise (mesh n N) k) hB1
    fun T x hx t _ => abs_sub_globalInterp_le_cube S hs hw hdeg hL T (interior_subset hx) t
  refine h.trans (le_of_eq ?_)
  rw [polyInterpConst, mesh_domain n N]; ring

/-- **High-order interpolation in `polyPartial`, on the cube**: the estimate of
`exists_mem_VPartial_le_smooth` with `v ∈ V_{h,Γ_J}ᵏ = (polyPartial n S N J).V k`. -/
theorem exists_mem_polyPartial_le_smooth (S : PolySeq) (J : Finset (Fin n)) (N k s : ℕ)
    (hs : polySpace n s k ≤ S.space n k) {w : FormField n} (hw : ContDiff ℝ (s + 1) w)
    (hdeg : ∀ x, IsDeg k (w x))
    (hJ : ∀ x : Fin n → ℝ, ∀ j ∈ J, (x j = 0 ∨ x j = 1 / 2) → ∀ t : Finset (Fin n), j ∉ t →
      w x t = 0)
    {L : ℝ} (hL : ∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ L) :
    ∃ v ∈ (polyPartial n S N J).V k,
      ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
          ⟨w, hw.continuous⟩ - v‖ ≤ polyInterpConst n S k * (meshSize N ^ (s + 1) * L) := by
  have key : ∀ (Ω' : Set (Fin n → ℝ)) (h : (mesh n N).domain = Ω') (hΩ' : IsOpen Ω')
      (hΩQ' : Ω' ⊆ Geometry.Q (Fin n)) (hb : Bornology.IsBounded Ω'),
      ∃ v ∈ (partialSubcomplexOfEq h (isOpen_of_eq_Q (mesh_domain_eq_Q N))
          (mesh_domain_eq_Q N).le hΩ' hΩQ' J
          (subcomplexPart (polyElement n S) (mesh n N) (mesh_domain_eq_Q N) J)).V k,
        ‖formL2 hΩ'.measurableSet hb k ⟨w, hw.continuous⟩ - v‖ ≤
          polyInterpConst n S k * (meshSize N ^ (s + 1) * L) := by
    rintro Ω' rfl hΩ' hΩQ' hb
    exact exists_mem_VPartial_le_smooth S J N k s hs hw hdeg hJ hL
  exact key _ (mesh_domain n N) (isOpen_cubeDomain n) (cubeDomain_subset_Q n)
    (isBounded_cubeDomain n)

/-- **The high-order rate of the parity-smoothed projections** ([AFW2010], §5.5; [Arnold2018],
Ch. 7): under `ParitySmoothingEstimates`, for a `C^{s+1}` degree-`k` form `w` whose tangential
components vanish on the faces normal to `J` (e.g. coefficients `wₜ` symmetric of the parity
`c(J, t)` on `ℝⁿ`), with `‖D^{s+1} w‖ ≤ L` on `cl Q` and
`P_sΛᵏ ⊆ P(T)ᵏ` (e.g. `s + 1 ≤ r_k`, `polySpace_le_space`),
`‖w - π_N w‖ ≤ (1 + 2C) A_k h_N^{s+1} L`: the order `m = s + 1` up to the polynomial order. -/
theorem ParitySmoothingEstimates.norm_sub_proj_le_smooth {J : Finset (Fin n)} {S : PolySeq}
    {ρ : ℕ → ReflKernel n} {C : ℝ} (hE : ParitySmoothingEstimates n J S ρ C) (N k s : ℕ)
    (hs : polySpace n s k ≤ S.space n k) {w : FormField n} (hw : ContDiff ℝ (s + 1) w)
    (hdeg : ∀ x, IsDeg k (w x))
    (hJ : ∀ x : Fin n → ℝ, ∀ j ∈ J, (x j = 0 ∨ x j = 1 / 2) → ∀ t : Finset (Fin n), j ∉ t →
      w x t = 0)
    {L : ℝ} (hL : ∀ y ∈ closure (cubeDomain n), ‖iteratedFDeriv ℝ (s + 1) w y‖ ≤ L) :
    ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k ⟨w, hw.continuous⟩ -
        (hE.proj N).π k (formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
          ⟨w, hw.continuous⟩)‖ ≤
      (1 + 2 * C) * polyInterpConst n S k * meshSize N ^ (s + 1) * L := by
  obtain ⟨v, hv, hyv⟩ := exists_mem_polyPartial_le_smooth S J N k s hs hw hdeg hJ hL
  refine (norm_sub_π_le_of_mem (hE.proj N) (hE.norm_proj_le N k) hv).trans ?_
  have := hE.two_mul_nonneg
  calc (1 + 2 * C) * ‖formL2 (isOpen_cubeDomain n).measurableSet (isBounded_cubeDomain n) k
          ⟨w, hw.continuous⟩ - v‖
      ≤ (1 + 2 * C) * (polyInterpConst n S k * (meshSize N ^ (s + 1) * L)) :=
        mul_le_mul_of_nonneg_left hyv (by linarith)
    _ = _ := by ring

end HighOrder

end Feec.Models.Cube.FEM
