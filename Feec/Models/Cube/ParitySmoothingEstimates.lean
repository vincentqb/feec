module

public import Feec.Models.Cube.ParitySmoother
public import Feec.Models.Cube.DeRhamPartialFEM

/-!
# Parity smoothing estimates (draft)
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
