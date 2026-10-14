import Feec.Ch4.Adjoint
import Feec.Ch4.Restriction

/-!
# The abstract Hodge wave equation (Thesis §4.4: Thm 4.6, Thm 4.7)

For a Hilbert complex `W0 --d0--> W1 --d1--> W2` of closed, densely defined operators
(`Feec.HilbertComplex2`; closed range **not** assumed), the Hodge wave operator (4.5)
`L(σ,u,ρ) = (-d0* u, d0 σ + d1* ρ, -d1 u)` on `D(L) = V0 × (V1 ∩ V1*) × V2*`
(`HilbertComplex2.waveOp`) and the evolution (4.4) `ξ' = -Lξ`.

## Coverage

* **Operator part of Thm 4.6**:
  `waveOp_isSkewSymm` (the four adjoint identities), `dense_midDomain` / `dense_domL`
  (density of `D(L)`, missing in the thesis), `adjoint_waveOp_domain_le` (`D(L*) ⊆ D(L)`:
  the u-, σ- and ρ-steps, the last omitted in the thesis), `waveOp_isSkewAdjoint` (`L* = -L`),
  `IsSkewAdjoint.neg` / `neg_waveOp_isSkewAdjoint` (sign of (4.4)).
  Closed range is replaced by `orthogonal_ker_d1_le` (`(ker d1)ᗮ ⊆ ker d0*`) and
  `orthogonal_ker_adjoint_d0_le` (`(ker d0*)ᗮ ⊆ ker d1`); `(4.1a)` for `d0` is
  `HilbertComplex2.orthogonal_range_d0` (`Feec.Ch4.Adjoint`).
* **Evolution part of Thm 4.6**: `thm_4_6` (existence from `WellPosedHom (-L) T`, proved
  uniqueness and energy conservation `norm_eq_of_isStrongSolution`), `thm_4_6_classical`
  (thesis regularity), `thm_4_6_of_unitaryGroupGenerator` and
  `thm_4_6_classical_of_unitaryGroupGenerator` (existence, with the thesis' regularity, from a
  Stone group; via `UnitaryGroupGenerator.wellPosedClassical`).
* **Weak form** (4.7)/(4.8): `toComplex3` (bridge to `Complex3`, test space `V0 × V1 × W2`),
  `toComplex3_a`, `a_self` (`a(ψ,ψ) = 0`), `IsWeakSolution`, `IsClassicalWeakSolution`,
  `weak_unique` (energy argument written out).
* **Thm 4.7**: `isWeakSolution_of_isStrongSolution`,
  `isClassicalWeakSolution_of_isClassicalSolution` (uses `norm_embed`, `d0 σ ⟂ d1* ρ`),
  `weak_imp_strong`, `weak_imp_classical`, and the equivalences `thm_4_7`,
  `thm_4_7_classical`. The thesis' self-citation is replaced by a citation of Thm 4.6.
* **Non-vacuity** (critic item 6): `wellPosedHom_neg_waveOp`, `wellPosedClassical_neg_waveOp`
  (every finite-dimensional complex), `HodgeWaveExample.nonvacuous` (a complex with `L ≠ 0`).

## Existence and solution classes (critic item 5)

Stone's theorem / Hille–Yosida is not in Mathlib; existence enters only as the explicit
hypotheses `WellPosedHom (-L) T` or `WellPosedClassical (-L) T Adm` (Thm 4.3 for `-L`).
`IsStrongSolution` and `IsWeakSolution` are pointwise notions (membership in `D(L)`, resp. `V`,
and a derivative in `W` at each `t ∈ [0,T]`): uniqueness statements for them are *stronger*
than the thesis', existence statements from `WellPosedHom` are *weaker* than the thesis'
`C⁰([0,T];D(L)) ∩ C¹([0,T];W)`. The thesis' classes are `IsClassicalSolution`
(`Feec.Ch4.Restriction`) and `IsClassicalWeakSolution` (`C⁰([0,T];V) ∩ C¹([0,T];W)`), with the
`_classical` versions of Thms 4.6/4.7 stated for them.

## References

* [QuennevilleBelair2015], §4.4 (the system (4.4), the operator (4.5), Thm 4.6, the weak form
  (4.7)/(4.8), weak uniqueness, Thm 4.7) and §4.3 (Thm 4.3, the existence theorem for
  skew-adjoint generators used in Thm 4.6)
* [Arnold2018] (the FEEC framework of Hilbert complexes `d`, dual complexes `d*`)
* [AFW2010] (abstract Hilbert complexes, domains `V^k`, `V*_k` of `d` and `d*`)
* [BruningLesch1992] (Hilbert complexes)
* [CazenaveHaraux1998], Prop 4.1.6 and Cor 2.4.9 (as cited in [QuennevilleBelair2015, §4.3]
  for Thm 4.3)
* [Pazy1983], §1.10 (unitary groups and Stone's theorem: a densely defined skew-adjoint operator
  generates a unitary group; this is the existence input that enters here as a hypothesis)
* [Geveci1988] (mixed first-order formulation of the wave equation, the scalar antecedent of
  (4.4); cf. [QuennevilleBelair2015, §4.8])
* [GilletteHolstZhu2017] (FEEC for evolution problems; cited in [QuennevilleBelair2015, §4.8]
  as the 2012 Gillette–Holst preprint)
-/

open scoped RealInnerProductSpace
open Set LinearPMap

noncomputable section

namespace Feec.HilbertComplex2



variable {W0 W1 W2 : Type*}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]

/-! ### Coordinates on `W = W0 × W1 × W2` -/

/-- `tot` as a continuous linear equivalence (auxiliary). -/
def totL : Tot W0 W1 W2 ≃L[ℝ] W0 × W1 × W2 :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ W0 (WithLp 2 (W1 × W2))).trans
    ((ContinuousLinearEquiv.refl ℝ W0).prodCongr (WithLp.prodContinuousLinearEquiv 2 ℝ W1 W2))

@[simp] theorem totL_apply (x : Tot W0 W1 W2) : totL x = tot W0 W1 W2 x := rfl

/-- The `ℓ²` inner product of `W` in coordinates (auxiliary). -/
theorem tot_inner (x y : Tot W0 W1 W2) :
    ⟪x, y⟫ = ⟪(tot W0 W1 W2 x).1, (tot W0 W1 W2 y).1⟫ + ⟪(tot W0 W1 W2 x).2.1,
      (tot W0 W1 W2 y).2.1⟫ + ⟪(tot W0 W1 W2 x).2.2, (tot W0 W1 W2 y).2.2⟫ := by
  simp only [WithLp.prod_inner_apply, tot, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply]
  rw [add_assoc]; rfl

/-- The squared norm of `W` in coordinates (auxiliary). -/
theorem tot_norm_sq (x : Tot W0 W1 W2) :
    ‖x‖ ^ 2 = ‖(tot W0 W1 W2 x).1‖ ^ 2 + ‖(tot W0 W1 W2 x).2.1‖ ^ 2 +
      ‖(tot W0 W1 W2 x).2.2‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, tot_inner, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

variable [CompleteSpace W0] [CompleteSpace W1] [CompleteSpace W2]
variable (H : HilbertComplex2 W0 W1 W2)

/-- `D(L) = V0 × (V1 ∩ V1*) × V2*` in coordinates (auxiliary). -/
theorem mem_domL {x : Tot W0 W1 W2} : x ∈ H.domL ↔ (tot W0 W1 W2 x).1 ∈ H.d0.domain ∧
    (tot W0 W1 W2 x).2.1 ∈ H.midDomain ∧ (tot W0 W1 W2 x).2.2 ∈ H.d1†.domain := by
  simp [domL, Submodule.mem_prod]

@[simp] theorem coe_pr0 (x : H.domL) : (H.pr0 x : W0) = (tot W0 W1 W2 x).1 := rfl
@[simp] theorem coe_prV1 (x : H.domL) : (H.prV1 x : W1) = (tot W0 W1 W2 x).2.1 := rfl
@[simp] theorem coe_prV1s (x : H.domL) : (H.prV1s x : W1) = (tot W0 W1 W2 x).2.1 := rfl
@[simp] theorem coe_prV2s (x : H.domL) : (H.prV2s x : W2) = (tot W0 W1 W2 x).2.2 := rfl

/-- The Hodge wave operator (4.5) in coordinates (auxiliary). -/
theorem tot_waveOp (x : H.waveOp.domain) :
    tot W0 W1 W2 (H.waveOp x) = (-(H.d0† (H.prV1s ⟨x.1, x.2⟩)),
      H.d0 (H.pr0 ⟨x.1, x.2⟩) + H.d1† (H.prV2s ⟨x.1, x.2⟩), -(H.d1 (H.prV1 ⟨x.1, x.2⟩))) := by
  change (tot W0 W1 W2) ((tot W0 W1 W2).symm _) = _
  rw [LinearEquiv.apply_symm_apply]; rfl

/-- A point of `D(L)` from its three components (auxiliary). -/
def mkDom (σ : H.d0.domain) (u : H.midDomain) (ρ : H.d1†.domain) : H.waveOp.domain :=
  ⟨(tot W0 W1 W2).symm ((σ : W0), (u : W1), (ρ : W2)), by
    change _ ∈ H.domL
    rw [mem_domL]; simp only [LinearEquiv.apply_symm_apply]; exact ⟨σ.2, u.2, ρ.2⟩⟩

@[simp] theorem tot_mkDom (σ : H.d0.domain) (u : H.midDomain) (ρ : H.d1†.domain) :
    tot W0 W1 W2 (H.mkDom σ u ρ : Tot W0 W1 W2) = ((σ : W0), (u : W1), (ρ : W2)) :=
  LinearEquiv.apply_symm_apply _ _

/-- `L (σ, u, ρ)` in coordinates (auxiliary). -/
theorem tot_waveOp_mkDom (σ : H.d0.domain) (u : H.midDomain) (ρ : H.d1†.domain) :
    tot W0 W1 W2 (H.waveOp (H.mkDom σ u ρ)) =
      (-(H.d0† ⟨u, (Submodule.mem_inf.1 u.2).2⟩), H.d0 σ + H.d1† ρ,
        -(H.d1 ⟨u, (Submodule.mem_inf.1 u.2).1⟩)) := by
  rw [tot_waveOp]
  have e0 : H.pr0 ⟨_, (H.mkDom σ u ρ).2⟩ = σ := Subtype.ext (by simp)
  have e1 : H.prV1 ⟨_, (H.mkDom σ u ρ).2⟩ = ⟨u, (Submodule.mem_inf.1 u.2).1⟩ :=
    Subtype.ext (by simp)
  have e1s : H.prV1s ⟨_, (H.mkDom σ u ρ).2⟩ = ⟨u, (Submodule.mem_inf.1 u.2).2⟩ :=
    Subtype.ext (by simp)
  have e2 : H.prV2s ⟨_, (H.mkDom σ u ρ).2⟩ = ρ := Subtype.ext (by simp)
  rw [e0, e1, e1s, e2]

/-! ### Skew-symmetry and the complex identities used in Thm 4.6 -/

/-- The Hodge wave operator is skew-symmetric on `D(L)`: `⟪Lξ, η⟫ = -⟪ξ, Lη⟫`
(Thesis Thm 4.6, proof, the computation `⟨ξ, Lη⟩ = -⟨Lξ, η⟩`).

Note: the thesis displays this computation; the four adjoint identities it uses are
`⟪σ, d0* v⟫ = ⟪d0 σ, v⟫`, `⟪u, d0 τ⟫ = ⟪d0* u, τ⟫`, `⟪u, d1* μ⟫ = ⟪d1 u, μ⟫` and
`⟪ρ, d1 v⟫ = ⟪d1* ρ, v⟫`. No closed range and no `d** = d` is needed.

See [QuennevilleBelair2015, Thm 4.6] (proof, first display). -/
theorem waveOp_isSkewSymm : IsSkewSymm H.waveOp := by
  intro x y
  rw [tot_inner, tot_inner, tot_waveOp, tot_waveOp]
  have a0 := adjoint_isFormalAdjoint H.dense0 (H.prV1s ⟨x.1, x.2⟩) (H.pr0 ⟨y.1, y.2⟩)
  have a0' := adjoint_isFormalAdjoint H.dense0 (H.prV1s ⟨y.1, y.2⟩) (H.pr0 ⟨x.1, x.2⟩)
  have a1 := adjoint_isFormalAdjoint H.dense1 (H.prV2s ⟨x.1, x.2⟩) (H.prV1 ⟨y.1, y.2⟩)
  have a1' := adjoint_isFormalAdjoint H.dense1 (H.prV2s ⟨y.1, y.2⟩) (H.prV1 ⟨x.1, x.2⟩)
  simp only [coe_pr0, coe_prV1, coe_prV1s, coe_prV2s] at a0 a0' a1 a1'
  simp only [inner_neg_left, inner_neg_right, inner_add_left, inner_add_right]
  have c1 := real_inner_comm (H.d0 (H.pr0 ⟨x.1, x.2⟩)) (tot W0 W1 W2 (y : Tot W0 W1 W2)).2.1
  have c3 := real_inner_comm (H.d1 (H.prV1 ⟨x.1, x.2⟩)) (tot W0 W1 W2 (y : Tot W0 W1 W2)).2.2
  have c4 := real_inner_comm (tot W0 W1 W2 (x : Tot W0 W1 W2)).1 (H.d0† (H.prV1s ⟨y.1, y.2⟩))
  have c2 := real_inner_comm (H.d1† (H.prV2s ⟨y.1, y.2⟩)) (tot W0 W1 W2 (x : Tot W0 W1 W2)).2.1
  linarith

/-- `Z*₁ = ker d0*` is closed (`d0*` is closed). -/
theorem isClosed_ker_adjoint_d0 : IsClosed (H.d0†.ker : Set W1) :=
  isClosed_ker (adjoint_isClosed H.dense0)

/-- The kernel of a partial map lies in its domain (auxiliary). -/
theorem ker_le_domain' {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (A : E →ₗ.[ℝ] F) : A.ker ≤ A.domain := by
  intro x hx
  obtain ⟨y, rfl, -⟩ := mem_ker_iff.1 hx
  exact y.2

/-- `B*₁ ⊆ Z*₁`: `range d1* ⊆ ker d0*` (the dual complex property `d0* d1* = 0`).
Cf. the dual complex of a Hilbert complex in [AFW2010] and [Arnold2018]. -/
theorem range_adjoint_d1_le : LinearMap.range H.d1†.toFun ≤ H.d0†.ker := by
  rintro _ ⟨ρ, rfl⟩
  exact mem_ker_iff.2 ⟨⟨_, H.adjoint_map_mem ρ⟩, rfl, H.adjoint_comp_zero ρ⟩

-- `orthogonal_ker_d1_le` (`(ker d1)ᗮ ⊆ ker d0*`) and `orthogonal_ker_adjoint_d0_le`
-- (`(ker d0*)ᗮ ⊆ ker d1`), both without closed range, live in `Feec.Ch4.Adjoint`.

/-- `⟪d0 σ, d1* ρ⟫ = 0` and hence `‖d0 σ + d1* ρ‖² = ‖d0 σ‖² + ‖d1* ρ‖²`
(Thesis Thm 4.7, first bullet: "it certainly belongs to `C⁰([0,T], V)`").

Thesis gap: this orthogonality (from `d1 d0 = 0`) is what makes the graph norm of `L` control
the `V`-norms of `σ` and `u`; it is not mentioned in the thesis.
See [QuennevilleBelair2015, Thm 4.7] (proof, first part). -/
theorem norm_embed (σ : H.d0.domain) (ρ : H.d1†.domain) :
    ‖H.d0 σ + H.d1† ρ‖ ^ 2 = ‖H.d0 σ‖ ^ 2 + ‖H.d1† ρ‖ ^ 2 := by
  rw [norm_add_sq_real, real_inner_comm, H.inner_adjoint_d0]
  ring

/-! ### Density of `D(L)` -/

section DenseAux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If `v - P_K v ∈ M` for all `v` in a dense set `D`, then `Kᗮ ⊆ cl M` (auxiliary). -/
theorem orthogonal_le_closure_of_dense (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    {D : Set E} (hD : Dense D) (M : Submodule ℝ E)
    (hM : ∀ v ∈ D, v - K.starProjection v ∈ M) : Kᗮ ≤ M.topologicalClosure := by
  intro k hk
  set Q : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - K.starProjection
  have hQk : Q k = k := by
    simp [Q, (Submodule.starProjection_apply_eq_zero_iff K).2 hk]
  have : Q k ∈ closure (Q '' D) := by
    apply image_closure_subset_closure_image Q.continuous
    exact ⟨k, hD.closure_eq ▸ mem_univ k, rfl⟩
  rw [hQk] at this
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  refine closure_mono ?_ this
  rintro _ ⟨v, hv, rfl⟩
  exact hM v hv

end DenseAux

/-- `V1 ∩ V1*` is dense in `W1` (missing in the thesis; needed for Thm 4.6).

Thesis gap: density of `D(L)` is never proved, but it is needed both for `L*` to be an operator
and for the hypothesis of Thm 4.3. The proof here needs **no closed range** and no von Neumann
`D(d*d)`-core argument: `ker d0* ∩ V1` is dense in `ker d0*` (project `V1` off `cl B⁰ ⊆ Z¹`),
`ker d1 ∩ V1*` is dense in `ker d1` (project `V1*` off `(Z¹)ᗮ ⊆ Z*₁`), and
`ker d1 + ker d0* ⊇ cl B⁰ + (cl B⁰)ᗮ = W1`.

Used for [QuennevilleBelair2015, Thm 4.6] (with `D(L)` as in §4.4, (4.5)). -/
theorem dense_midDomain : Dense (H.midDomain : Set W1) := by
  set K := H.d0†.kerᗮ
  have : CompleteSpace H.d0†.ker := H.isClosed_ker_adjoint_d0.completeSpace_coe
  have hK : Kᗮ = H.d0†.ker := Submodule.orthogonal_orthogonal _
  set K' := H.d1.kerᗮ
  have : CompleteSpace H.d1.ker := (isClosed_ker H.closed1).completeSpace_coe
  have hK' : K'ᗮ = H.d1.ker := Submodule.orthogonal_orthogonal _
  -- `ker d0* ⊆ cl (V1 ∩ V1*)`
  have h1 : H.d0†.ker ≤ H.midDomain.topologicalClosure := by
    rw [← hK]
    refine orthogonal_le_closure_of_dense K H.dense1 _ fun v hv => ?_
    have hP : K.starProjection v ∈ H.d1.domain :=
      ker_le_domain' _ (H.orthogonal_ker_adjoint_d0_le (K.starProjection_apply_mem v))
    have hQ : v - K.starProjection v ∈ Kᗮ := K.sub_starProjection_mem_orthogonal v
    rw [hK] at hQ
    exact Submodule.mem_inf.2 ⟨H.d1.domain.sub_mem hv hP, ker_le_domain' _ hQ⟩
  -- `ker d1 ⊆ cl (V1 ∩ V1*)`
  have h2 : H.d1.ker ≤ H.midDomain.topologicalClosure := by
    rw [← hK']
    refine orthogonal_le_closure_of_dense K' (dense_adjoint_domain _ H.dense0 H.closed0) _
      fun w hw => ?_
    have hP : K'.starProjection w ∈ H.d0†.domain :=
      ker_le_domain' _ (H.orthogonal_ker_d1_le (K'.starProjection_apply_mem w))
    have hQ : w - K'.starProjection w ∈ K'ᗮ := K'.sub_starProjection_mem_orthogonal w
    rw [hK'] at hQ
    exact Submodule.mem_inf.2 ⟨ker_le_domain' _ hQ, H.d0†.domain.sub_mem hw hP⟩
  rw [Submodule.dense_iff_topologicalClosure_eq_top, eq_top_iff]
  calc (⊤ : Submodule ℝ W1) = K ⊔ Kᗮ := Submodule.sup_orthogonal_of_hasOrthogonalProjection.symm
    _ ≤ H.midDomain.topologicalClosure :=
      sup_le (H.orthogonal_ker_adjoint_d0_le.trans h2) (hK ▸ h1)

/-- `D(L) = V0 × (V1 ∩ V1*) × V2*` is dense in `W` (missing in the thesis; needed for Thm 4.6).
See [QuennevilleBelair2015, §4.4, (4.5) and Thm 4.6]. -/
theorem dense_domL : Dense (H.waveOp.domain : Set (Tot W0 W1 W2)) := by
  have hs : Dense ((H.d0.domain : Set W0) ×ˢ ((H.midDomain : Set W1) ×ˢ
      (H.d1†.domain : Set W2))) :=
    H.dense0.prod (H.dense_midDomain.prod (dense_adjoint_domain _ H.dense1 H.closed1))
  have := hs.preimage (totL (W0 := W0) (W1 := W1) (W2 := W2)).toHomeomorph.isOpenMap
  convert this using 1
  ext x
  change x ∈ H.domL ↔ _
  rw [mem_domL]
  rfl

/-! ### Skew-adjointness (Thm 4.6, operator part) -/

/-- A domain point in the kernel is mapped to `0` (auxiliary). -/
theorem apply_eq_zero_of_mem_ker' {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] {A : E →ₗ.[ℝ] F} (x : A.domain) (hx : (x : E) ∈ A.ker) : A x = 0 := by
  obtain ⟨y, hy, hy0⟩ := mem_ker_iff.1 hx
  rw [← hy0]; congr 1; exact Subtype.ext hy

/-- `A ⟨0, h⟩ = 0` (auxiliary). -/
@[simp] theorem map_mk_zero' {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] (A : E →ₗ.[ℝ] F) (h : (0 : E) ∈ A.domain) : A ⟨0, h⟩ = 0 :=
  A.map_zero

/-- `D(L*) ⊆ D(L)` for the Hodge wave operator: the maximality half of Thesis Thm 4.6.

Thesis gap: the thesis' proof (i) uses the closed-range Hodge decomposition `w = z + y`,
`y ∈ (Z¹)ᗮ = B*₁`, for the σ-step; here only `(Z¹)ᗮ ⊆ ker d0*` (`orthogonal_ker_d1_le`)
is used, so **no closed range** is needed; (ii) omits the ρ-step ("the argument is similar"),
written out here with the dual projection onto `(ker d0*)ᗮ = cl B⁰ ⊆ Z¹`;
(iii) uses `d** = d` for `d0`, `d1` (closed and densely defined), here in the form
`mem_graph_iff_of_isClosed`. The bound (4.6) is replaced by the adjoint identity
`⟪L*ξ, η⟫ = ⟪ξ, Lη⟫`, which avoids estimating constants.

See [QuennevilleBelair2015, Thm 4.6] (proof, "It remains to show that `D(L*) ⊂ D(L)`"; the
thesis attributes the argument to Arnold). -/
theorem adjoint_waveOp_domain_le : H.waveOp†.domain ≤ H.waveOp.domain := by
  intro x hx
  have key : ∀ y : H.waveOp.domain, ⟪H.waveOp† ⟨x, hx⟩, (y : Tot W0 W1 W2)⟫ =
      ⟪x, H.waveOp y⟫ := fun y => adjoint_isFormalAdjoint H.dense_domL ⟨x, hx⟩ y
  set σ := (tot W0 W1 W2 x).1
  set u := (tot W0 W1 W2 x).2.1
  set ρ := (tot W0 W1 W2 x).2.2
  set a := (tot W0 W1 W2 (H.waveOp† ⟨x, hx⟩)).1
  set b := (tot W0 W1 W2 (H.waveOp† ⟨x, hx⟩)).2.1
  set c := (tot W0 W1 W2 (H.waveOp† ⟨x, hx⟩)).2.2
  -- the adjoint identity tested on `(τ, v, μ) ∈ D(L)`
  have key' : ∀ (τ : H.d0.domain) (v : H.midDomain) (μ : H.d1†.domain),
      ⟪a, (τ : W0)⟫ + ⟪b, (v : W1)⟫ + ⟪c, (μ : W2)⟫ =
        -⟪σ, H.d0† ⟨v, (Submodule.mem_inf.1 v.2).2⟩⟫ + ⟪u, H.d0 τ + H.d1† μ⟫ -
          ⟪ρ, H.d1 ⟨v, (Submodule.mem_inf.1 v.2).1⟩⟫ := by
    intro τ v μ
    have := key (H.mkDom τ v μ)
    rw [tot_inner, tot_inner, tot_waveOp_mkDom, tot_mkDom] at this
    simpa only [inner_neg_right, sub_eq_add_neg] using this
  -- u-step: `u ∈ V1*`
  have hu1 : u ∈ H.d0†.domain := by
    refine mem_adjoint_domain_of_exists u ⟨a, fun τ => ?_⟩
    have := key' τ 0 0
    simpa only [ZeroMemClass.coe_zero, inner_zero_right, add_zero, map_mk_zero',
      LinearPMap.map_zero, neg_zero, sub_zero, zero_add] using this
  -- u-step: `u ∈ V1`, via `d1** = d1`
  have hu2 : u ∈ H.d1.domain := by
    have hg : (u, c) ∈ H.d1.graph := by
      rw [mem_graph_iff_of_isClosed H.dense1 H.closed1]
      intro μ
      have := key' 0 0 μ
      simp only [ZeroMemClass.coe_zero, inner_zero_right, zero_add, map_mk_zero',
        LinearPMap.map_zero, neg_zero, sub_zero] at this
      rw [real_inner_comm, ← this, real_inner_comm]
    exact LinearPMap.mem_domain_of_mem_graph hg
  -- σ-step: `σ ∈ V0`, via `d0** = d0` and the projection onto `(ker d1)ᗮ ⊆ ker d0*`
  have hσ : σ ∈ H.d0.domain := by
    set K' := H.d1.kerᗮ
    have : CompleteSpace H.d1.ker := (isClosed_ker H.closed1).completeSpace_coe
    have hK' : K'ᗮ = H.d1.ker := Submodule.orthogonal_orthogonal _
    have hg : (σ, -(b - K'.starProjection b)) ∈ H.d0.graph := by
      rw [mem_graph_iff_of_isClosed H.dense0 H.closed0]
      intro w
      have hyk : K'.starProjection (w : W1) ∈ H.d0†.ker :=
        H.orthogonal_ker_d1_le (K'.starProjection_apply_mem _)
      set y : H.d0†.domain := ⟨_, ker_le_domain' _ hyk⟩
      set z := w - y
      have hz : (z : W1) ∈ H.d1.ker := by
        rw [← hK']; exact K'.sub_starProjection_mem_orthogonal _
      have hdz : H.d0† z = H.d0† w := by
        rw [LinearPMap.map_sub, apply_eq_zero_of_mem_ker' y hyk, sub_zero]
      set v : H.midDomain := ⟨z, Submodule.mem_inf.2 ⟨ker_le_domain' _ hz, z.2⟩⟩
      have := key' 0 v 0
      have hd1v : H.d1 ⟨(v : W1), (Submodule.mem_inf.1 v.2).1⟩ = 0 :=
        apply_eq_zero_of_mem_ker' _ hz
      simp only [ZeroMemClass.coe_zero, inner_zero_right, add_zero,
        LinearPMap.map_zero, zero_add, hd1v, sub_zero] at this
      change ⟪b, (w : W1) - K'.starProjection w⟫ = -⟪σ, H.d0† z⟫ at this
      rw [hdz] at this
      rw [real_inner_comm, inner_neg_right, inner_sub_right,
        ← Submodule.inner_starProjection_left_eq_right]
      rw [inner_sub_right] at this
      linarith [real_inner_comm b (w : W1), real_inner_comm b (K'.starProjection (w : W1))]
    exact LinearPMap.mem_domain_of_mem_graph hg
  -- ρ-step: `ρ ∈ V2*`, via the projection onto `(ker d0*)ᗮ ⊆ ker d1`
  have hρ : ρ ∈ H.d1†.domain := by
    set K := H.d0†.kerᗮ
    have : CompleteSpace H.d0†.ker := H.isClosed_ker_adjoint_d0.completeSpace_coe
    have hK : Kᗮ = H.d0†.ker := Submodule.orthogonal_orthogonal _
    refine mem_adjoint_domain_of_exists ρ ⟨-(b - K.starProjection b), fun v => ?_⟩
    have hyk : K.starProjection (v : W1) ∈ H.d1.ker :=
      H.orthogonal_ker_adjoint_d0_le (K.starProjection_apply_mem _)
    set y : H.d1.domain := ⟨_, ker_le_domain' _ hyk⟩
    set z := v - y
    have hz : (z : W1) ∈ H.d0†.ker := by
      rw [← hK]; exact K.sub_starProjection_mem_orthogonal _
    have hdz : H.d1 z = H.d1 v := by
      rw [LinearPMap.map_sub, apply_eq_zero_of_mem_ker' y hyk, sub_zero]
    set w : H.midDomain := ⟨z, Submodule.mem_inf.2 ⟨z.2, ker_le_domain' _ hz⟩⟩
    have := key' 0 w 0
    have hd0w : H.d0† ⟨(w : W1), (Submodule.mem_inf.1 w.2).2⟩ = 0 :=
      apply_eq_zero_of_mem_ker' _ hz
    simp only [ZeroMemClass.coe_zero, inner_zero_right, add_zero,
      LinearPMap.map_zero, zero_add, hd0w, neg_zero, zero_sub] at this
    change ⟪b, (v : W1) - K.starProjection v⟫ = -⟪ρ, H.d1 z⟫ at this
    rw [hdz] at this
    rw [inner_neg_left, inner_sub_left, Submodule.inner_starProjection_left_eq_right,
      ← inner_sub_right, this, neg_neg]
  exact (mem_domL H).2 ⟨hσ, Submodule.mem_inf.2 ⟨hu2, hu1⟩, hρ⟩

/-- **Thesis Thm 4.6 (operator part)**: the Hodge wave operator `L` of (4.5) is densely defined
and skew-adjoint, `L* = -L`, for **every** Hilbert complex of length 2.

Strengthening: the thesis assumes closed range; it is not needed (see
`adjoint_waveOp_domain_le`). Thesis gap: density of `D(L)` (`dense_domL`) is not proved in
the thesis.

See [QuennevilleBelair2015, Thm 4.6]; skew-adjointness is the hypothesis of
[QuennevilleBelair2015, Thm 4.3] and of Stone's theorem, cf. [Pazy1983, §1.10]. -/
theorem waveOp_isSkewAdjoint : IsSkewAdjoint H.waveOp :=
  (isSkewAdjoint_iff _ H.dense_domL).2 ⟨H.waveOp_isSkewSymm, H.adjoint_waveOp_domain_le⟩

end Feec.HilbertComplex2

namespace Feec

open LinearPMap

/-- `-L` is skew-adjoint when `L` is (used to pass from `L` to the evolution `ξ' = -Lξ`).

Thesis gap: (4.4) reads `ξ' = -Lξ`, while Thm 4.3 is stated for `U' = LU`; the thesis applies
Thm 4.3 silently, which requires this lemma. See [QuennevilleBelair2015, (4.4) and Thm 4.3]. -/
theorem IsSkewAdjoint.neg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {L : E →ₗ.[ℝ] E} (hL : IsSkewAdjoint L) : IsSkewAdjoint (-L) := by
  have hD : Dense ((-L).domain : Set E) := hL.dense_domain
  refine (isSkewAdjoint_iff _ hD).2 ⟨fun x y => ?_, fun y hy => ?_⟩
  · have := (hL.isSkewSymm hL.dense_domain) x y
    simp only [LinearPMap.neg_apply, inner_neg_left, inner_neg_right]
    linarith
  · rw [mem_adjoint_domain_iff] at hy
    have hy' : y ∈ L†.domain := by
      rw [mem_adjoint_domain_iff]
      have : (innerₛₗ ℝ y).comp L.toFun = -((innerₛₗ ℝ y).comp (-L).toFun) := by
        ext x; simp [LinearPMap.neg_apply]
      rw [this]
      exact hy.neg
    have : L†.domain = L.domain := by rw [show L† = -L from hL]; rfl
    exact this ▸ hy'

end Feec

namespace Feec.HilbertComplex2

variable {W0 W1 W2 : Type*}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
    (H : HilbertComplex2 W0 W1 W2)

open LinearPMap

/-- The generator `-L` of the Hodge wave evolution `ξ' = -Lξ` (4.4) is skew-adjoint.
See [QuennevilleBelair2015, §4.4, (4.4)–(4.5) and Thm 4.6]. -/
theorem neg_waveOp_isSkewAdjoint : IsSkewAdjoint (-H.waveOp) :=
  H.waveOp_isSkewAdjoint.neg

/-! ### Strong solutions: Thm 4.6 -/

section Energy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Energy conservation `‖U(t)‖ = ‖U₀‖` for strong solutions of `U' = LU`, `L` skew-symmetric
(Thesis Thm 4.6, "energy is conserved"; auxiliary, general `L`).
See [QuennevilleBelair2015, Thm 4.6]; cf. the norm-preserving unitary groups of
[Pazy1983, §1.10]. -/
theorem norm_eq_of_isStrongSolution {L : E →ₗ.[ℝ] E} (hL : IsSkewSymm L) {T : ℝ} {U₀ : E}
    {U : ℝ → E} (hU : IsStrongSolution L T U₀ 0 U) : ∀ t ∈ Icc 0 T, ‖U t‖ = ‖U₀‖ := by
  have hc : ∀ t ∈ Icc (0 : ℝ) T, ‖U t‖ ^ 2 = ‖U 0‖ ^ 2 := by
    refine constant_of_has_deriv_right_zero (f := fun t => ‖U t‖ ^ 2)
      (hU.continuousOn.norm.pow 2) fun t ht => ?_
    have := (hU.hasDerivWithinAt_Ici ht).norm_sq
    simp only [Pi.zero_apply, add_zero] at this
    rwa [real_inner_comm, hL.inner_self, mul_zero] at this
  intro t ht
  have := hc t ht
  rw [hU.init] at this
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

end Energy

/-- **Thesis Thm 4.6** (corrected): for every Hilbert complex of length 2 (closed range **not**
assumed), `L` is densely defined and skew-adjoint, and under the existence hypothesis
`WellPosedHom (-L) T` (standing for Thm 4.3, i.e. Stone's theorem, absent from Mathlib) every
`ξ₀ ∈ D(L)` has a strong solution of `ξ' = -Lξ`, `ξ(0) = ξ₀`, which is unique and conserves
energy, `‖ξ(t)‖ = ‖ξ₀‖`.

Strengthening: closed range is dropped (`adjoint_waveOp_domain_le`); the sign of (4.4) is handled
by `IsSkewAdjoint.neg`. Thesis gap: density of `D(L)` (`dense_domL`) and the ρ-step are
supplied. Scope (critic item 5): `IsStrongSolution` asks only for pointwise derivatives, so the
existence part is weaker than the thesis' `C⁰([0,T];D(L)) ∩ C¹([0,T];W)` (see
`thm_4_6_classical`) and the uniqueness part is stronger. Uniqueness and energy conservation
are proved, not assumed.

See [QuennevilleBelair2015, Thm 4.6]; the existence input is [QuennevilleBelair2015, Thm 4.3]
(cited there from [CazenaveHaraux1998, Prop 4.1.6 and Cor 2.4.9]); cf. Stone's theorem,
[Pazy1983, §1.10]. -/
theorem thm_4_6 {T : ℝ} (hHY : WellPosedHom (-H.waveOp) T) {ξ₀ : Tot W0 W1 W2}
    (h0 : ξ₀ ∈ H.waveOp.domain) :
    Dense (H.waveOp.domain : Set (Tot W0 W1 W2)) ∧ IsSkewAdjoint H.waveOp ∧
      ∃ ξ, IsStrongSolution (-H.waveOp) T ξ₀ 0 ξ ∧
        (∀ ξ', IsStrongSolution (-H.waveOp) T ξ₀ 0 ξ' → EqOn ξ' ξ (Icc 0 T)) ∧
        ∀ t ∈ Icc 0 T, ‖ξ t‖ = ‖ξ₀‖ := by
  have hS : IsSkewSymm (-H.waveOp) :=
    H.neg_waveOp_isSkewAdjoint.isSkewSymm H.neg_waveOp_isSkewAdjoint.dense_domain
  obtain ⟨ξ, hξ⟩ := hHY ξ₀ h0
  exact ⟨H.dense_domL, H.waveOp_isSkewAdjoint, ξ, hξ,
    fun ξ' hξ' => strongSolution_unique _ hS hξ' hξ, norm_eq_of_isStrongSolution hS hξ⟩

/-- **Thesis Thm 4.6** with the thesis' regularity `ξ ∈ C⁰([0,T];D(L)) ∩ C¹([0,T];W)`
(critic item 5): if the existence hypothesis provides classical solutions
(`WellPosedClassical`, standing for Stone's theorem), the solution is classical, unique among
strong solutions, and conserves energy.

See [QuennevilleBelair2015, Thm 4.6] (regularity class as stated there); existence via
[QuennevilleBelair2015, Thm 4.3]. -/
theorem thm_4_6_classical {T : ℝ} {Adm : (ℝ → Tot W0 W1 W2) → Prop}
    (hHY : WellPosedClassical (-H.waveOp) T Adm) (hAdm : Adm 0) {ξ₀ : Tot W0 W1 W2}
    (h0 : ξ₀ ∈ H.waveOp.domain) :
    ∃ ξ, IsClassicalSolution (-H.waveOp) T ξ₀ 0 ξ ∧
      (∀ ξ', IsStrongSolution (-H.waveOp) T ξ₀ 0 ξ' → EqOn ξ' ξ (Icc 0 T)) ∧
      ∀ t ∈ Icc 0 T, ‖ξ t‖ = ‖ξ₀‖ := by
  have hS : IsSkewSymm (-H.waveOp) :=
    H.neg_waveOp_isSkewAdjoint.isSkewSymm H.neg_waveOp_isSkewAdjoint.dense_domain
  obtain ⟨ξ, hξ⟩ := hHY ξ₀ h0 0 hAdm
  exact ⟨ξ, hξ, fun ξ' hξ' => strongSolution_unique _ hS hξ' hξ.toIsStrongSolution,
    norm_eq_of_isStrongSolution hS hξ.toIsStrongSolution⟩

/-- Thesis Thm 4.6 with existence from a unitary group generated by `-L`
(`UnitaryGroupGenerator`, the conclusion of Stone's theorem), for every horizon `T`.
See [QuennevilleBelair2015, Thm 4.6]; cf. [Pazy1983, §1.10]. -/
theorem thm_4_6_of_unitaryGroupGenerator (G : UnitaryGroupGenerator (-H.waveOp)) (T : ℝ)
    {ξ₀ : Tot W0 W1 W2} (h0 : ξ₀ ∈ H.waveOp.domain) :
    ∃ ξ, IsStrongSolution (-H.waveOp) T ξ₀ 0 ξ ∧
      (∀ ξ', IsStrongSolution (-H.waveOp) T ξ₀ 0 ξ' → EqOn ξ' ξ (Icc 0 T)) ∧
      ∀ t ∈ Icc 0 T, ‖ξ t‖ = ‖ξ₀‖ :=
  (H.thm_4_6 (G.wellPosedHom T) h0).2.2

/-- A unitary group stand-in yields **classical** solutions of the homogeneous problem:
`U t = S t U₀` satisfies `L U(t) = S t (L U₀)`, which is continuous in `t`, so
`U ∈ C⁰([0,T];D(L)) ∩ C¹([0,T];X)` (Thesis Thm 4.3, homogeneous case, with the thesis'
regularity; auxiliary, general `L`).
See [QuennevilleBelair2015, Thm 4.3]; cf. [Pazy1983, §1.10]. -/
theorem _root_.Feec.UnitaryGroupGenerator.wellPosedClassical {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {L : E →ₗ.[ℝ] E}
    (G : UnitaryGroupGenerator L) (T : ℝ) : WellPosedClassical L T (fun F => F = 0) := by
  rintro U₀ hU₀ F rfl
  have hc : ContinuousOn (fun t => G.S t (L ⟨U₀, hU₀⟩)) (Icc 0 T) :=
    (G.continuous_apply _).continuousOn
  have hS : IsStrongSolution L T U₀ 0 fun t => G.S t U₀ := by
    refine ⟨fun t _ => G.mem_domain_apply ⟨U₀, hU₀⟩ t, fun t _ => ?_, ?_⟩
    · simp only [Pi.zero_apply, add_zero]
      rw [G.apply_comm ⟨U₀, hU₀⟩ t]
      exact (G.hasDerivAt_apply ⟨U₀, hU₀⟩ t).hasDerivWithinAt
    · simp [G.map_zero]
  exact ⟨_, hS, ⟨_, hc, fun t _ => G.apply_comm ⟨U₀, hU₀⟩ t⟩,
    ⟨_, hc, fun t _ => by rw [Pi.zero_apply, add_zero]; exact G.apply_comm ⟨U₀, hU₀⟩ t⟩⟩

/-- **Thesis Thm 4.6** with the thesis' regularity, existence coming from a unitary group
generated by `-L` (`UnitaryGroupGenerator`, the conclusion of Stone's theorem): for every
`ξ₀ ∈ D(L)` and every horizon `T`, `ξ' = -Lξ`, `ξ(0) = ξ₀` has a solution in
`C⁰([0,T];D(L)) ∩ C¹([0,T];W)`, unique among strong solutions, conserving energy.
See [QuennevilleBelair2015, Thm 4.6]; cf. [Pazy1983, §1.10]. -/
theorem thm_4_6_classical_of_unitaryGroupGenerator (G : UnitaryGroupGenerator (-H.waveOp))
    (T : ℝ) {ξ₀ : Tot W0 W1 W2} (h0 : ξ₀ ∈ H.waveOp.domain) :
    ∃ ξ, IsClassicalSolution (-H.waveOp) T ξ₀ 0 ξ ∧
      (∀ ξ', IsStrongSolution (-H.waveOp) T ξ₀ 0 ξ' → EqOn ξ' ξ (Icc 0 T)) ∧
      ∀ t ∈ Icc 0 T, ‖ξ t‖ = ‖ξ₀‖ :=
  H.thm_4_6_classical (G.wellPosedClassical T) rfl h0

/-! ### The weak form (4.7)/(4.8) and Thm 4.7 -/

/-- Bridge to the algebraic segment model: `V0 → V1 → W2` with `d0` corestricted to `V1`
(via `map_mem`) and the `W`-inner products on the domains (Thesis §4.4, test space
`V = V0 × V1 × W2` of the weak form). See [QuennevilleBelair2015, §4.4, (4.7)]. -/
def toComplex3 : Complex3 H.d0.domain H.d1.domain W2 where
  d0 := LinearMap.codRestrict H.d1.domain H.d0.toFun H.map_mem
  d1 := H.d1.toFun
  d1_d0 := H.comp_zero

/-- The skew form `a` of (4.7) in terms of `d0`, `d1`:
`a(σ,u,ρ; τ,v,μ) = -(u, d0 τ) + (d0 σ, v) + (ρ, d1 v) - (d1 u, μ)`.
See [QuennevilleBelair2015, §4.4] (the form `a` defined after (4.7)). -/
theorem toComplex3_a (σ : H.d0.domain) (u : H.d1.domain) (ρ : W2) (τ : H.d0.domain)
    (v : H.d1.domain) (μ : W2) :
    H.toComplex3.a σ u ρ τ v μ =
      -⟪(u : W1), H.d0 τ⟫ + ⟪H.d0 σ, (v : W1)⟫ + ⟪ρ, H.d1 v⟫ - ⟪H.d1 u, μ⟫ := rfl

/-- Weak solution of the Hodge wave equation (Thesis (4.7)/(4.8)) on `[0,T]`:
`ξ(t) = (σ, u, ρ)(t) ∈ V = V0 × V1 × W2`, `ξ` differentiable in `W`, and
`(ξ'(t), ψ) + a(ξ(t), ψ) = 0` for all `ψ = (τ, v, μ) ∈ V`, with `ξ(0) = ξ₀`.

Scope (critic item 5): membership in `V` is pointwise and the derivative is pointwise in `W`;
the thesis' class `C⁰([0,T];V) ∩ C¹([0,T];W)` is `IsClassicalWeakSolution`.
See [QuennevilleBelair2015, §4.4, (4.7)–(4.8)]. -/
structure IsWeakSolution (T : ℝ) (ξ₀ : Tot W0 W1 W2) (ξ : ℝ → Tot W0 W1 W2) : Prop where
  mem0 : ∀ t ∈ Icc 0 T, (tot W0 W1 W2 (ξ t)).1 ∈ H.d0.domain
  mem1 : ∀ t ∈ Icc 0 T, (tot W0 W1 W2 (ξ t)).2.1 ∈ H.d1.domain
  deriv : ∀ t (ht : t ∈ Icc 0 T), ∃ ξ' : Tot W0 W1 W2, HasDerivWithinAt ξ ξ' (Icc 0 T) t ∧
    ∀ (τ : H.d0.domain) (v : H.d1.domain) (μ : W2),
      ⟪ξ', (tot W0 W1 W2).symm ((τ : W0), (v : W1), μ)⟫ +
        H.toComplex3.a ⟨_, mem0 t ht⟩ ⟨_, mem1 t ht⟩ (tot W0 W1 W2 (ξ t)).2.2 τ v μ = 0
  init : ξ 0 = ξ₀

/-- Weak solution in the thesis' class `C⁰([0,T];V) ∩ C¹([0,T];W)` (Thesis §4.4):
additionally `t ↦ d0 σ(t)`, `t ↦ d1 u(t)` and `t ↦ ξ'(t)` are continuous on `[0,T]`
(continuity of `σ, u, ρ` in `W` follows from differentiability).
See [QuennevilleBelair2015, §4.4, (4.7)–(4.8)]. -/
structure IsClassicalWeakSolution (T : ℝ) (ξ₀ : Tot W0 W1 W2) (ξ : ℝ → Tot W0 W1 W2) : Prop
    extends H.IsWeakSolution T ξ₀ ξ where
  contV : ∃ G0 : ℝ → W1, ∃ G1 : ℝ → W2, ContinuousOn G0 (Icc 0 T) ∧ ContinuousOn G1 (Icc 0 T) ∧
    ∀ t (ht : t ∈ Icc 0 T), H.d0 ⟨_, mem0 t ht⟩ = G0 t ∧ H.d1 ⟨_, mem1 t ht⟩ = G1 t
  c1 : ∃ D : ℝ → Tot W0 W1 W2, ContinuousOn D (Icc 0 T) ∧
    ∀ t ∈ Icc 0 T, HasDerivWithinAt ξ (D t) (Icc 0 T) t

/-- Antisymmetry of the weak form, `a(ψ, ψ) = 0` (Thesis §4.4, used for weak uniqueness;
not stated in the thesis). Cf. [QuennevilleBelair2015, §4.4, after (4.8)]. -/
theorem a_self (σ : H.d0.domain) (u : H.d1.domain) (ρ : W2) :
    H.toComplex3.a σ u ρ σ u ρ = 0 :=
  H.toComplex3.a_self σ u ρ

/-- **Thesis Thm 4.7, first bullet** (strong ⇒ weak), pointwise version: a strong solution of
`ξ' = -Lξ` is a weak solution (4.8) with the same initial data.

Thesis gap: "easily follows" — the three identities use `(d0* u, τ) = (u, d0 τ)` and
`(d1* ρ, v) = (ρ, d1 v)`. See [QuennevilleBelair2015, Thm 4.7] (first bullet and proof). -/
theorem isWeakSolution_of_isStrongSolution {T : ℝ} {ξ₀ : Tot W0 W1 W2} {ξ : ℝ → Tot W0 W1 W2}
    (hξ : IsStrongSolution (-H.waveOp) T ξ₀ 0 ξ) : H.IsWeakSolution T ξ₀ ξ where
  mem0 t ht := (((mem_domL H).1 (hξ.mem t ht)).1)
  mem1 t ht := (Submodule.mem_inf.1 ((mem_domL H).1 (hξ.mem t ht)).2.1).1
  deriv t ht := by
    refine ⟨_, hξ.deriv t ht, fun τ v μ => ?_⟩
    have hx : ξ t ∈ H.waveOp.domain := hξ.mem t ht
    have hc := tot_waveOp H ⟨ξ t, hx⟩
    rw [Pi.zero_apply, add_zero, tot_inner, LinearPMap.neg_apply, _root_.map_neg,
      LinearEquiv.apply_symm_apply, toComplex3_a]
    change ⟪-(tot W0 W1 W2 (H.waveOp ⟨ξ t, hx⟩)).1, _⟫ +
      ⟪-(tot W0 W1 W2 (H.waveOp ⟨ξ t, hx⟩)).2.1, _⟫ +
      ⟪-(tot W0 W1 W2 (H.waveOp ⟨ξ t, hx⟩)).2.2, _⟫ + _ = _
    rw [hc]
    have a0 := adjoint_isFormalAdjoint H.dense0 (H.prV1s ⟨ξ t, hx⟩) τ
    have a1 := adjoint_isFormalAdjoint H.dense1 (H.prV2s ⟨ξ t, hx⟩) v
    simp only [coe_prV1s, coe_prV2s] at a0 a1
    simp only [neg_neg, inner_neg_left, inner_add_left]
    have e0 : H.pr0 ⟨ξ t, hx⟩ = ⟨_, ((mem_domL H).1 hx).1⟩ := rfl
    have e1 : H.prV1 ⟨ξ t, hx⟩ = ⟨_, (Submodule.mem_inf.1 ((mem_domL H).1 hx).2.1).1⟩ := rfl
    rw [e0, e1] at *
    linarith
  init := hξ.init

/-- **Thesis Thm 4.7, first bullet** (strong ⇒ weak) with the thesis' regularity: a classical
strong solution (`ξ ∈ C⁰([0,T];D(L)) ∩ C¹([0,T];W)`) is a weak solution in
`C⁰([0,T];V) ∩ C¹([0,T];W)`.

Thesis gap: "it certainly belongs to `C⁰([0,T], V)`" needs `d0 σ ⟂ d1* ρ` (`norm_embed`): here
`d0 σ(t) = P (d0 σ(t) + d1* ρ(t))` with `P` the orthogonal projection onto `cl(range d0)`,
so continuity of `Lξ` gives continuity of `d0 σ`.
See [QuennevilleBelair2015, Thm 4.7] (first bullet and proof). -/
theorem isClassicalWeakSolution_of_isClassicalSolution {T : ℝ} {ξ₀ : Tot W0 W1 W2}
    {ξ : ℝ → Tot W0 W1 W2} (hξ : IsClassicalSolution (-H.waveOp) T ξ₀ 0 ξ) :
    H.IsClassicalWeakSolution T ξ₀ ξ where
  toIsWeakSolution := H.isWeakSolution_of_isStrongSolution hξ.toIsStrongSolution
  contV := by
    obtain ⟨G, hGc, hG⟩ := hξ.graph
    set K := (LinearMap.range H.d0.toFun).topologicalClosure
    have : CompleteSpace K := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
    refine ⟨fun t => K.starProjection (-(tot W0 W1 W2 (G t)).2.1),
      fun t => (tot W0 W1 W2 (G t)).2.2,
      (K.starProjection.continuous.comp_continuousOn
        ((totL.continuous.comp_continuousOn hGc).snd.fst.neg)),
      (totL.continuous.comp_continuousOn hGc).snd.snd, fun t ht => ?_⟩
    have hx : ξ t ∈ H.waveOp.domain := hξ.mem t ht
    have hc := tot_waveOp H ⟨ξ t, hx⟩
    have hGt := congrArg (tot W0 W1 W2) (hG t ht)
    rw [LinearPMap.neg_apply, _root_.map_neg] at hGt
    have e0 : H.pr0 ⟨ξ t, hx⟩ = ⟨_, ((mem_domL H).1 hx).1⟩ := rfl
    have e1 : H.prV1 ⟨ξ t, hx⟩ = ⟨_, (Submodule.mem_inf.1 ((mem_domL H).1 hx).2.1).1⟩ := rfl
    rw [e0, e1] at hc
    beta_reduce
    rw [← hGt, hc]
    simp only [Prod.neg_mk, neg_neg, and_true]
    have hm : H.d0 ⟨(tot W0 W1 W2 (ξ t)).1, ((mem_domL H).1 hx).1⟩ ∈ K :=
      Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ _)
    have hn : K.starProjection (H.d1† (H.prV2s ⟨ξ t, hx⟩)) = 0 := by
      rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_closure,
        H.orthogonal_range_d0]
      exact H.range_adjoint_d1_le (LinearMap.mem_range_self _ _)
    rw [_root_.map_add, (K.starProjection_eq_self_iff).2 hm, hn, add_zero]
  c1 := by
    obtain ⟨G, hGc, hG⟩ := hξ.c1
    exact ⟨G, hGc, fun t ht => hG t ht ▸ hξ.deriv t ht⟩

/-- **Uniqueness of weak solutions** (Thesis §4.4, after (4.8)): two weak solutions with the
same initial value agree on `[0,T]`.

Thesis gap: "taking `τ = σ1 - σ2`, … we get `‖σ1 - σ2‖² + … = 0`" skips the energy argument:
testing with `e(t) = ξ1(t) - ξ2(t)` gives `(e', e) + a(e, e) = 0`, `a(e, e) = 0`
(`a_self`), so `d/dt ‖e‖² = 0` and `e ≡ 0` from `e(0) = 0` (`Feec.energy_zero`). Only pointwise
membership `e(t) ∈ V` is used, so this is stronger than the thesis' statement.
See [QuennevilleBelair2015, §4.4, paragraph after (4.8)]. -/
theorem weak_unique {T : ℝ} {ξ₀ : Tot W0 W1 W2} {ξ₁ ξ₂ : ℝ → Tot W0 W1 W2}
    (h₁ : H.IsWeakSolution T ξ₀ ξ₁) (h₂ : H.IsWeakSolution T ξ₀ ξ₂) : EqOn ξ₁ ξ₂ (Icc 0 T) := by
  have hcont : ∀ {ξ}, H.IsWeakSolution T ξ₀ ξ → ContinuousOn ξ (Icc 0 T) := fun h t ht =>
    (h.deriv t ht).choose_spec.1.continuousWithinAt
  have key := energy_zero_of_exists (e := fun t => ξ₁ t - ξ₂ t) ((hcont h₁).sub (hcont h₂))
    (fun t ht => by
      have ht' := Ico_subset_Icc_self ht
      obtain ⟨ξ₁', hd₁, hw₁⟩ := h₁.deriv t ht'
      obtain ⟨ξ₂', hd₂, hw₂⟩ := h₂.deriv t ht'
      refine ⟨ξ₁' - ξ₂', (hd₁.sub hd₂).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht), ?_⟩
      set s₁ : H.d0.domain := ⟨_, h₁.mem0 t ht'⟩
      set s₂ : H.d0.domain := ⟨_, h₂.mem0 t ht'⟩
      set w₁ : H.d1.domain := ⟨_, h₁.mem1 t ht'⟩
      set w₂ : H.d1.domain := ⟨_, h₂.mem1 t ht'⟩
      set r₁ := (tot W0 W1 W2 (ξ₁ t)).2.2
      set r₂ := (tot W0 W1 W2 (ξ₂ t)).2.2
      have he : (tot W0 W1 W2).symm (((s₁ - s₂ : H.d0.domain) : W0),
          ((w₁ - w₂ : H.d1.domain) : W1), r₁ - r₂) = ξ₁ t - ξ₂ t := by
        apply (tot W0 W1 W2).injective
        rw [LinearEquiv.apply_symm_apply, _root_.map_sub]
        rfl
      have k₁ := hw₁ (s₁ - s₂) (w₁ - w₂) (r₁ - r₂)
      have k₂ := hw₂ (s₁ - s₂) (w₁ - w₂) (r₁ - r₂)
      rw [he, toComplex3_a] at k₁ k₂
      rw [inner_sub_left, inner_sub_right, inner_sub_right]
      simp only [LinearPMap.map_sub, Submodule.coe_sub, inner_sub_right] at k₁ k₂
      linarith [real_inner_comm (w₁ : W1) (H.d0 s₁), real_inner_comm (w₁ : W1) (H.d0 s₂),
        real_inner_comm (w₂ : W1) (H.d0 s₁), real_inner_comm (w₂ : W1) (H.d0 s₂),
        real_inner_comm r₁ (H.d1 w₁), real_inner_comm r₁ (H.d1 w₂),
        real_inner_comm r₂ (H.d1 w₁), real_inner_comm r₂ (H.d1 w₂)])
    (by simp [h₁.init, h₂.init])
  intro t ht
  exact sub_eq_zero.1 (key t ht)

/-- Transfer of a strong solution along equality on `[0,T]` (auxiliary). -/
theorem _root_.Feec.IsStrongSolution.of_eqOn {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {L : E →ₗ.[ℝ] E} {T : ℝ} {U₀ : E} {F U V : ℝ → E} (hU : IsStrongSolution L T U₀ F U)
    (h : EqOn V U (Icc 0 T)) (h0 : V 0 = U₀) : IsStrongSolution L T U₀ F V where
  mem t ht := h ht ▸ hU.mem t ht
  deriv t ht := by
    have e : (⟨V t, h ht ▸ hU.mem t ht⟩ : L.domain) = ⟨U t, hU.mem t ht⟩ := Subtype.ext (h ht)
    rw [e]
    exact (hU.deriv t ht).congr h (h ht)
  init := h0

/-- **Thesis Thm 4.7, second bullet** (weak ⇒ strong): under the existence hypothesis of
Thm 4.6, a weak solution with initial value in `D(L)` is a strong solution.

Correction: the thesis' proof cites "Theorem 4.7" itself for the existence of a strong
solution; it is Thm 4.6 (`thm_4_6`, here through its existence hypothesis `WellPosedHom`).
See [QuennevilleBelair2015, Thm 4.7] (second bullet and proof). -/
theorem weak_imp_strong {T : ℝ} (hHY : WellPosedHom (-H.waveOp) T) {ξ₀ : Tot W0 W1 W2}
    (h0 : ξ₀ ∈ H.waveOp.domain) {ξ : ℝ → Tot W0 W1 W2} (hξ : H.IsWeakSolution T ξ₀ ξ) :
    IsStrongSolution (-H.waveOp) T ξ₀ 0 ξ := by
  obtain ⟨ξs, hs⟩ := hHY ξ₀ h0
  exact hs.of_eqOn (H.weak_unique hξ (H.isWeakSolution_of_isStrongSolution hs)) hξ.init

/-- **Thesis Thm 4.7, second bullet**, with the thesis' regularity: if the existence hypothesis
provides classical solutions, a weak solution with data in `D(L)` lies in
`C⁰([0,T];D(L)) ∩ C¹([0,T];W)` and solves (4.4).
See [QuennevilleBelair2015, Thm 4.7] (second bullet). -/
theorem weak_imp_classical {T : ℝ} {Adm : (ℝ → Tot W0 W1 W2) → Prop}
    (hHY : WellPosedClassical (-H.waveOp) T Adm) (hAdm : Adm 0) {ξ₀ : Tot W0 W1 W2}
    (h0 : ξ₀ ∈ H.waveOp.domain) {ξ : ℝ → Tot W0 W1 W2} (hξ : H.IsWeakSolution T ξ₀ ξ) :
    IsClassicalSolution (-H.waveOp) T ξ₀ 0 ξ := by
  obtain ⟨ξs, hs⟩ := hHY ξ₀ h0 0 hAdm
  have h := H.weak_unique hξ (H.isWeakSolution_of_isStrongSolution hs.toIsStrongSolution)
  have hS := hs.toIsStrongSolution.of_eqOn h hξ.init
  refine ⟨hS, ?_, ?_⟩
  · obtain ⟨G, hGc, hG⟩ := hs.graph
    refine ⟨G, hGc, fun t ht => ?_⟩
    rw [← hG t ht]
    exact congrArg _ (Subtype.ext (h ht))
  · obtain ⟨G, hGc, hG⟩ := hs.c1
    refine ⟨G, hGc, fun t ht => ?_⟩
    rw [← hG t ht]
    exact congrArg (· + _) (congrArg _ (Subtype.ext (h ht)))

/-- **Thesis Thm 4.7** (corrected): under the existence hypothesis of Thm 4.6, for initial data
in `D(L)`, strong solutions of (4.4) and weak solutions of (4.7)/(4.8) coincide.

Correction: the proof uses Thm 4.6 (not Thm 4.7, as the thesis cites).
See [QuennevilleBelair2015, Thm 4.7]. -/
theorem thm_4_7 {T : ℝ} (hHY : WellPosedHom (-H.waveOp) T) {ξ₀ : Tot W0 W1 W2}
    (h0 : ξ₀ ∈ H.waveOp.domain) (ξ : ℝ → Tot W0 W1 W2) :
    IsStrongSolution (-H.waveOp) T ξ₀ 0 ξ ↔ H.IsWeakSolution T ξ₀ ξ :=
  ⟨H.isWeakSolution_of_isStrongSolution, H.weak_imp_strong hHY h0⟩

/-- **Thesis Thm 4.7** with the thesis' regularity classes: under classical existence,
for data in `D(L)`, classical strong solutions (`C⁰(D(L)) ∩ C¹(W)`) and classical weak
solutions (`C⁰(V) ∩ C¹(W)`) coincide. See [QuennevilleBelair2015, Thm 4.7]. -/
theorem thm_4_7_classical {T : ℝ} {Adm : (ℝ → Tot W0 W1 W2) → Prop}
    (hHY : WellPosedClassical (-H.waveOp) T Adm) (hAdm : Adm 0) {ξ₀ : Tot W0 W1 W2}
    (h0 : ξ₀ ∈ H.waveOp.domain) (ξ : ℝ → Tot W0 W1 W2) :
    IsClassicalSolution (-H.waveOp) T ξ₀ 0 ξ ↔ H.IsClassicalWeakSolution T ξ₀ ξ :=
  ⟨H.isClassicalWeakSolution_of_isClassicalSolution,
    fun h => H.weak_imp_classical hHY hAdm h0 h.toIsWeakSolution⟩

/-! ### Non-vacuity of the existence hypothesis (critic item 6) -/

section FiniteDim

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- In finite dimensions a dense subspace is everything (auxiliary). -/
theorem eq_top_of_dense (p : Submodule ℝ E) (h : Dense (p : Set E)) : p = ⊤ := by
  rw [← (p.closed_of_finiteDimensional).submodule_topologicalClosure_eq]
  exact (Submodule.dense_iff_topologicalClosure_eq_top).1 h

/-- In finite dimensions an everywhere-defined operator is a bounded operator (auxiliary). -/
theorem exists_eq_bddOp (L : E →ₗ.[ℝ] E) (hdom : L.domain = ⊤) :
    ∃ A : E →L[ℝ] E, L = bddOp A := by
  refine ⟨LinearMap.toContinuousLinearMap
    (L.toFun ∘ₗ (LinearEquiv.ofTop L.domain hdom).symm.toLinearMap), ?_⟩
  refine LinearPMap.ext hdom fun x hx _ => ?_
  change L ⟨x, hx⟩ = L ((LinearEquiv.ofTop L.domain hdom).symm x)
  congr 1

end FiniteDim

variable [FiniteDimensional ℝ W0] [FiniteDimensional ℝ W1] [FiniteDimensional ℝ W2]

/-- **Non-vacuity of the hypotheses of Thm 4.6/4.7**: for every Hilbert complex of
finite-dimensional spaces the classical existence hypothesis of `thm_4_6_classical` and
`thm_4_7_classical` holds (with continuous forcing), via `exp(-tL)` and Duhamel's formula.
Hypotheses of [QuennevilleBelair2015, Thm 4.3] as used in Thms 4.6/4.7 (no counterpart in the
thesis). -/
theorem wellPosedClassical_neg_waveOp (T : ℝ) :
    WellPosedClassical (-H.waveOp) T (fun F => ContinuousOn F (Icc 0 T)) := by
  obtain ⟨A, hA⟩ := exists_eq_bddOp (-H.waveOp) (eq_top_of_dense _ H.dense_domL)
  rw [hA]
  exact wellPosedClassical_bddOp A T

/-- **Non-vacuity of the hypothesis of Thm 4.6/4.7** (`WellPosedHom`), finite-dimensional
case. -/
theorem wellPosedHom_neg_waveOp (T : ℝ) : WellPosedHom (-H.waveOp) T := by
  obtain ⟨A, hA⟩ := exists_eq_bddOp (-H.waveOp) (eq_top_of_dense _ H.dense_domL)
  rw [hA]
  exact wellPosedHom_bddOp A T

end Feec.HilbertComplex2

namespace Feec.HodgeWaveExample

open HilbertComplex2

/-- A concrete Hilbert complex `ℝ --id--> ℝ --0--> ℝ` (auxiliary, for non-vacuity). -/
def idComplex : HilbertComplex2 ℝ ℝ ℝ where
  d0 := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).toPMap ⊤
  d1 := (0 : ℝ →ₗ[ℝ] ℝ).toPMap ⊤
  dense0 := by simp [dense_univ]
  dense1 := by simp [dense_univ]
  closed0 := Submodule.closed_of_finiteDimensional _
  closed1 := Submodule.closed_of_finiteDimensional _
  map_mem _ := Submodule.mem_top
  comp_zero _ := rfl

/-- **The hypotheses of Thm 4.6/4.7 are satisfiable with a nonzero Hodge wave operator**
(critic item 6): for `ℝ --id--> ℝ --0--> ℝ`, `WellPosedHom (-L) T` and the classical existence
hypothesis hold for every `T`, and `L ≠ 0` on `D(L)`. Witness for the hypotheses of
[QuennevilleBelair2015, Thms 4.6 and 4.7] (no counterpart in the thesis). -/
theorem nonvacuous :
    (∃ x : idComplex.waveOp.domain, idComplex.waveOp x ≠ 0) ∧
      ∀ T, WellPosedHom (-idComplex.waveOp) T ∧
        WellPosedClassical (-idComplex.waveOp) T (fun F => ContinuousOn F (Icc 0 T)) := by
  refine ⟨⟨idComplex.mkDom ⟨1, Submodule.mem_top⟩ 0 0, fun h => ?_⟩, fun T =>
    ⟨idComplex.wellPosedHom_neg_waveOp T, idComplex.wellPosedClassical_neg_waveOp T⟩⟩
  have := congrArg (fun x => (tot ℝ ℝ ℝ x).2.1) h
  simp only [tot_waveOp_mkDom, _root_.map_zero, Prod.snd_zero, Prod.fst_zero] at this
  rw [LinearPMap.map_zero, add_zero] at this
  exact one_ne_zero this

end Feec.HodgeWaveExample
