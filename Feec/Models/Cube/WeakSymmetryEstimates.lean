module

public import Feec.Models.Cube.WeakSymmetryComplex
public import Feec.Models.Cube.SmoothingEstimates

/-!
# The weak-symmetry maps on the Freudenthal meshes of the cube: Props 5.8 and 5.9

On the level-`(N + 1)` Freudenthal meshes of `Q = (0, ½)³` (`Feec.Models.Cube.FEM.mesh 3 N`,
mesh size `h_N = 1 / (2 (N + 1))`), for the elements of Table 5.1 of [QuennevilleBelair2015]
(`P₂Λ⁰ ⊗ ℝ³ → P₂⁻Λ¹ ⊗ ℝ³` and the lowest-order Nédélec and Raviart–Thomas spaces), with constants
independent of `N`:

* **Prop 5.8, corrected** (`norm_glue_bggS0h_le`, `norm_glue_bggS1h_le`): `‖S₀,ₕψ‖ ≤ C ‖ψ‖` and
  `‖S₁,ₕv‖ ≤ C ‖v‖` in `L²(Q)`. The thesis' proof uses global `ℓ¹` sums of DOFs, which are not
  uniformly equivalent to the `L²` norm (`docs/audit.json`); the proof here is local: on each
  simplex `S_h = Π' S`, and `Π'` is `L²`-bounded on polynomial fields uniformly on the homothetic
  copies `t + h K_σ` of the Kuhn simplices (`exists_local_bound`).
* **Prop 5.9(1)** (`norm_sub_glue_bggS0h_le`): `‖(I − Π¹) S⁰ψ‖ ≤ C h ‖∇ψ‖` on `P₂Λ⁰ ⊗ ℝ³`
  (the kernel lemma `Feec.FiniteElement.exists_formL2Sq_sub_polyMinusInterp_le_formGradL2Sq`).
* **Strong approximation** (`norm_sub_globalInterp_coordWedge_le`): `‖(I − Π) S u‖ ≤ C h sup ‖Du‖`
  for `C¹` vector fields `u`, for `S⁰` and `S¹`.
* **Prop 5.9(2) is false** (`exists_counterexample_prop59_two`): there is `c > 0` such that on
  every mesh there is `v ∈ P₂⁻Λ̊¹ ⊗ ℝ³`, `v ≠ 0`, with `‖(I − Π²) S¹ v‖ ≥ c ‖v‖_{H(curl)}`; so the
  hypothesis `happ1` of `Feec.BGG.Discrete.error_estimate` (an `O(h)` bound) fails for these
  elements. The field is `v = grad φ` row-wise, `φ = (0, 0, Π̃⁰ f_N)` with `f_N` a bump at the mesh
  scale, quadratic on one simplex `T₀`: `curl v = 0`, while on `T₀` the field `S¹ v = −d(f_N dx₃)`
  is affine and not a Raviart–Thomas field.

**The canonical interpolants.** The interpolants of the global trimmed families on a mesh simplex
`T` are the interpolants `Feec.FiniteElement.polyMinusInterp` of `LocalDof` for the lexicographic
vertex order (`Feec.FiniteElement.PolySeq.localInterp_eq_polyMinusInterp`); the mesh simplices
are `t + h_N K_σ` with `K_σ` the Kuhn simplices with lexicographically ordered vertices
(`lexSimplex`, `mesh_simplex_eq_lex`), so the local estimates of
`Feec.FiniteElement.PolyInterpolation` hold with constants uniform over the `3!` simplices `K_σ`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.3, Props 5.8–5.9, Table 5.1
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.2 (canonical interpolants), §5.4 (scaling arguments)
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], Thm 3.1.4
  (interpolation error on affine-equivalent families)
* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]
* [H. W. Kuhn, *Some combinatorial lemmas in topology*][Kuhn1960]
-/

open scoped InnerProductSpace ContDiff
open MeasureTheory Set Finset Filter

@[expose] public noncomputable section

namespace Feec.Models.Cube.WeakSymmetry

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex ExteriorFibre
  Feec.Models.Cube.FEM

variable {n : ℕ}

/-! ### Reference simplices with lexicographically ordered vertices -/

theorem exists_perm_lexEnum (K : Affine.Simplex ℝ (Fin n → ℝ) n) :
    ∃ π : Equiv.Perm (Fin (n + 1)), lexEnum (vertexSet K) n = K.points ∘ π :=
  exists_perm_comp_eq (lexEnum_injective (card_vertexSet K)) K.independent.injective
    (by rw [range_lexEnum (card_vertexSet K), coe_vertexSet])

/-- `K` with its vertices in lexicographic order. -/
def lexSimplex (K : Affine.Simplex ℝ (Fin n → ℝ) n) : Affine.Simplex ℝ (Fin n → ℝ) n :=
  K.reindex (exists_perm_lexEnum K).choose.symm

theorem lexSimplex_points (K : Affine.Simplex ℝ (Fin n → ℝ) n) :
    (lexSimplex K).points = lexEnum (vertexSet K) n := by
  rw [(exists_perm_lexEnum K).choose_spec]
  rfl

theorem vertexSet_lexSimplex (K : Affine.Simplex ℝ (Fin n → ℝ) n) :
    vertexSet (lexSimplex K) = vertexSet K := by
  classical
  change Finset.univ.image (lexSimplex K).points = _
  rw [lexSimplex_points, image_lexEnum (card_vertexSet K)]

theorem vertexSet_mapEquiv_lexSimplex (K : Affine.Simplex ℝ (Fin n → ℝ) n) (t : Fin n → ℝ)
    {h : ℝ} (hh : h ≠ 0) :
    vertexSet (mapEquiv (boxMap t h hh) (lexSimplex K)) = vertexSet (mapEquiv (boxMap t h hh) K) := by
  rw [vertexSet_mapEquiv_boxMap, vertexSet_mapEquiv_boxMap, vertexSet_lexSimplex]

theorem points_mapEquiv_lexSimplex (K : Affine.Simplex ℝ (Fin n → ℝ) n) (t : Fin n → ℝ)
    {h : ℝ} (hh : 0 < h) :
    (mapEquiv (boxMap t h hh.ne') (lexSimplex K)).points =
      lexEnum (vertexSet (mapEquiv (boxMap t h hh.ne') K)) n := by
  rw [points_mapEquiv_boxMap, lexSimplex_points, vertexSet_mapEquiv_boxMap,
    lexEnum_image_affine_scalarMat hh t (card_vertexSet K)]

theorem closedInterior_mapEquiv_lexSimplex (K : Affine.Simplex ℝ (Fin n → ℝ) n) (t : Fin n → ℝ)
    {h : ℝ} (hh : h ≠ 0) :
    (mapEquiv (boxMap t h hh) (lexSimplex K)).closedInterior =
      (mapEquiv (boxMap t h hh) K).closedInterior := by
  rw [← convexHull_vertexSet, ← convexHull_vertexSet, vertexSet_mapEquiv_lexSimplex]

/-- **The interpolant of `P₁⁻Λᵏ⁺¹` on `T = t + h K`** is `polyMinusInterp` on the homothetic image
of the lexicographically ordered `K`. -/
theorem localInterp_lowestOrder_eq (K : Affine.Simplex ℝ (Fin n → ℝ) n) (t : Fin n → ℝ)
    {h : ℝ} (hh : 0 < h) {k : ℕ} (hk : k + 1 ≤ n) (w : contDegForms n (k + 1)) :
    (((polyElement n PolySeq.lowestOrder).localInterp (mapEquiv (boxMap t h hh.ne') K) (k + 1)
        ⟨w, w.2.1⟩ : (polyElement n PolySeq.lowestOrder).space _ (k + 1)) : FormField n) =
      (polyMinusInterp (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') (lexSimplex K)))
        (PolySeq.lowestOrder.one_le_deg (k + 1)) hk w : FormField n) := by
  have hpts := points_mapEquiv_lexSimplex K t hh
  refine PolySeq.localInterp_eq_polyMinusInterp PolySeq.lowestOrder (by simp [PolySeq.lowestOrder]) hk _
    (q := (mapEquiv (boxMap t h hh.ne') (lexSimplex K)).points) ?_ ?_ _ w
  · rw [hpts]; exact strictMono_lexEnum (card_vertexSet _)
  · intro x hx
    rw [hpts]
    exact exists_lexEnum_eq_of_mem_vertexSet _ hx

/-! ### Local bounds for the canonical interpolant on homothetic simplices -/

section LocalBounds

variable {r k : ℕ}

/-- **`L²`-boundedness of the canonical interpolant on polynomial fields**: for `T = t + h K`,
`‖Π_T u‖_{L²(T)} ≤ C ‖u‖_{L²(T)}` on `P_rΛᵏ`, with `Π_T` the interpolant of `P_{r'}⁻Λᵏ`
(`r' ≤ r`) and `C` depending only on `K`, `r`, `r'`, `k` (a finite-dimensional bound on `K`,
transported by the naturality of `Π` under homotheties). -/
theorem exists_formL2Sq_polyMinusInterp_le (K : Affine.Simplex ℝ (Fin n → ℝ) n) {r' : ℕ}
    (hr' : 1 ≤ r') (hk : k ≤ n) (hrr : r' ≤ r) :
    ∃ C, 0 ≤ C ∧ ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {u : FormField n}
      (hu : u ∈ polySpace n r k),
      √(formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior
        (polyMinusInterp (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') K)) hr' hk
          ⟨u, polySpace_le_contDegForms r k hu⟩ : FormField n)) ≤
        C * √(formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior u) := by
  set P := polyMinusInterpOn K hr' hk hrr (r := r)
  have hK := K.isCompact_closedInterior
  set D := l2EmbedOf (polySpace n r k) (polySpace_le_contForms r k) hK
  have hD : Function.Injective D :=
    l2EmbedOf_injective_of_le_polySpace le_rfl hK (interior_closedInterior_nonempty K)
  obtain ⟨C, hC0, hC⟩ := exists_norm_le_mul_norm_of_ker_le D (D ∘ₗ P) (by
    rw [LinearMap.ker_eq_bot.2 hD]; exact bot_le)
  refine ⟨C, hC0, fun {h} hh t u hu => ?_⟩
  set v : polySpace n r k := ⟨affinePullback (scalarMat n h) t u,
    affinePullback_mem_polySpace_scalarMat h t hu⟩
  have hdeg := isDeg_of_mem_polySpace hu
  set w : FormField n := (polyMinusInterp (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') K))
    hr' hk ⟨u, polySpace_le_contDegForms r k hu⟩ : FormField n)
  have hwdeg : ∀ x, IsDeg k (w x) := isDeg_of_mem_polySpace (polyMinusSpace_le_polySpace hr'
      (mem_polyMinusSpace_of_mem_localPolyMinusSpace (isUnit_det_edgeMatrix _)
        (polyMinusInterp (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') K)) hr' hk
          ⟨u, polySpace_le_contDegForms r k hu⟩).2))
  have hnat : affinePullback (scalarMat n h) t w = (P v : FormField n) :=
    affinePullback_polyMinusInterp (isUnit_det_edgeMatrix K)
      (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') K)) (scalarMat n h) t
      (points_mapEquiv_boxMap K t hh.ne') hr' hk ⟨u, polySpace_le_contDegForms r k hu⟩
  have hhk : 0 < h ^ k := pow_pos hh k
  have hn : 0 ≤ h ^ n := pow_nonneg hh.le n
  have h1 : √(h ^ n) * ‖D (P v)‖ =
      h ^ k * √(formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior w) := by
    rw [norm_l2EmbedOf, ← hnat]
    exact sqrt_mul_sqrt_eq_of_mul_eq hn hhk.le (formL2Sq_affinePullback_scalarMat K hh t hwdeg)
  have h2 : √(h ^ n) * ‖D v‖ =
      h ^ k * √(formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior u) := by
    rw [norm_l2EmbedOf]
    exact sqrt_mul_sqrt_eq_of_mul_eq hn hhk.le (formL2Sq_affinePullback_scalarMat K hh t hdeg)
  refine le_of_mul_le_mul_left ?_ hhk
  calc h ^ k * √(formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior w)
      = √(h ^ n) * ‖D (P v)‖ := h1.symm
    _ ≤ √(h ^ n) * (C * ‖D v‖) :=
        mul_le_mul_of_nonneg_left (hC v) (Real.sqrt_nonneg _)
    _ = C * (√(h ^ n) * ‖D v‖) := by ring
    _ = h ^ k * (C * √(formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior u)) := by
        rw [h2]; ring

/-- `exists_formL2Sq_polyMinusInterp_le` with one constant for finitely many reference
simplices. -/
theorem exists_formL2Sq_polyMinusInterp_le_uniform {ι : Type*} [Finite ι]
    (K : ι → Affine.Simplex ℝ (Fin n → ℝ) n) {r' : ℕ} (hr' : 1 ≤ r') (hk : k ≤ n)
    (hrr : r' ≤ r) :
    ∃ C, 0 ≤ C ∧ ∀ i, ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {u : FormField n}
      (hu : u ∈ polySpace n r k),
      √(formL2Sq (mapEquiv (boxMap t h hh.ne') (K i)).closedInterior
        (polyMinusInterp (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') (K i))) hr' hk
          ⟨u, polySpace_le_contDegForms r k hu⟩ : FormField n)) ≤
        C * √(formL2Sq (mapEquiv (boxMap t h hh.ne') (K i)).closedInterior u) := by
  classical
  have := Fintype.ofFinite ι
  choose C hC0 hC using fun i => exists_formL2Sq_polyMinusInterp_le (K i) hr' hk hrr (r := r)
  refine ⟨∑ i, C i, Finset.sum_nonneg fun i _ => hC0 i, fun i {h} hh t u hu =>
    (hC i hh t hu).trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := C)
      (fun j _ => hC0 j) (Finset.mem_univ i)) (Real.sqrt_nonneg _))⟩

/-- The kernel lemma `exists_formL2Sq_sub_polyMinusInterp_le_formGradL2Sq` with one constant for
finitely many reference simplices. -/
theorem exists_formL2Sq_sub_polyMinusInterp_le_uniform {ι : Type*} [Finite ι]
    (K : ι → Affine.Simplex ℝ (Fin n → ℝ) n) {r' : ℕ} (hr' : 1 ≤ r') (hk : k ≤ n)
    (hrr : r' ≤ r) :
    ∃ C, 0 ≤ C ∧ ∀ i, ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {u : FormField n}
      (hu : u ∈ polySpace n r k),
      √(formL2Sq (mapEquiv (boxMap t h hh.ne') (K i)).closedInterior
        (u - (polyMinusInterp (isUnit_det_edgeMatrix (mapEquiv (boxMap t h hh.ne') (K i))) hr' hk
          ⟨u, polySpace_le_contDegForms r k hu⟩ : FormField n))) ≤
        C * h * √(formGradL2Sq (mapEquiv (boxMap t h hh.ne') (K i)).closedInterior u) := by
  classical
  have := Fintype.ofFinite ι
  choose C hC0 hC using fun i =>
    exists_formL2Sq_sub_polyMinusInterp_le_formGradL2Sq (K i) hr' hk hrr (r := r)
  refine ⟨∑ i, C i, Finset.sum_nonneg fun i _ => hC0 i, fun i {h} hh t u hu =>
    (hC i hh t hu).trans ?_⟩
  have hCi : C i ≤ ∑ j, C j := Finset.single_le_sum (f := C) (fun j _ => hC0 j) (Finset.mem_univ i)
  gcongr

end LocalBounds

/-! ### Norms of glued fields -/

section Glue

/-- **The squared norm of a glued field is the sum of the local squared norms**, on meshes whose
open simplices lie in the meshed domain (the reverse inequality of
`Feec.FiniteElement.norm_sq_pieceL2_le`). -/
theorem norm_sq_pieceL2_eq (M : SimplicialMesh n)
    (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain) {ι : Type*} [Fintype ι]
    (v : Affine.Simplex ℝ (Fin n → ℝ) n → ι → (Fin n → ℝ) → ℝ)
    (hv : ∀ T ∈ M.simplices, ∀ i, Continuous (v T i)) :
    ‖pieceL2 M M.domain v hv‖ ^ 2 =
      ∑ T ∈ M.simplices, ∑ i, ∫ x in T.closedInterior, (v T i x) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_sq_eq_integral_sq]
  have hint' : ∀ T ∈ M.simplices, Integrable
      ((interior T.closedInterior).indicator fun x => (v T i x) ^ 2) := fun T hT =>
    (integrable_indicator_iff isOpen_interior.measurableSet).2
      ((((hv T hT i).pow 2).continuousOn.integrableOn_compact T.isCompact_closedInterior).mono_set
        interior_subset)
  calc ∫ x, ((pieceL2 M M.domain v hv i : (Fin n → ℝ) → ℝ) x) ^ 2 ∂volume.restrict M.domain
      = ∫ x in M.domain, (pieceFun M (fun T => v T i) x) ^ 2 := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_pieceL2 M M.domain v hv i] with x hx
        rw [hx]
    _ = ∫ x in M.domain, ∑ T ∈ M.simplices,
          (interior T.closedInterior).indicator (fun x => (v T i x) ^ 2) x := by
        simp_rw [pieceFun_sq]
    _ = ∑ T ∈ M.simplices, ∫ x in M.domain,
          (interior T.closedInterior).indicator (fun x => (v T i x) ^ 2) x :=
        integral_finsetSum _ fun T hT => (hint' T hT).integrableOn
    _ = ∑ T ∈ M.simplices, ∫ x in interior T.closedInterior, (v T i x) ^ 2 := by
        refine Finset.sum_congr rfl fun T hT => ?_
        rw [setIntegral_indicator isOpen_interior.measurableSet,
          Set.inter_eq_right.2 (hint T hT)]
    _ = ∑ T ∈ M.simplices, ∫ x in T.closedInterior, (v T i x) ^ 2 := by
        refine Finset.sum_congr rfl fun T _ => ?_
        exact (integral_closedInterior_eq_interior T _).symm

theorem interior_subset_mesh_domain {N : ℕ} :
    ∀ T ∈ (mesh n N).simplices, interior T.closedInterior ⊆ (mesh n N).domain := fun T hT => by
  rw [mesh_domain]; exact interior_closedInterior_subset_cubeDomain hT

/-- `Σ_{#s = k} ∫ u_s² = formL2Sq` for a field of degree `k`. -/
theorem sum_formIdx_integral_eq_formL2Sq {k : ℕ} {S : Set (Fin n → ℝ)} {u : FormField n}
    (hu : ∀ x, IsDeg k (u x)) :
    ∑ s : formIdx n k, ∫ x in S, (u x s.1) ^ 2 = formL2Sq S u := by
  unfold formL2Sq
  refine (sum_eq_sum_formIdx (f := fun s => ∫ x in S, (u x s) ^ 2) fun s hs => ?_).symm
  have : ∀ x, (u x s) ^ 2 = 0 := fun x => by rw [hu x s hs]; ring
  simp_rw [this]; simp

/-- **`‖glue u‖² = Σ_T ‖u_T‖²_{L²(T)}`** on the Freudenthal meshes of the cube. -/
theorem norm_sq_glue_eq (E : LocalElement n) {N k : ℕ} (u : E.Piecewise (mesh n N) k) :
    ‖E.glue (mesh n N) k u‖ ^ 2 =
      ∑ T : (mesh n N).simplices, formL2Sq (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior
        ((u T : E.space T k) : FormField n) := by
  change ‖pieceL2 (mesh n N) (mesh n N).domain (fun T => formComp (k := (k : ℤ))
    (E.extendPW (mesh n N) u T)) (fun T hT s => continuous_formComp
      (E.contDiff_extendPW (mesh n N) u hT).continuous s)‖ ^ 2 = _
  rw [norm_sq_pieceL2_eq _ interior_subset_mesh_domain, ← Finset.sum_coe_sort]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← sum_formIdx_integral_eq_formL2Sq (E.isDeg_of_mem (u T).2)]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [formComp, E.extendPW_of_mem _ u T.2]

/-- `norm_sq_glue_eq` for integer degrees `k ≥ 0`. -/
theorem norm_sq_glue_eq_int (E : LocalElement n) {N : ℕ} {k : ℤ} (hk : 0 ≤ k)
    (u : E.Piecewise (mesh n N) k.toNat) :
    ‖E.glue (mesh n N) k u‖ ^ 2 =
      ∑ T : (mesh n N).simplices, formL2Sq (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior
        ((u T : E.space T k.toNat) : FormField n) := by
  obtain ⟨k', rfl⟩ := Int.eq_ofNat_of_zero_le hk
  exact norm_sq_glue_eq E u

/-- `‖Σ_a uₐ‖² = Σₐ ‖uₐ‖²` for the componentwise gluing. -/
theorem norm_sq_tensorGlue (E : LocalElement n) {M : SimplicialMesh n} {m : ℕ} {k : ℤ}
    (u : Fin m → E.Piecewise M k.toNat) :
    ‖E.tensorGlue M m k u‖ ^ 2 = ∑ a, ‖E.glue M k (u a)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]; rfl

end Glue

/-! ### Pointwise identities and bounds for `S` -/

section Pointwise

/-- `(S v)_t = Σ_{a,r} c(t; a, r) (vₐ)_r` for vectors of `k`-forms. -/
theorem coordWedgeSum_eq_sum_wsCoeff {k : ℕ} {v : Fin n → Finset (Fin n) → ℝ}
    (hv : ∀ a, IsDeg k (v a)) (t : formIdx n ((k : ℤ) + 1)) :
    coordWedgeSum v t.1 = ∑ p : Fin n × formIdx n k, wsCoeff k t p * v p.1 p.2.1 := by
  have e : v = fun a => formExt fun r : formIdx n k => v a r.1 := by
    funext a
    have := formExt_formComp (k := k) (η := fun _ : Fin n → ℝ => v a) (x := 0) (hv a)
    exact this.symm
  conv_lhs => rw [e]
  exact coordWedgeSum_formExt (fun a r => v a r.1) t

/-- The algebra of `‖S‖² ≤ k + 1`: `Σ_t (Σ_p c(t; p) x_p)² ≤ (k + 1) Σ_p x_p²`. -/
theorem sum_sq_wsCoeff_le (k : ℤ) (x : Fin n × formIdx n k → ℝ) :
    ∑ t : formIdx n (k + 1), (∑ p, wsCoeff k t p * x p) ^ 2 ≤ ((k : ℝ) + 1) * ∑ p, x p ^ 2 := by
  have hpt : ∀ t : formIdx n (k + 1),
      (∑ p, wsCoeff k t p * x p) ^ 2 ≤ ((k : ℝ) + 1) * ∑ p, |wsCoeff k t p| * x p ^ 2 := by
    intro t
    have h1 : |∑ p, wsCoeff k t p * x p| ≤ ∑ p, |wsCoeff k t p| * |x p| :=
      (Finset.abs_sum_le_sum_abs _ _).trans_eq (by simp [abs_mul])
    have h2 : (∑ p, |wsCoeff k t p| * |x p|) ^ 2 ≤
        (∑ p, |wsCoeff k t p|) * ∑ p, |wsCoeff k t p| * |x p| ^ 2 :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun p _ => abs_nonneg _)
        (fun p _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)) fun p _ => le_of_eq (by ring)
    rw [sum_abs_wsCoeff_left] at h2
    simp only [sq_abs] at h2
    calc (∑ p, wsCoeff k t p * x p) ^ 2 = |∑ p, wsCoeff k t p * x p| ^ 2 := (sq_abs _).symm
      _ ≤ (∑ p, |wsCoeff k t p| * |x p|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ ≤ _ := h2
  calc ∑ t, (∑ p, wsCoeff k t p * x p) ^ 2
      ≤ ∑ t, ((k : ℝ) + 1) * ∑ p, |wsCoeff k t p| * x p ^ 2 := Finset.sum_le_sum fun t _ => hpt t
    _ = ((k : ℝ) + 1) * ∑ p, (∑ t, |wsCoeff k t p|) * x p ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.sum_mul]
    _ ≤ ((k : ℝ) + 1) * ∑ p, x p ^ 2 := by
        by_cases hk : (0 : ℝ) ≤ (k : ℝ) + 1
        · gcongr with p
          exact mul_le_of_le_one_left (sq_nonneg _) (sum_abs_wsCoeff_right p)
        · have : IsEmpty (formIdx n k) := ⟨fun r => by
            have h1 := r.2
            have h2 : (0 : ℤ) ≤ #r.1 := Int.natCast_nonneg _
            have : (k : ℝ) + 1 < 0 := lt_of_not_ge hk
            have : k + 1 < 0 := by exact_mod_cast this
            omega⟩
          simp

/-- **`|S v|² ≤ (k + 1) Σₐ |vₐ|²` pointwise** (`k`-forms; the Frobenius norms of the
coefficients). -/
theorem sum_sq_coordWedgeSum_le {k : ℕ} {v : Fin n → Finset (Fin n) → ℝ}
    (hv : ∀ a, IsDeg k (v a)) :
    ∑ s, (coordWedgeSum v s) ^ 2 ≤ ((k : ℝ) + 1) * ∑ a, ∑ s, (v a s) ^ 2 := by
  have hdeg : IsDeg (k + 1) (coordWedgeSum v) := isDeg_coordWedgeSum hv
  rw [sum_eq_sum_formIdx (k := k + 1) (f := fun s => (coordWedgeSum v s) ^ 2) fun s hs => by
    rw [hdeg s hs]; ring]
  have e1 : ∀ t : formIdx n ((k + 1 : ℕ) : ℤ), coordWedgeSum v t.1 =
      ∑ p : Fin n × formIdx n k, wsCoeff k ⟨t.1, by have := t.2; push_cast at this ⊢; exact this⟩ p *
        v p.1 p.2.1 := fun t => coordWedgeSum_eq_sum_wsCoeff hv _
  simp_rw [e1]
  have e2 : ∀ a, ∑ s, (v a s) ^ 2 = ∑ r : formIdx n k, (v a r.1) ^ 2 := fun a =>
    sum_eq_sum_formIdx (f := fun s => (v a s) ^ 2) fun s hs => by rw [hv a s hs]; ring
  simp_rw [e2]
  rw [← Fintype.sum_prod_type' (f := fun a (r : formIdx n k) => (v a r.1) ^ 2)]
  have h := sum_sq_wsCoeff_le (n := n) k (fun p => v p.1 p.2.1)
  push_cast at h
  refine le_trans (le_of_eq ?_) h
  refine Fintype.sum_equiv (Equiv.subtypeEquivRight fun s => by push_cast; rfl) _ _ fun t => ?_
  rfl

/-- **`S⁰` is an isometry pointwise**: `|S⁰ψ|² = Σₐ |ψₐ|²` for vectors of `0`-forms. -/
theorem sum_sq_coordWedgeSum_zero {v : Fin n → Finset (Fin n) → ℝ} (hv : ∀ a, IsDeg 0 (v a)) :
    ∑ s, (coordWedgeSum v s) ^ 2 = ∑ a, ∑ s, (v a s) ^ 2 := by
  have hdeg : IsDeg 1 (coordWedgeSum v) := isDeg_coordWedgeSum hv
  have h1 : ∑ s, (coordWedgeSum v s) ^ 2 = ∑ j : Fin n, (coordWedgeSum v {j}) ^ 2 := by
    rw [sum_eq_sum_formIdx (k := 1) (f := fun s => (coordWedgeSum v s) ^ 2) fun s hs => by
      rw [hdeg s hs]; ring]
    have hb : Function.Bijective fun j : Fin n => (⟨{j}, by simp⟩ : formIdx n ((1 : ℕ) : ℤ)) := by
      refine ⟨fun i j hij => Finset.singleton_injective (congrArg Subtype.val hij), fun t => ?_⟩
      obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (by exact_mod_cast t.2 : #t.1 = 1)
      exact ⟨a, Subtype.ext ha.symm⟩
    exact (Fintype.sum_bijective _ hb (fun j => (coordWedgeSum v {j}) ^ 2)
      (fun t : formIdx n ((1 : ℕ) : ℤ) => (coordWedgeSum v t.1) ^ 2) fun j => rfl).symm
  have h2 : ∀ a, ∑ s, (v a s) ^ 2 = (v a ∅) ^ 2 := fun a => by
    rw [Finset.sum_eq_single ∅ (fun s _ hs => by
      rw [hv a s (by rwa [Ne, Finset.card_eq_zero])]; ring) (by simp)]
  rw [h1]
  simp_rw [coordWedgeSum_singleton, h2]

end Pointwise

/-! ### `S` on polynomial fields and on `L²(T)` -/

section Integrated

theorem continuous_sq_coeff {u : FormField n} (hu : Continuous u) (s : Finset (Fin n)) :
    Continuous fun x => (u x s) ^ 2 := ((continuous_apply s).comp hu).pow 2

theorem continuous_sum_sq {u : FormField n} (hu : Continuous u) :
    Continuous fun x => ∑ s, (u x s) ^ 2 :=
  continuous_finsetSum _ fun s _ => continuous_sq_coeff hu s

/-- `ξ ∧ ·` maps `P_rΛᵏ` to `P_rΛᵏ⁺¹` for a constant covector `ξ`. -/
theorem wedge_mem_polySpace {r k : ℕ} (ξ : Fin n → ℝ) {w : FormField n}
    (hw : w ∈ polySpace n r k) : (fun x => wedge ξ (w x)) ∈ polySpace n r (k + 1) := by
  obtain ⟨Ω, hΩ, rfl⟩ := hw
  refine ⟨fun s => ∑ j ∈ s, MvPolynomial.C (sgn j s * ξ j) * Ω (s.erase j), ⟨fun s hs => ?_,
    fun s => ?_⟩, ?_⟩
  · refine Finset.sum_eq_zero fun j hj => ?_
    have := Finset.card_pos.2 ⟨j, hj⟩
    rw [hΩ.1 (s.erase j) (by rw [Finset.card_erase_of_mem hj]; omega), mul_zero]
  · refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact hΩ.2 _
  · funext x s
    simp [evalForm_apply, wedge_apply, mul_comm]

/-- `S` maps `(P_rΛᵏ)ⁿ` to `P_rΛᵏ⁺¹`. -/
theorem coordWedgeField_mem_polySpace {r k : ℕ} {v : Fin n → FormField n}
    (hv : ∀ a, v a ∈ polySpace n r k) : coordWedgeField v ∈ polySpace n r (k + 1) := by
  have : coordWedgeField v = ∑ a, fun x => wedge (Pi.single a 1) (v a x) := by
    funext x; simp [coordWedgeField_apply, coordWedgeSum, Finset.sum_apply]
  rw [this]
  exact Submodule.sum_mem _ fun a _ => wedge_mem_polySpace _ (hv a)

theorem integral_sum_sq_eq_formL2Sq {S : Set (Fin n → ℝ)} (hS : IsCompact S) {u : FormField n}
    (hu : Continuous u) : ∫ x in S, ∑ s, (u x s) ^ 2 = formL2Sq S u := by
  unfold formL2Sq
  exact integral_finsetSum _ fun s _ =>
    (continuous_sq_coeff hu s).continuousOn.integrableOn_compact hS

/-- `‖S v‖²_{L²(S)} ≤ (k + 1) Σₐ ‖vₐ‖²_{L²(S)}`. -/
theorem formL2Sq_coordWedgeField_le {S : Set (Fin n → ℝ)} (hS : IsCompact S) {k : ℕ}
    {v : Fin n → FormField n} (hc : ∀ a, Continuous (v a)) (hv : ∀ a x, IsDeg k (v a x)) :
    formL2Sq S (coordWedgeField v) ≤ ((k : ℝ) + 1) * ∑ a, formL2Sq S (v a) := by
  rw [← integral_sum_sq_eq_formL2Sq hS (continuous_coordWedgeField hc)]
  simp_rw [← integral_sum_sq_eq_formL2Sq hS (hc _)]
  have hcw := continuous_coordWedgeField hc
  rw [← integral_finsetSum _ fun a _ => (continuous_sum_sq (hc a)).continuousOn.integrableOn_compact hS,
    ← integral_const_mul]
  refine setIntegral_mono_on ((continuous_sum_sq hcw).continuousOn.integrableOn_compact hS)
    ((continuous_const.mul (continuous_finsetSum _ fun a _ =>
      continuous_sum_sq (hc a))).continuousOn.integrableOn_compact hS)
    hS.measurableSet fun x _ => ?_
  exact sum_sq_coordWedgeSum_le fun a => hv a x

/-- `‖S⁰ψ‖²_{L²(S)} = Σₐ ‖ψₐ‖²_{L²(S)}`. -/
theorem formL2Sq_coordWedgeField_zero {S : Set (Fin n → ℝ)} (hS : IsCompact S)
    {v : Fin n → FormField n} (hc : ∀ a, Continuous (v a)) (hv : ∀ a x, IsDeg 0 (v a x)) :
    formL2Sq S (coordWedgeField v) = ∑ a, formL2Sq S (v a) := by
  rw [← integral_sum_sq_eq_formL2Sq hS (continuous_coordWedgeField hc)]
  simp_rw [← integral_sum_sq_eq_formL2Sq hS (hc _)]
  rw [← integral_finsetSum _ fun a _ => (continuous_sum_sq (hc a)).continuousOn.integrableOn_compact hS]
  refine setIntegral_congr_fun hS.measurableSet fun x _ => ?_
  exact sum_sq_coordWedgeSum_zero fun a => hv a x

end Integrated

/-! ### The local estimates on the mesh simplices -/

section MeshLocal

theorem exists_mesh_simplex_eq {N : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) :
    ∃ (σ : Equiv.Perm (Fin n)) (t : Fin n → ℝ),
      T = mapEquiv (boxMap t (hN N) (hN_pos N).ne') (kuhnSimplex σ) := by
  obtain ⟨m, σ, rfl⟩ := mem_mesh_simplices.1 hT
  exact ⟨σ, _, cubeSimplex_eq N m σ⟩

/-- The reference simplices: the Kuhn simplices with lexicographically ordered vertices. -/
abbrev kuhnLex (σ : Equiv.Perm (Fin n)) : Affine.Simplex ℝ (Fin n → ℝ) n :=
  lexSimplex (kuhnSimplex σ)

/-- **The local bound of `S_h = Π' S`** on every mesh simplex, with a constant independent of the
mesh: `‖Π'_T (S v)‖²_{L²(T)} ≤ C ‖S v‖²_{L²(T)}` for `S v ∈ P_rΛᵏ⁺¹`. -/
theorem exists_formL2Sq_localInterp_le {k r : ℕ} (hk : k + 1 ≤ n) (hr : 1 ≤ r) :
    ∃ C, 0 ≤ C ∧ ∀ (N : ℕ) (T : (mesh n N).simplices) {w : FormField n}
      (hw : w ∈ polySpace n r (k + 1)),
      formL2Sq (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior
        (((polyElement n PolySeq.lowestOrder).localInterp T (k + 1)
          ⟨w, (polySpace_le_contDegForms r (k + 1) hw).1⟩ :
            (polyElement n PolySeq.lowestOrder).space T (k + 1)) : FormField n) ≤
        C * formL2Sq (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior w := by
  obtain ⟨C, hC0, hC⟩ := exists_formL2Sq_polyMinusInterp_le_uniform (n := n)
    (fun σ : Equiv.Perm (Fin n) => kuhnLex σ) (r := r) (k := k + 1) le_rfl hk hr
  refine ⟨C ^ 2, sq_nonneg C, fun N T w hw => ?_⟩
  obtain ⟨σ, t, hT⟩ := exists_mesh_simplex_eq T.2
  have hh := hN_pos N
  set wc : contDegForms n (k + 1) := ⟨w, polySpace_le_contDegForms r (k + 1) hw⟩
  have hid := localInterp_lowestOrder_eq (kuhnSimplex σ) t hh hk wc
  have hS := closedInterior_mapEquiv_lexSimplex (kuhnSimplex σ) t hh.ne'
  have h1 := hC σ hh t hw
  rw [hS] at h1
  have e1 : (((polyElement n PolySeq.lowestOrder).localInterp T (k + 1) ⟨w, wc.2.1⟩ :
      (polyElement n PolySeq.lowestOrder).space T (k + 1)) : FormField n) =
      (polyMinusInterp (isUnit_det_edgeMatrix (mapEquiv (boxMap t (hN N) hh.ne') (kuhnLex σ)))
        (PolySeq.lowestOrder.one_le_deg (k + 1)) hk wc : FormField n) := by
    rw [← hid]
    exact PolySeq.localInterp_congr _ _ (by rw [hT]) _
  change formL2Sq _ (((polyElement n PolySeq.lowestOrder).localInterp T (k + 1) ⟨w, wc.2.1⟩ :
      (polyElement n PolySeq.lowestOrder).space T (k + 1)) : FormField n) ≤ _
  rw [e1, hT]
  have hm := (mapEquiv (boxMap t (hN N) hh.ne') (kuhnSimplex σ)).isCompact_closedInterior.measurableSet
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  rw [Real.sq_sqrt (formL2Sq_nonneg hm _), mul_pow, Real.sq_sqrt (formL2Sq_nonneg hm _)] at h2
  exact h2

end MeshLocal

/-! ### Prop 5.8, corrected -/

section Prop58

/-- `S_h` on a mesh simplex as the interpolant of a polynomial field. -/
theorem wsPiecewise_apply_eq (S : PolySeq) {N k : ℕ}
    (u : Fin n → (polyElement n S).Piecewise (mesh n N) k) (T : (mesh n N).simplices) {r : ℕ}
    (hw : coordWedgeField (fun a => ((u a T : (polyElement n S).space T k) : FormField n)) ∈
      polySpace n r (k + 1)) :
    ((S.wsPiecewise (mesh n N) k u T : (polyElement n PolySeq.lowestOrder).space T (k + 1)) :
        FormField n) =
      (((polyElement n PolySeq.lowestOrder).localInterp T (k + 1)
        ⟨coordWedgeField (fun a => ((u a T : (polyElement n S).space T k) : FormField n)),
          (polySpace_le_contDegForms r (k + 1) hw).1⟩ :
          (polyElement n PolySeq.lowestOrder).space T (k + 1)) : FormField n) := rfl

/-- The fields of a polynomial family lie in `P_{r_k}Λᵏ`. -/
theorem mem_polySpace_of_space (S : PolySeq) {k : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (u : (polyElement n S).space T k) : (u : FormField n) ∈ polySpace n (S.deg k) k :=
  S.space_le_polySpace k u.2

/-- The local form of Prop 5.8 for `S⁰`: `‖S₀,ₕψ‖²_{L²(T)} ≤ C Σₐ ‖ψₐ‖²_{L²(T)}`. -/
theorem exists_formL2Sq_wsPiecewise_zero_le : ∃ C, 0 ≤ C ∧ ∀ (N : ℕ)
    (ψ : Fin 3 → (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 N) 0)
    (T : (mesh 3 N).simplices),
    formL2Sq (T : Affine.Simplex ℝ (Fin 3 → ℝ) 3).closedInterior
      ((PolySeq.lagrangeP2.wsPiecewise (mesh 3 N) 0 ψ T :
        (polyElement 3 PolySeq.lowestOrder).space T 1) : FormField 3) ≤
      C * ∑ a, formL2Sq (T : Affine.Simplex ℝ (Fin 3 → ℝ) 3).closedInterior
        ((ψ a T : (polyElement 3 PolySeq.lagrangeP2).space T 0) : FormField 3) := by
  obtain ⟨C, hC0, hC⟩ := exists_formL2Sq_localInterp_le (n := 3) (k := 0) (r := 2)
    (by norm_num) (by norm_num)
  refine ⟨C, hC0, fun N ψ T => ?_⟩
  have hw : coordWedgeField (fun a => ((ψ a T : (polyElement 3 PolySeq.lagrangeP2).space T 0) :
      FormField 3)) ∈ polySpace 3 2 (0 + 1) :=
    coordWedgeField_mem_polySpace fun a => mem_polySpace_of_space _ (ψ a T)
  have h1 := hC N T hw
  rw [formL2Sq_coordWedgeField_zero (T : Affine.Simplex ℝ (Fin 3 → ℝ) 3).isCompact_closedInterior
    (fun a => ((polyElement 3 PolySeq.lagrangeP2).contDiff_of_mem (ψ a T).2).continuous)
    (fun a x => (polyElement 3 PolySeq.lagrangeP2).isDeg_of_mem (ψ a T).2 x)] at h1
  rw [wsPiecewise_apply_eq _ _ _ hw]
  exact h1

/-- The local form of Prop 5.8 for `S¹`: `‖S₁,ₕv‖²_{L²(T)} ≤ C Σₐ ‖vₐ‖²_{L²(T)}`. -/
theorem exists_formL2Sq_wsPiecewise_one_le : ∃ C, 0 ≤ C ∧ ∀ (N : ℕ)
    (v : Fin 3 → (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 N) 1)
    (T : (mesh 3 N).simplices),
    formL2Sq (T : Affine.Simplex ℝ (Fin 3 → ℝ) 3).closedInterior
      ((PolySeq.lagrangeP2.wsPiecewise (mesh 3 N) 1 v T :
        (polyElement 3 PolySeq.lowestOrder).space T 2) : FormField 3) ≤
      C * ∑ a, formL2Sq (T : Affine.Simplex ℝ (Fin 3 → ℝ) 3).closedInterior
        ((v a T : (polyElement 3 PolySeq.lagrangeP2).space T 1) : FormField 3) := by
  obtain ⟨C, hC0, hC⟩ := exists_formL2Sq_localInterp_le (n := 3) (k := 1) (r := 2)
    (by norm_num) (by norm_num)
  refine ⟨C * 2, by positivity, fun N v T => ?_⟩
  have hw : coordWedgeField (fun a => ((v a T : (polyElement 3 PolySeq.lagrangeP2).space T 1) :
      FormField 3)) ∈ polySpace 3 2 (1 + 1) :=
    coordWedgeField_mem_polySpace fun a => mem_polySpace_of_space _ (v a T)
  have h1 := hC N T hw
  have h2 := formL2Sq_coordWedgeField_le (k := 1)
    (T : Affine.Simplex ℝ (Fin 3 → ℝ) 3).isCompact_closedInterior
    (fun a => ((polyElement 3 PolySeq.lagrangeP2).contDiff_of_mem (v a T).2).continuous)
    (fun a x => (polyElement 3 PolySeq.lagrangeP2).isDeg_of_mem (v a T).2 x)
  rw [wsPiecewise_apply_eq _ _ _ hw]
  norm_num at h2
  calc _ ≤ C * formL2Sq (T : Affine.Simplex ℝ (Fin 3 → ℝ) 3).closedInterior
        (coordWedgeField fun a => ((v a T : (polyElement 3 PolySeq.lagrangeP2).space T 1) :
          FormField 3)) := h1
    _ ≤ C * (2 * ∑ a, formL2Sq (T : Affine.Simplex ℝ (Fin 3 → ℝ) 3).closedInterior
        ((v a T : (polyElement 3 PolySeq.lagrangeP2).space T 1) : FormField 3)) :=
        mul_le_mul_of_nonneg_left h2 hC0
    _ = _ := by ring

/-- Summing a local bound over the mesh. -/
theorem norm_le_of_local {N : ℕ} {E E' : LocalElement n} {k k' : ℕ} {m : ℕ}
    (u : E'.Piecewise (mesh n N) k') (ψ : Fin m → E.Piecewise (mesh n N) k) {C : ℝ} (hC0 : 0 ≤ C)
    (hloc : ∀ T : (mesh n N).simplices,
      formL2Sq (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior
        ((u T : E'.space T k') : FormField n) ≤
      C * ∑ a, formL2Sq (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior
        ((ψ a T : E.space T k) : FormField n)) :
    ‖E'.glue (mesh n N) k' u‖ ≤ √C * ‖E.tensorGlue (mesh n N) m k ψ‖ := by
  have hsq : ‖E'.glue (mesh n N) k' u‖ ^ 2 ≤ C * ‖E.tensorGlue (mesh n N) m k ψ‖ ^ 2 := by
    rw [norm_sq_tensorGlue, norm_sq_glue_eq]
    simp_rw [norm_sq_glue_eq]
    calc _ ≤ ∑ T : (mesh n N).simplices, C * ∑ a,
          formL2Sq (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior
            ((ψ a T : E.space T k) : FormField n) := Finset.sum_le_sum fun T _ => hloc T
      _ = C * ∑ a, ∑ T : (mesh n N).simplices,
          formL2Sq (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior
            ((ψ a T : E.space T k) : FormField n) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
    (norm_nonneg _)) two_ne_zero).1 ?_
  rw [mul_pow, Real.sq_sqrt hC0]
  exact hsq

/-- **[QuennevilleBelair2015], Prop 5.8, corrected (`S₀,ₕ`)**: `‖S₀,ₕψ‖_{L²(Q)} ≤ C ‖ψ‖_{L²(Q)}`
on `P₂Λ⁰ ⊗ ℝ³`, `C` independent of the mesh level. -/
theorem norm_glue_bggS0h_le : ∃ C, 0 ≤ C ∧ ∀ (N : ℕ)
    (ψ : Fin 3 → (polyElement 3 PolySeq.lagrangeP2).globalSpace (mesh 3 N) 0),
    ‖(polyElement 3 PolySeq.lowestOrder).glue (mesh 3 N) ((0 : ℕ) + 1 : ℕ)
      ((PolySeq.bggS0h (mesh 3 N) ψ : (polyElement 3 PolySeq.lowestOrder).globalSpace (mesh 3 N) 1) :
        (polyElement 3 PolySeq.lowestOrder).Piecewise (mesh 3 N) 1)‖ ≤
      C * ‖(polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 N) 3 ((0 : ℕ) : ℤ)
        fun a => ((ψ a : (polyElement 3 PolySeq.lagrangeP2).globalSpace (mesh 3 N) 0) :
          (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 N) 0)‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_formL2Sq_wsPiecewise_zero_le
  exact ⟨√C, Real.sqrt_nonneg _, fun N ψ => norm_le_of_local _ _ hC0 fun T => hC N _ T⟩

/-- **[QuennevilleBelair2015], Prop 5.8, corrected (`S₁,ₕ`)**: `‖S₁,ₕv‖_{L²(Q)} ≤ C ‖v‖_{L²(Q)}`
on `P₂⁻Λ¹ ⊗ ℝ³` (the half of Prop 5.8 that the thesis does not prove). -/
theorem norm_glue_bggS1h_le : ∃ C, 0 ≤ C ∧ ∀ (N : ℕ)
    (v : Fin 3 → (polyElement 3 PolySeq.lagrangeP2).globalSpace (mesh 3 N) 1),
    ‖(polyElement 3 PolySeq.lowestOrder).glue (mesh 3 N) ((1 : ℕ) + 1 : ℕ)
      ((PolySeq.bggS1h (mesh 3 N) v : (polyElement 3 PolySeq.lowestOrder).globalSpace (mesh 3 N) 2) :
        (polyElement 3 PolySeq.lowestOrder).Piecewise (mesh 3 N) 2)‖ ≤
      C * ‖(polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 N) 3 ((1 : ℕ) : ℤ)
        fun a => ((v a : (polyElement 3 PolySeq.lagrangeP2).globalSpace (mesh 3 N) 1) :
          (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 N) 1)‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_formL2Sq_wsPiecewise_one_le
  exact ⟨√C, Real.sqrt_nonneg _, fun N v => norm_le_of_local _ _ hC0 fun T => hC N _ T⟩

end Prop58

end Feec.Models.Cube.WeakSymmetry
