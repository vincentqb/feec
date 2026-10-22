module

public import Feec.Models.Cube.WeakSymmetryComplex
public import Feec.Models.Cube.SmoothingEstimates
public import Feec.Models.Cube.PolySmoothingEstimates

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
  copies `t + h K_σ` of the Kuhn simplices (`exists_formL2Sq_localInterp_le`).
* **Prop 5.9(1)** (`norm_sub_glue_bggS0h_le`): `‖(I − Π¹) S⁰ψ‖ ≤ C h ‖∇ψ‖` on `P₂Λ⁰ ⊗ ℝ³`
  (the kernel lemma `Feec.FiniteElement.exists_formL2Sq_sub_polyMinusInterp_le_formGradL2Sq`).
* **Prop 5.9(2) is false** (`exists_interpolationError_ge`, `not_exists_interpolationError_bound`):
  there is `c > 0` such that on every mesh `mesh 3 (N + 2)` there is `v ∈ P₂⁻Λ̊¹ ⊗ ℝ³`
  (vanishing boundary DOFs), `v ≠ 0`, with `‖(I − Π²) S¹ v‖ ≥ c ‖v‖_{H(curl)}` for the canonical
  interpolant `Π²`; hence no bound `‖(I − Π²) S¹ v‖ ≤ C h ‖v‖_{H(curl)}` holds. **Projection
  independence** (`exists_bestApproxError_ge`, `not_exists_bestApprox_bound`):
  the same `v_N` satisfies `‖S¹ v_N − w‖ ≥ c' ‖v_N‖_{H(curl)}` for *every* piecewise `P₁⁻Λ²`
  field `w`, because `δ₀ = dist_{L²(K₁)}(Ẑ, P₁⁻Λ²) > 0` (`refDist_pos`); so the hypothesis
  `happ1` of `Feec.BGG.Discrete.error_estimate` fails for every projection `P²` onto the
  Raviart–Thomas spaces of Table 5.1 (canonical or smoothed). `v_N` is also piecewise linear,
  `v_N ∈ P₁Λ¹ ⊗ ℝ³` (`vN_mem_polySpace`), the space of the thesis' statement. The field is
  `v_N = (0, 0, grad Π̃⁰ f_N)` (`vN`), `f_N(x) = F(h⁻¹(x − t_N))` with `F = χ y₀²/2` a smooth
  bump profile, quadratic on one simplex `T₀ = t_N + h K_id`: `curl v_N = 0` (`dPiecewise_vN`),
  `‖v_N‖² ≤ C h` (`exists_sum_formL2Sq_vN_le`: `L∞`-stability of `Π̃¹`, bounded overlap), while
  on `T₀` the field `S¹ v_N` pulls back to `h Ẑ`, `Ẑ = S¹(0, 0, y₀ dy₀)` not a Raviart–Thomas
  field (`refZ_notMem`), so `‖(I − Π²) S¹ v_N‖²_{L²(T₀)} = h c₀`, `c₀ > 0` (`formL2Sq_simplex₀`,
  `refGap_pos`).
* **`S` and the smoothing** (`smoothForm_wsL2`): `R S u = c S R̃ u` for the smoothing operators of
  `Feec.Models.Cube.FEM.smoothForm` (extension by zero, mollification, dilation by `c`).
* **`grad` is injective on `P₂Λ̊⁰ ⊗ ℝ³`** (`eq_zero_of_dPiecewise_tensor_eq_zero`; any family,
  `eq_zero_of_dPiecewise_eq_zero`), from `ℌ⁰(H̊Λ(Q)) = 0`.

**The canonical interpolants.** The interpolants of the global trimmed families on a mesh simplex
`T` are the interpolants `Feec.FiniteElement.polyMinusInterp` of `LocalDof` for the lexicographic
vertex order (`Feec.FiniteElement.PolySeq.localInterp_eq_polyMinusInterp`); the mesh simplices
are `t + h_N K_σ` with `K_σ` the Kuhn simplices (`exists_mesh_simplex_eq`), reordered
lexicographically (`lexSimplex`, `kuhnLex`, `localInterp_lowestOrder_eq`), so the local estimates
of `Feec.FiniteElement.PolyInterpolation` hold with constants uniform over the `3!` simplices.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.3, Props 5.8–5.9, Table 5.1
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.2 (canonical interpolants), §5.4 (scaling arguments)
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], Thm 3.1.4
  (interpolation error on affine-equivalent families)
* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]
* [H. W. Kuhn, *Some combinatorial lemmas in topology*][Kuhn1960]

Bibliography: [references.bib](../../../docs/references.bib)
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

/-! ### `S` on glued fields -/

section GluedS

theorem pieceFun_sum_mul (M : SimplicialMesh n) {β : Type*} (u : Finset β) (c : β → ℝ)
    (v : β → Affine.Simplex ℝ (Fin n → ℝ) n → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    ∑ b ∈ u, c b * pieceFun M (v b) x = pieceFun M (fun T y => ∑ b ∈ u, c b * v b T y) x := by
  simp only [pieceFun, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hx : x ∈ interior T.closedInterior
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-- **`S` of a glued field is the glued field of the local `S`**: `S(glue ψ) = glue(T ↦ S ψ_T)`. -/
theorem wsL2_tensorGlue (E : LocalElement n) (M : SimplicialMesh n) {k : ℕ}
    (ψ : Fin n → E.Piecewise M k) :
    wsL2 (Ω := M.domain) k (E.tensorGlue M n k ψ) =
      pieceL2 M M.domain (fun T => formComp (k := (k : ℤ) + 1)
        (coordWedgeField fun a => E.extendPW M (ψ a) T))
        (fun _ hT s => continuous_formComp (continuous_coordWedgeField fun a =>
          (E.contDiff_extendPW M (ψ a) hT).continuous) s) := by
  refine PiLp.ext fun t => Lp.ext ?_
  rw [wsL2_apply]
  have h1 := Lp.coeFn_finsetSum Finset.univ fun p : Fin n × formIdx n k =>
    wsCoeff k t p • (E.tensorGlue M n k ψ) p.1 p.2
  have h2 : ∀ p : Fin n × formIdx n k,
      (((wsCoeff k t p • (E.tensorGlue M n k ψ) p.1 p.2 : L2 ℝ M.domain)) : (Fin n → ℝ) → ℝ) =ᵐ[
        volume.restrict M.domain] fun x => wsCoeff k t p *
          pieceFun M (fun T => formComp (k := (k : ℤ)) (E.extendPW M (ψ p.1) T) p.2) x := by
    intro p
    filter_upwards [Lp.coeFn_smul (wsCoeff k t p) ((E.tensorGlue M n k ψ) p.1 p.2),
      coeFn_pieceL2 M M.domain (fun T => formComp (k := (k : ℤ)) (E.extendPW M (ψ p.1) T))
        (fun T hT s => continuous_formComp (E.contDiff_extendPW M (ψ p.1) hT).continuous s) p.2]
      with x hx1 hx2
    rw [hx1, Pi.smul_apply, smul_eq_mul]
    congr 1
  have h2' := ae_all_iff.2 h2
  filter_upwards [h1, h2', coeFn_pieceL2 M M.domain _ (fun T hT s => continuous_formComp
    (continuous_coordWedgeField fun a => (E.contDiff_extendPW M (ψ a) hT).continuous) s) t]
    with x hx1 hx2 hx3
  rw [hx1, Finset.sum_apply, hx3]
  simp only [hx2]
  rw [pieceFun_sum_mul]
  simp only [pieceFun]
  refine Finset.sum_congr rfl fun T hT => ?_
  by_cases hxT : x ∈ interior T.closedInterior
  · rw [Set.indicator_of_mem hxT, Set.indicator_of_mem hxT]
    simp only [formComp]
    rw [coordWedgeField_apply, coordWedgeSum_eq_sum_wsCoeff (fun a => E.isDeg_extendPW M (ψ a) hT x)]
  · rw [Set.indicator_of_notMem hxT, Set.indicator_of_notMem hxT]

end GluedS

/-! ### Prop 5.9(1) -/

section Prop59

theorem isDeg_zero_partialDerivForm {u : FormField n} (hu : ∀ x, IsDeg 0 (u x)) (j : Fin n)
    (x : Fin n → ℝ) : IsDeg 0 (partialDerivForm j u x) := fun s hs => by
  have : (fun y => u y s) = fun _ => 0 := funext fun y => hu y s hs
  simp only [partialDerivForm, this, partialDeriv_const]

/-- `‖D S⁰ψ‖²_{L²(S)} = Σₐ ‖Dψₐ‖²_{L²(S)}` for polynomial `ψ`. -/
theorem formGradL2Sq_coordWedgeField_zero {S : Set (Fin n → ℝ)} (hS : IsCompact S) {r : ℕ}
    {v : Fin n → FormField n} (hv : ∀ a, v a ∈ polySpace n r 0) :
    formGradL2Sq S (coordWedgeField v) = ∑ a, formGradL2Sq S (v a) := by
  have hd : ∀ a x, DifferentiableAt ℝ (v a) x := fun a x =>
    differentiableAt_pi.2 fun s => (differentiable_coeff_of_mem_polySpace (hv a) s) x
  have hcont : ∀ a j s, Continuous fun x => (partialDerivForm j (v a) x s) ^ 2 := fun a j s =>
    (continuous_partialDeriv_coeff_of_mem_polySpace (hv a) j s).pow 2
  unfold formGradL2Sq
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : ∀ s, ∫ x in S, (partialDeriv j (fun y => coordWedgeField v y s) x) ^ 2 =
      ∫ x in S, (coordWedgeSum (fun a => partialDerivForm j (v a) x) s) ^ 2 := fun s =>
    setIntegral_congr_fun hS.measurableSet fun x _ => by
      rw [← partialDerivForm_coordWedgeField (fun a => hd a x) j]; rfl
  simp_rw [e1]
  have hp : coordWedgeField v ∈ polySpace n r (0 + 1) := coordWedgeField_mem_polySpace hv
  have hint : ∀ s, IntegrableOn
      (fun x => (coordWedgeSum (fun a => partialDerivForm j (v a) x) s) ^ 2) S := fun s => by
    have : (fun x => (coordWedgeSum (fun a => partialDerivForm j (v a) x) s) ^ 2) =
        fun x => (partialDeriv j (fun y => coordWedgeField v y s) x) ^ 2 := by
      funext x
      rw [← partialDerivForm_coordWedgeField (fun a => hd a x) j]; rfl
    rw [this]
    exact ((continuous_partialDeriv_coeff_of_mem_polySpace hp j s).pow 2).continuousOn
      |>.integrableOn_compact hS
  rw [← integral_finsetSum _ fun s _ => hint s]
  have e2 : ∀ a, ∑ s, ∫ x in S, (partialDeriv j (fun y => v a y s) x) ^ 2 =
      ∫ x in S, ∑ s, (partialDerivForm j (v a) x s) ^ 2 := fun a =>
    (integral_finsetSum _ fun s _ => (hcont a j s).continuousOn.integrableOn_compact hS).symm
  simp_rw [e2]
  rw [← integral_finsetSum _ fun a _ => (continuous_finsetSum _ fun s _ =>
    hcont a j s).continuousOn.integrableOn_compact hS]
  refine setIntegral_congr_fun hS.measurableSet fun x _ => ?_
  exact sum_sq_coordWedgeSum_zero fun a =>
    isDeg_zero_partialDerivForm (isDeg_of_mem_polySpace (hv a)) j x

/-- For `0`-forms, `‖Du‖_{L²(S)} = ‖du‖_{L²(S)}` (`du = Σⱼ ∂ⱼu dxⱼ`). -/
theorem formGradL2Sq_eq_formL2Sq_extDeriv {S : Set (Fin n → ℝ)} {u : FormField n}
    (hu : ∀ x, IsDeg 0 (u x)) : formGradL2Sq S u = formL2Sq S (extDeriv u) := by
  have hdeg : ∀ x, IsDeg 1 (extDeriv u x) := IsDeg.extDeriv hu
  unfold formGradL2Sq formL2Sq
  have h1 : ∀ j, ∑ s, ∫ x in S, (partialDeriv j (fun y => u y s) x) ^ 2 =
      ∫ x in S, (partialDeriv j (fun y => u y ∅) x) ^ 2 := fun j => by
    rw [Finset.sum_eq_single ∅ (fun s _ hs => by
      have : (fun y => u y s) = fun _ => 0 := funext fun y =>
        hu y s (by rwa [Ne, Finset.card_eq_zero])
      simp [this]) (by simp)]
  simp_rw [h1]
  rw [sum_eq_sum_formIdx (k := 1) (f := fun s => ∫ x in S, (extDeriv u x s) ^ 2) fun s hs => by
    have : ∀ x, (extDeriv u x s) ^ 2 = 0 := fun x => by rw [hdeg x s hs]; ring
    simp_rw [this]; simp]
  have hb : Function.Bijective fun j : Fin n => (⟨{j}, by simp⟩ : formIdx n ((1 : ℕ) : ℤ)) := by
    refine ⟨fun i j hij => Finset.singleton_injective (congrArg Subtype.val hij), fun t => ?_⟩
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (by exact_mod_cast t.2 : #t.1 = 1)
    exact ⟨a, Subtype.ext ha.symm⟩
  refine Fintype.sum_bijective _ hb _ _ fun j => ?_
  congr 1
  funext x
  simp [extDeriv_apply, ExteriorFibre.sgn, Finset.filter_singleton]

/-- The kernel lemma on every mesh simplex, with a constant independent of the mesh:
`‖w − Π'_T w‖²_{L²(T)} ≤ C h² ‖Dw‖²_{L²(T)}` for `w ∈ P_rΛᵏ⁺¹`. -/
theorem exists_formL2Sq_sub_localInterp_le {k r : ℕ} (hk : k + 1 ≤ n) (hr : 1 ≤ r) :
    ∃ C, 0 ≤ C ∧ ∀ (N : ℕ) (T : (mesh n N).simplices) {w : FormField n}
      (hw : w ∈ polySpace n r (k + 1)),
      formL2Sq (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior
        (w - (((polyElement n PolySeq.lowestOrder).localInterp T (k + 1)
          ⟨w, (polySpace_le_contDegForms r (k + 1) hw).1⟩ :
            (polyElement n PolySeq.lowestOrder).space T (k + 1)) : FormField n)) ≤
        C * hN N ^ 2 * formGradL2Sq (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior w := by
  obtain ⟨C, hC0, hC⟩ := exists_formL2Sq_sub_polyMinusInterp_le_uniform (n := n)
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
  change formL2Sq _ (w - (((polyElement n PolySeq.lowestOrder).localInterp T (k + 1) ⟨w, wc.2.1⟩ :
      (polyElement n PolySeq.lowestOrder).space T (k + 1)) : FormField n)) ≤ _
  rw [e1, hT]
  have hm := (mapEquiv (boxMap t (hN N) hh.ne') (kuhnSimplex σ)).isCompact_closedInterior.measurableSet
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  rw [Real.sq_sqrt (formL2Sq_nonneg hm _), mul_pow, mul_pow,
    Real.sq_sqrt (formGradL2Sq_nonneg hm _)] at h2
  exact h2

theorem pieceL2_sub (M : SimplicialMesh n) (S : Set (Fin n → ℝ)) {ι : Type*} [Fintype ι]
    {v w : Affine.Simplex ℝ (Fin n → ℝ) n → ι → (Fin n → ℝ) → ℝ}
    (hv : ∀ T ∈ M.simplices, ∀ i, Continuous (v T i))
    (hw : ∀ T ∈ M.simplices, ∀ i, Continuous (w T i)) :
    pieceL2 M S v hv - pieceL2 M S w hw =
      pieceL2 M S (fun T i x => v T i x - w T i x)
        (fun T hT i => (hv T hT i).sub (hw T hT i)) := by
  refine PiLp.ext fun i => Lp.ext ?_
  filter_upwards [Lp.coeFn_sub (pieceL2 M S v hv i) (pieceL2 M S w hw i),
    coeFn_pieceL2 M S v hv i, coeFn_pieceL2 M S w hw i,
    coeFn_pieceL2 M S (fun T i x => v T i x - w T i x)
      (fun T hT i => (hv T hT i).sub (hw T hT i)) i] with x h1 h2 h3 h4
  rw [PiLp.sub_apply, h1, Pi.sub_apply, h2, h3, h4]
  simp only [pieceFun, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hx : x ∈ interior T.closedInterior
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-- `‖S(glue ψ) − glue u‖² ≤ Σ_T ‖S ψ_T − u_T‖²_{L²(T)}` on the cube meshes (`ψ` a vector of
`k`-forms, `u` a `(k+1)`-form). -/
theorem norm_sq_wsL2_sub_glue_le {N k : ℕ} (E E' : LocalElement n)
    (ψ : Fin n → E.Piecewise (mesh n N) k) (u : E'.Piecewise (mesh n N) (k + 1)) :
    ‖wsL2 (Ω := (mesh n N).domain) (k : ℤ) (E.tensorGlue (mesh n N) n (k : ℤ) ψ) -
        E'.glue (mesh n N) ((k : ℤ) + 1) u‖ ^ 2 ≤
      ∑ T : (mesh n N).simplices, formL2Sq (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior
        (coordWedgeField (fun a => ((ψ a T : E.space T k) : FormField n)) -
          ((u T : E'.space T (k + 1)) : FormField n)) := by
  rw [wsL2_tensorGlue]
  have hg : E'.glue (mesh n N) ((k : ℤ) + 1) u = pieceL2 (mesh n N) (mesh n N).domain
      (fun T => formComp (k := (k : ℤ) + 1) (E'.extendPW (mesh n N) u T))
      (fun T hT s => continuous_formComp (E'.contDiff_extendPW (mesh n N) u hT).continuous s) :=
    rfl
  rw [hg, pieceL2_sub]
  refine (norm_sq_pieceL2_le _ _ _ _).trans_eq ?_
  rw [← Finset.sum_coe_sort]
  refine Finset.sum_congr rfl fun T _ => ?_
  have hdeg : ∀ x, IsDeg (k + 1) ((coordWedgeField (fun a => ((ψ a T : E.space T k) : FormField n)) -
      ((u T : E'.space T (k + 1)) : FormField n)) x) := fun x s hs => by
    simp only [Pi.sub_apply]
    rw [isDeg_coordWedgeField (fun a x => E.isDeg_of_mem (ψ a T).2 x) x s hs,
      E'.isDeg_of_mem (u T).2 x s hs, sub_zero]
  refine Eq.trans ?_ (sum_formIdx_integral_eq_formL2Sq hdeg)
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [formComp, E.extendPW_of_mem _ _ T.2, E'.extendPW_of_mem _ _ T.2,
    coordWedgeField_apply, Pi.sub_apply]

/-- The local form of Prop 5.9(1): `‖(I − Π¹)S⁰ψ‖²_{L²(T)} ≤ C h² Σₐ ‖dψₐ‖²_{L²(T)}`. -/
theorem exists_formL2Sq_sub_wsPiecewise_zero_le : ∃ C, 0 ≤ C ∧ ∀ (N : ℕ)
    (ψ : Fin 3 → (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 N) 0)
    (T : (mesh 3 N).simplices),
    formL2Sq (T : Affine.Simplex ℝ (Fin 3 → ℝ) 3).closedInterior
      (coordWedgeField (fun a => ((ψ a T : (polyElement 3 PolySeq.lagrangeP2).space T 0) :
          FormField 3)) -
        ((PolySeq.lagrangeP2.wsPiecewise (mesh 3 N) 0 ψ T :
          (polyElement 3 PolySeq.lowestOrder).space T 1) : FormField 3)) ≤
      C * hN N ^ 2 * ∑ a, formL2Sq (T : Affine.Simplex ℝ (Fin 3 → ℝ) 3).closedInterior
        (extDeriv ((ψ a T : (polyElement 3 PolySeq.lagrangeP2).space T 0) : FormField 3)) := by
  obtain ⟨C, hC0, hC⟩ := exists_formL2Sq_sub_localInterp_le (n := 3) (k := 0) (r := 2)
    (by norm_num) (by norm_num)
  refine ⟨C, hC0, fun N ψ T => ?_⟩
  have hw : coordWedgeField (fun a => ((ψ a T : (polyElement 3 PolySeq.lagrangeP2).space T 0) :
      FormField 3)) ∈ polySpace 3 2 (0 + 1) :=
    coordWedgeField_mem_polySpace fun a => mem_polySpace_of_space _ (ψ a T)
  have h1 := hC N T hw
  rw [wsPiecewise_apply_eq _ _ _ hw]
  refine h1.trans_eq ?_
  rw [formGradL2Sq_coordWedgeField_zero (T : Affine.Simplex ℝ (Fin 3 → ℝ) 3).isCompact_closedInterior
    (r := 2) fun a => mem_polySpace_of_space _ (ψ a T)]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  exact formGradL2Sq_eq_formL2Sq_extDeriv ((polyElement 3 PolySeq.lagrangeP2).isDeg_of_mem (ψ a T).2)

theorem norm_sq_tensorGlue_dPiecewise {N : ℕ} (E : LocalElement n) {m : ℕ}
    (ψ : Fin m → E.Piecewise (mesh n N) 0) :
    ‖E.tensorGlue (mesh n N) m ((0 + 1 : ℕ) : ℤ) (fun a => E.dPiecewise (mesh n N) 0 (ψ a))‖ ^ 2 =
      ∑ a, ∑ T : (mesh n N).simplices, formL2Sq (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior
        (extDeriv ((ψ a T : E.space T 0) : FormField n)) := by
  rw [norm_sq_tensorGlue]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [norm_sq_glue_eq_int _ (by norm_num)]
  rfl

/-- **[QuennevilleBelair2015], Prop 5.9(1)**: `‖(I − Π¹) S⁰ψ‖_{L²(Q)} ≤ C h ‖∇ψ‖_{L²(Q)}` on
`P₂Λ⁰ ⊗ ℝ³`, `C` independent of the mesh (`S⁰ψ` is the `L²` field `wsL2 0`, `(I − Π¹) S⁰ψ` its
difference with `S₀,ₕψ = Π¹S⁰ψ`, and `∇ψ` the glued `dψ`). -/
theorem norm_sub_glue_bggS0h_le : ∃ C, 0 ≤ C ∧ ∀ (N : ℕ)
    (ψ : Fin 3 → (polyElement 3 PolySeq.lagrangeP2).globalSpace (mesh 3 N) 0),
    ‖wsL2 (Ω := (mesh 3 N).domain) ((0 : ℕ) : ℤ) ((polyElement 3 PolySeq.lagrangeP2).tensorGlue
        (mesh 3 N) 3 ((0 : ℕ) : ℤ) fun a =>
          ((ψ a : (polyElement 3 PolySeq.lagrangeP2).globalSpace (mesh 3 N) 0) :
            (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 N) 0)) -
      (polyElement 3 PolySeq.lowestOrder).glue (mesh 3 N) (((0 : ℕ) : ℤ) + 1)
        ((PolySeq.bggS0h (mesh 3 N) ψ :
          (polyElement 3 PolySeq.lowestOrder).globalSpace (mesh 3 N) 1) :
            (polyElement 3 PolySeq.lowestOrder).Piecewise (mesh 3 N) 1)‖ ≤
      C * hN N * ‖(polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 N) 3 ((0 + 1 : ℕ) : ℤ)
        fun a => (polyElement 3 PolySeq.lagrangeP2).dPiecewise (mesh 3 N) 0
          ((ψ a : (polyElement 3 PolySeq.lagrangeP2).globalSpace (mesh 3 N) 0) :
            (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 N) 0)‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_formL2Sq_sub_wsPiecewise_zero_le
  refine ⟨√C, Real.sqrt_nonneg _, fun N ψ => ?_⟩
  have hL := norm_sq_wsL2_sub_glue_le (N := N) (k := 0) (polyElement 3 PolySeq.lagrangeP2)
    (polyElement 3 PolySeq.lowestOrder) (fun a => (ψ a : _))
    ((PolySeq.bggS0h (mesh 3 N) ψ : (polyElement 3 PolySeq.lowestOrder).globalSpace (mesh 3 N) 1) :
      (polyElement 3 PolySeq.lowestOrder).Piecewise (mesh 3 N) 1)
  have hR := norm_sq_tensorGlue_dPiecewise (N := N) (polyElement 3 PolySeq.lagrangeP2)
    (fun a => (ψ a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 N) 0))
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
    (hN_pos N).le) (norm_nonneg _)) two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt hC0, hR]
  refine hL.trans ?_
  calc _ ≤ ∑ T : (mesh 3 N).simplices, C * hN N ^ 2 * ∑ a, formL2Sq
        (T : Affine.Simplex ℝ (Fin 3 → ℝ) 3).closedInterior
          (extDeriv (((ψ a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 N) 0) T :
            (polyElement 3 PolySeq.lagrangeP2).space T 0) : FormField 3)) :=
        Finset.sum_le_sum fun T _ => hC N _ T
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

end Prop59

/-! ### Strong approximation for `C¹` fields -/

section Strong

theorem globalInterp_apply_eq_localInterp (E : LocalElement n) (M : SimplicialMesh n) (k : ℕ)
    (w : contForms n) (T : M.simplices) :
    ((E.globalInterp M k w : E.Piecewise M k) T) = E.localInterp T k w :=
  E.localSpace_ext T k fun g hg i => by
    rw [LocalElement.localDof_globalInterp _ _ _ _ _ _ hg,
      LocalElement.localDof_localInterp _ _ _ _ _ hg]

end Strong

/-! ### `S` and the smoothing; injectivity of `grad` -/

section SmoothingInjective

/-- `u ↦ R̃ u` (extension by zero, mollification, dilation) as a linear map on `L²(Ω)`. -/
def smoothExtₗ {Ω : Set (Fin n → ℝ)} (p : SmoothingParam (Fin n → ℝ)) (hΩ : MeasurableSet Ω) :
    L2 ℝ Ω →ₗ[ℝ] (Fin n → ℝ) → ℝ where
  toFun u := smoothExt Ω p (u : (Fin n → ℝ) → ℝ)
  map_add' u v := smoothExt_coe_add hΩ u v
  map_smul' a u := smoothExt_coe_smul hΩ a u

theorem isDeg_smoothForm {Ω : Set (Fin n → ℝ)} (p : SmoothingParam (Fin n → ℝ))
    (hΩ : MeasurableSet Ω) (k : ℕ) (u : L2F ℝ Ω (formIdx n k)) (x : Fin n → ℝ) :
    IsDeg k ((smoothForm p hΩ (k : ℤ) u : FormField n) x) := fun s hs => by
  change formExt (smoothCoeff p (k : ℤ) u) s x = 0
  have : ¬ ((s.card : ℤ) = (k : ℤ)) := by exact_mod_cast hs
  simp [formExt, this]

/-- **`S` commutes with the smoothing up to the dilation factor**: `R S u = c S R̃ u`, with
`R`, `R̃` the smoothing of `L²` forms of degrees `k + 1`, `k` (`smoothForm`: extension by zero,
mollification, pullback by the dilation `x ↦ c (x − x₀) + x₀`) — the mollification commutes
with the constant-coefficient map `S`, and the dilation contributes the factor `c` of
`affinePullback_scalarMat_coordWedgeField`. -/
theorem smoothForm_wsL2 {Ω : Set (Fin n → ℝ)} (p : SmoothingParam (Fin n → ℝ))
    (hΩ : MeasurableSet Ω) (k : ℕ) (u : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n k))) :
    (smoothForm p hΩ ((k : ℤ) + 1) (wsL2 (Ω := Ω) (k : ℤ) u) : FormField n) =
      p.factor • coordWedgeField (fun a => (smoothForm p hΩ (k : ℤ) (u a) : FormField n)) := by
  have hc : p.factor ≠ 0 := by linarith [p.half_le_factor]
  funext x t
  change formExt (smoothCoeff p ((k : ℤ) + 1) (wsL2 (Ω := Ω) (k : ℤ) u)) t x = _
  rw [Pi.smul_apply, coordWedgeField_apply, Pi.smul_apply, smul_eq_mul]
  by_cases ht : (t.card : ℤ) = (k : ℤ) + 1
  · rw [formExt, dite_eq_left_of_eq_true (eq_true ht)]
    set t' : formIdx n ((k : ℤ) + 1) := ⟨t, ht⟩
    rw [coordWedgeSum_eq_sum_wsCoeff (fun a => isDeg_smoothForm p hΩ k (u a) x) t']
    change p.factor ^ ((k : ℤ) + 1) * smoothExtₗ p hΩ (wsL2 (Ω := Ω) (k : ℤ) u t') x = _
    rw [wsL2_apply, map_sum, Finset.sum_apply, Finset.mul_sum, Finset.mul_sum,
      zpow_add_one₀ hc]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    change _ = p.factor * (wsCoeff (k : ℤ) t' q *
      formExt (smoothCoeff p (k : ℤ) (u q.1)) q.2.1 x)
    rw [formExt_val]
    simp only [smoothCoeff, smoothExtₗ, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  · have h0 : ¬ (t.card = k + 1) := fun h => ht (by exact_mod_cast h)
    rw [formExt, dite_eq_right_of_eq_false (eq_false ht),
      isDeg_coordWedgeSum (fun a => isDeg_smoothForm p hΩ k (u a) x) t h0, mul_zero]
    rfl

theorem eq_zero_of_minimal_eq_zero_of_eq {Ω : Set (Fin 3 → ℝ)} (hΩ : Ω = cubeDomain 3)
    {x : ((extDerivOp ℝ 3 (0 : ℤ)).minimal Ω).domain}
    (hx : (extDerivOp ℝ 3 (0 : ℤ)).minimal Ω x = 0) : (x : L2F ℝ Ω (formIdx 3 (0 : ℤ))) = 0 := by
  subst hΩ
  exact D0_eq_zero hx

/-- **`d` is injective on `Λ̊_h⁰`** (any element family on the cube meshes): `ℌ⁰(H̊Λ(Q)) = 0`
and the glued fields of `Λ̊_h⁰` lie in `D(d_min)`. -/
theorem eq_zero_of_dPiecewise_eq_zero (E : LocalElement 3) (N : ℕ) (u : E.globalSpace₀ (mesh 3 N) 0)
    (hu : E.dPiecewise (mesh 3 N) 0 (u : E.Piecewise (mesh 3 N) 0) = 0) : u = 0 := by
  obtain ⟨h, hval⟩ := E.glue_mem_minimal (mesh 3 N) (isOpen_mesh_domain 3 N) (center 3)
    (strictStar_mesh 3 N) 0 u
  rw [hu, map_zero] at hval
  have h0 := eq_zero_of_minimal_eq_zero_of_eq (mesh_domain 3 N) hval
  have := E.glue_injective (mesh 3 N) (isOpen_mesh_domain 3 N) 0
    ((show E.glue (mesh 3 N) ((0 : ℕ) : ℤ) (u : E.Piecewise (mesh 3 N) 0) = 0 from h0).trans
      (map_zero _).symm)
  exact Subtype.ext this

/-- **`grad` is injective on `P₂Λ̊⁰ ⊗ ℝ³`** (row-wise; the injectivity used in the BGG
construction of [QuennevilleBelair2015], §5.3). -/
theorem eq_zero_of_dPiecewise_tensor_eq_zero (N : ℕ)
    (ψ : Fin 3 → (polyElement 3 PolySeq.lagrangeP2).globalSpace₀ (mesh 3 N) 0)
    (hψ : ∀ a, (polyElement 3 PolySeq.lagrangeP2).dPiecewise (mesh 3 N) 0
      (ψ a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 N) 0) = 0) : ψ = 0 :=
  funext fun a => eq_zero_of_dPiecewise_eq_zero _ N (ψ a) (hψ a)

end SmoothingInjective

/-! ### Prop 5.9(2) is false -/

section Prop59Two

/-! #### The reference field `Ẑ = S¹(0, 0, d(y₀²/2))` -/

/-- The polynomial `0`-form `y₀²/2`. -/
def refΩ : Koszul.PolyForm ℝ (Fin 3) :=
  fun s => if s = ∅ then MvPolynomial.C (1 / 2 : ℝ) * MvPolynomial.X 0 * MvPolynomial.X 0 else 0

def refQ : FormField 3 := evalForm 3 refΩ

theorem refQ_mem : refQ ∈ polySpace 3 2 0 := by
  refine ⟨refΩ, ⟨fun s hs => ?_, fun s => ?_⟩, rfl⟩
  · simp [refΩ]; intro h; subst h; simp at hs
  · simp only [refΩ]
    split_ifs
    · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      refine (add_le_add (MvPolynomial.totalDegree_mul _ _) le_rfl).trans ?_
      simp
    · simp

theorem extDeriv_refQ_zero (y : Fin 3 → ℝ) : extDeriv refQ y {0} = y 0 := by
  rw [extDeriv_apply, Finset.sum_singleton, Finset.erase_singleton]
  simp only [ExteriorFibre.sgn, Finset.filter_singleton]
  have : partialDeriv 0 (fun z => refQ z ∅) y = y 0 := by
    change partialDeriv 0 (fun z => MvPolynomial.eval z (refΩ ∅)) y = y 0
    rw [partialDeriv_eval]
    simp [refΩ]
    ring
  simp [this]


/-- The reference field `Ẑ = S¹(0, 0, dQ)`, `Q(y) = y₀²/2`. -/
def refZ : FormField 3 := coordWedgeField (Pi.single (2 : Fin 3) (extDeriv refQ))

theorem refZ_apply (y : Fin 3 → ℝ) : refZ y {0, 2} = -(y 0) := by
  rw [refZ, coordWedgeField_apply, coordWedgeSum_pair (by decide : (0 : Fin 3) < 2)]
  simp [extDeriv_refQ_zero]

theorem refZ_mem : refZ ∈ polySpace 3 1 2 := by
  refine coordWedgeField_mem_polySpace (k := 1) fun a => ?_
  by_cases ha : a = 2
  · subst ha
    simpa using extDeriv_mem_polySpace refQ_mem
  · simp [ha]

/-- The coefficient of `dy₀ ∧ dy₂` of a trimmed linear `2`-form does not depend on `y₀`. -/
theorem apply_single_eq_of_mem_p1MinusForms {u : FormField 3} (hu : u ∈ p1MinusForms 3 2) :
    u (Pi.single 0 1) {0, 2} = u 0 {0, 2} := by
  induction hu using Submodule.span_induction with
  | mem w hw =>
    rcases hw with ⟨α, -, rfl⟩ | ⟨β, -, rfl⟩
    · rfl
    · change interior (Pi.single 0 1) β {0, 2} = interior 0 β {0, 2}
      rw [interior_apply, interior_apply]
      refine (Finset.sum_eq_zero fun j hj => ?_).trans (Finset.sum_eq_zero fun j _ => by simp).symm
      have hj0 : j ≠ 0 := by rintro rfl; simp at hj
      simp [hj0]
  | zero => rfl
  | add w w' _ _ hw hw' => simp [hw, hw']
  | smul c w _ hw => simp [hw]

theorem refZ_notMem : refZ ∉ p1MinusForms 3 2 := fun h => by
  have := apply_single_eq_of_mem_p1MinusForms h
  rw [refZ_apply, refZ_apply] at this
  simp at this

theorem polyMinusSpace_one_le : polyMinusSpace 3 1 2 ≤ p1MinusForms 3 2 := by
  rw [polyMinusSpace, ← whitneySpace_refVertex_eq_map_polyFormMinus]
  exact whitneySpace_le_p1MinusForms _ _


/-- The reference simplex `K₁ = lex(Kuhn(id))`. -/
abbrev refK : Affine.Simplex ℝ (Fin 3 → ℝ) 3 := kuhnLex (1 : Equiv.Perm (Fin 3))

theorem refZ_mem_contDegForms : refZ ∈ contDegForms 3 2 := polySpace_le_contDegForms 1 2 refZ_mem

/-- `c₀ = ‖Ẑ − Π Ẑ‖²_{L²(K₁)}`, `Π` the interpolant of `P₁⁻Λ²(K₁)`. -/
def refGap : ℝ :=
  formL2Sq refK.closedInterior (refZ - (polyMinusInterp (isUnit_det_edgeMatrix refK) (r := 1)
    le_rfl (by norm_num : 2 ≤ 3) ⟨refZ, refZ_mem_contDegForms⟩ : FormField 3))

theorem refGap_pos : 0 < refGap := by
  set P := (polyMinusInterp (isUnit_det_edgeMatrix refK) (r := 1)
    le_rfl (by norm_num : 2 ≤ 3) ⟨refZ, refZ_mem_contDegForms⟩ : FormField 3)
  have hPm : P ∈ polyMinusSpace 3 1 2 := mem_polyMinusSpace_of_mem_localPolyMinusSpace
    (isUnit_det_edgeMatrix refK) (polyMinusInterp (isUnit_det_edgeMatrix refK) (r := 1)
      le_rfl (by norm_num : 2 ≤ 3) ⟨refZ, refZ_mem_contDegForms⟩).2
  have hu : refZ - P ∈ polySpace 3 1 2 :=
    Submodule.sub_mem _ refZ_mem (polyMinusSpace_le_polySpace le_rfl hPm)
  have hK := refK.isCompact_closedInterior
  refine lt_of_le_of_ne (formL2Sq_nonneg hK.measurableSet _) fun h0 => ?_
  have hinj := l2EmbedOf_injective_of_le_polySpace (le_refl (polySpace 3 1 2)) hK
    (interior_closedInterior_nonempty refK)
  have hn := norm_sq_l2EmbedOf (polySpace 3 1 2) (polySpace_le_contForms 1 2) hK ⟨_, hu⟩
  have h1 : l2EmbedOf (polySpace 3 1 2) (polySpace_le_contForms 1 2) hK ⟨_, hu⟩ = 0 := by
    rw [← norm_eq_zero, ← sq_eq_zero_iff, hn]
    exact h0.symm
  have h2 : (⟨_, hu⟩ : polySpace 3 1 2) = 0 := hinj (h1.trans (map_zero _).symm)
  have h3 : refZ = P := sub_eq_zero.1 (congrArg Subtype.val h2)
  exact refZ_notMem (polyMinusSpace_one_le (h3 ▸ hPm))


theorem affinePullback_scalarMat_inv {h : ℝ} (hh : h ≠ 0) (t : Fin 3 → ℝ) (w : FormField 3) :
    affinePullback (scalarMat 3 h) t (affinePullback (scalarMat 3 h⁻¹) (-(h⁻¹ • t)) w) = w := by
  rw [affinePullback_affinePullback]
  have e1 : (fun j l => ∑ i, scalarMat 3 h⁻¹ j i * scalarMat 3 h i l) =
      fun i j : Fin 3 => if i = j then (1 : ℝ) else 0 := by
    funext j l
    simp only [scalarMat, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    split_ifs <;> simp [inv_mul_cancel₀ hh]
  have e2 : affine (scalarMat 3 h⁻¹) (-(h⁻¹ • t)) t = 0 := by
    rw [affine_scalarMat]; simp
  rw [e1, e2, affinePullback_id]

theorem formL2Sq_smul (S : Set (Fin 3 → ℝ)) (c : ℝ) (u : FormField 3) :
    formL2Sq S (c • u) = c ^ 2 * formL2Sq S u := by
  simp only [formL2Sq, Pi.smul_apply, smul_eq_mul, mul_pow, integral_const_mul, Finset.mul_sum]

/-- **The local gap on a scaled simplex**: if `H^* Z = h Ẑ` for `T = t + h K_id`, then
`‖Z − Π_T Z‖²_{L²(T)} = h c₀`. -/
theorem formL2Sq_sub_localInterp_of_pullback {h : ℝ} (hh : 0 < h) (t : Fin 3 → ℝ)
    {T : Affine.Simplex ℝ (Fin 3 → ℝ) 3}
    (hT : T = mapEquiv (boxMap t h hh.ne') (kuhnSimplex (1 : Equiv.Perm (Fin 3))))
    {Z : FormField 3} (hZ : Z ∈ polySpace 3 1 2)
    (hpull : affinePullback (scalarMat 3 h) t Z = h • refZ) :
    formL2Sq T.closedInterior
      (Z - (((polyElement 3 PolySeq.lowestOrder).localInterp T (1 + 1)
          ⟨Z, (polySpace_le_contDegForms 1 2 hZ).1⟩ :
          (polyElement 3 PolySeq.lowestOrder).space _ (1 + 1)) : FormField 3)) = h * refGap := by
  subst hT
  set K := kuhnSimplex (1 : Equiv.Perm (Fin 3))
  have hZc : Z ∈ contDegForms 3 2 := polySpace_le_contDegForms 1 2 hZ
  have hid := localInterp_lowestOrder_eq K t hh (k := 1) (by norm_num) ⟨Z, hZc⟩
  rw [hid, ← closedInterior_mapEquiv_lexSimplex K t hh.ne']
  set q := mapEquiv (boxMap t h hh.ne') (lexSimplex K)
  set P := (polyMinusInterp (isUnit_det_edgeMatrix q) (PolySeq.lowestOrder.one_le_deg (1 + 1))
    (by norm_num : 1 + 1 ≤ 3) ⟨Z, hZc⟩ : FormField 3)
  have hnat : affinePullback (scalarMat 3 h) t P =
      (polyMinusInterp (isUnit_det_edgeMatrix refK) (PolySeq.lowestOrder.one_le_deg (1 + 1))
        (by norm_num : 1 + 1 ≤ 3) ⟨affinePullback (scalarMat 3 h) t Z,
          affinePullback_mem_contDegForms _ _ hZc⟩ : FormField 3) :=
    affinePullback_polyMinusInterp (isUnit_det_edgeMatrix refK) (isUnit_det_edgeMatrix q)
      (scalarMat 3 h) t (points_mapEquiv_boxMap refK t hh.ne') _ _ ⟨Z, hZc⟩
  have hsm : (⟨affinePullback (scalarMat 3 h) t Z, affinePullback_mem_contDegForms _ _ hZc⟩ :
      contDegForms 3 (1 + 1)) = h • ⟨refZ, refZ_mem_contDegForms⟩ := Subtype.ext hpull
  have hsub : affinePullback (scalarMat 3 h) t (Z - P) =
      h • (refZ - (polyMinusInterp (isUnit_det_edgeMatrix refK) (r := 1)
        le_rfl (by norm_num : 2 ≤ 3) ⟨refZ, refZ_mem_contDegForms⟩ : FormField 3)) := by
    have e := (affinePullbackₗ (scalarMat 3 h) t).map_sub Z P
    simp only [affinePullbackₗ_apply] at e
    rw [e, hnat, hsm, map_smul, hpull, smul_sub]
    rfl
  have hPdeg : ∀ x, IsDeg 2 (P x) := isDeg_of_mem_polySpace (polyMinusSpace_le_polySpace
    (r := 1) le_rfl (mem_polyMinusSpace_of_mem_localPolyMinusSpace (isUnit_det_edgeMatrix q)
      (polyMinusInterp (isUnit_det_edgeMatrix q) (PolySeq.lowestOrder.one_le_deg (1 + 1))
        (by norm_num : 1 + 1 ≤ 3) ⟨Z, hZc⟩).2))
  have hdeg : ∀ x, IsDeg 2 ((Z - P) x) := fun x s hs => by
    simp only [Pi.sub_apply]
    rw [isDeg_of_mem_polySpace hZ x s hs, hPdeg x s hs, sub_zero]
  have key := formL2Sq_affinePullback_scalarMat refK hh t hdeg
  rw [hsub, formL2Sq_smul] at key
  change h ^ 3 * (h ^ 2 * refGap) = (h ^ 2) ^ 2 * formL2Sq q.closedInterior (Z - P) at key
  have h4 : 0 < (h ^ 2) ^ 2 := by positivity
  refine (mul_left_cancel₀ h4.ne' ?_)
  rw [← key]
  ring


/-! #### Projection independence: the `L²` distance of `Ẑ` to `P₁⁻Λ²` -/

/-- The `L²(K₁)` map of `P₁Λ²`. -/
abbrev refEmb : polySpace 3 1 2 →ₗ[ℝ] Domain.L2F ℝ refK.closedInterior (Finset (Fin 3)) :=
  l2EmbedOf (polySpace 3 1 2) (polySpace_le_contForms 1 2) refK.isCompact_closedInterior

/-- The image of `P₁⁻Λ² ⊆ P₁Λ²` in `L²(K₁)` (finite-dimensional, hence closed). -/
def refMinusL2 : Submodule ℝ (Domain.L2F ℝ refK.closedInterior (Finset (Fin 3))) :=
  ((polyMinusSpace 3 1 2).comap (polySpace 3 1 2).subtype).map refEmb

/-- `δ₀ = dist_{L²(K₁)}(Ẑ, P₁⁻Λ²)`: the distance of `Ẑ` to the whole lowest-order
Raviart–Thomas space, not only to its canonical interpolant (compare `refGap`). -/
def refDist : ℝ := Metric.infDist (refEmb ⟨refZ, refZ_mem⟩) (refMinusL2 : Set _)

theorem refDist_pos : 0 < refDist := by
  have : FiniteDimensional ℝ ((polyMinusSpace 3 1 2).comap (polySpace 3 1 2).subtype) :=
    inferInstance
  have : FiniteDimensional ℝ refMinusL2 := Module.Finite.map _ _
  have hc : IsClosed (refMinusL2 : Set (Domain.L2F ℝ refK.closedInterior (Finset (Fin 3)))) :=
    Submodule.closed_of_finiteDimensional _
  refine (hc.notMem_iff_infDist_pos ⟨0, refMinusL2.zero_mem⟩).1 fun h => ?_
  obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.1 h
  have hinj := l2EmbedOf_injective_of_le_polySpace (le_refl (polySpace 3 1 2))
    refK.isCompact_closedInterior (interior_closedInterior_nonempty refK)
  have : p = ⟨refZ, refZ_mem⟩ := hinj hpe
  subst this
  exact refZ_notMem (polyMinusSpace_one_le hp)

/-- `‖Ẑ − p‖²_{L²(K₁)} ≥ δ₀²` for every `p ∈ P₁⁻Λ²`. -/
theorem refDist_sq_le {p : FormField 3} (hp : p ∈ polyMinusSpace 3 1 2) :
    refDist ^ 2 ≤ formL2Sq refK.closedInterior (refZ - p) := by
  have hpp : p ∈ polySpace 3 1 2 := polyMinusSpace_le_polySpace le_rfl hp
  have hmem : refEmb ⟨p, hpp⟩ ∈ refMinusL2 := Submodule.mem_map_of_mem (by exact hp)
  have h1 := Metric.infDist_le_dist_of_mem (x := refEmb ⟨refZ, refZ_mem⟩) hmem
  rw [dist_eq_norm, ← map_sub] at h1
  have hn := norm_sq_l2EmbedOf (polySpace 3 1 2) (polySpace_le_contForms 1 2)
    refK.isCompact_closedInterior ⟨refZ - p, Submodule.sub_mem _ refZ_mem hpp⟩
  have e : (⟨refZ, refZ_mem⟩ - ⟨p, hpp⟩ : polySpace 3 1 2) =
      ⟨refZ - p, Submodule.sub_mem _ refZ_mem hpp⟩ := rfl
  rw [e] at h1
  rw [← hn]
  exact pow_le_pow_left₀ Metric.infDist_nonneg h1 2

/-- **The local best-approximation gap on a scaled simplex**: if `H^* Z = h Ẑ` for
`T = t + h K_id`, then `‖Z − w‖²_{L²(T)} ≥ h δ₀²` for every `w ∈ P₁⁻Λ²`. -/
theorem mul_refDist_sq_le_formL2Sq {h : ℝ} (hh : 0 < h) (t : Fin 3 → ℝ)
    {Z : FormField 3} (hZ : Z ∈ polySpace 3 1 2)
    (hpull : affinePullback (scalarMat 3 h) t Z = h • refZ)
    {w : FormField 3} (hw : w ∈ polyMinusSpace 3 1 2) :
    h * refDist ^ 2 ≤ formL2Sq
      (mapEquiv (boxMap t h hh.ne') (kuhnSimplex (1 : Equiv.Perm (Fin 3)))).closedInterior
        (Z - w) := by
  rw [← closedInterior_mapEquiv_lexSimplex _ t hh.ne']
  have hwp : w ∈ polySpace 3 1 2 := polyMinusSpace_le_polySpace le_rfl hw
  have hdeg : ∀ x, IsDeg 2 ((Z - w) x) := fun x s hs => by
    simp only [Pi.sub_apply]
    rw [isDeg_of_mem_polySpace hZ x s hs, isDeg_of_mem_polySpace hwp x s hs, sub_zero]
  have key := formL2Sq_affinePullback_scalarMat refK hh t hdeg
  have hp : h⁻¹ • affinePullback (scalarMat 3 h) t w ∈ polyMinusSpace 3 1 2 :=
    Submodule.smul_mem _ _ (affinePullback_mem_polyMinusSpace_scalarMat h t hw)
  have hsub : affinePullback (scalarMat 3 h) t (Z - w) =
      h • (refZ - h⁻¹ • affinePullback (scalarMat 3 h) t w) := by
    have e := (affinePullbackₗ (scalarMat 3 h) t).map_sub Z w
    simp only [affinePullbackₗ_apply] at e
    rw [e, hpull, smul_sub, smul_inv_smul₀ hh.ne']
  rw [hsub, formL2Sq_smul] at key
  have hd := refDist_sq_le hp
  have h4 : 0 < (h ^ 2) ^ 2 := by positivity
  refine le_of_mul_le_mul_left ?_ h4
  rw [← key]
  have e1 : (h ^ 2) ^ 2 * (h * refDist ^ 2) = h ^ 5 * refDist ^ 2 := by ring
  have e2 : h ^ 3 * (h ^ 2 * formL2Sq refK.closedInterior
      (refZ - h⁻¹ • affinePullback (scalarMat 3 h) t w)) =
      h ^ 5 * formL2Sq refK.closedInterior (refZ - h⁻¹ • affinePullback (scalarMat 3 h) t w) := by
    ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left hd (by positivity)

/-- The centre `p₀ = (½, ½, ½)` of the reference cube `[0, 1]³`. -/
abbrev refCenter : Fin 3 → ℝ := fun _ => 1 / 2

/-- A smooth bump, `= 1` on `[0, 1]³ = B̄_∞(p₀, ½)` and supported in `B_∞(p₀, 1)`. -/
def refBump : ContDiffBump refCenter where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The reference profile `F = χ Q`. -/
def refF : FormField 3 := fun y => refBump y • refQ y

theorem contDiff_refQ {r : WithTop ℕ∞} : ContDiff ℝ r refQ := contDiff_evalForm refΩ

theorem contDiff_refF {r : ℕ∞} : ContDiff ℝ r refF :=
  contDiff_pi.2 fun s => (refBump.contDiff (n := r)).mul (contDiff_pi.1 contDiff_refQ s)

theorem isDeg_refQ (y : Fin 3 → ℝ) : IsDeg 0 (refQ y) := isDeg_of_mem_polySpace refQ_mem y

theorem isDeg_refF (y : Fin 3 → ℝ) : IsDeg 0 (refF y) := fun s hs => by
  simp [refF, isDeg_refQ y s hs]

theorem refF_eq_refQ {y : Fin 3 → ℝ} (hy : y ∈ Metric.closedBall refCenter (1 / 2)) :
    refF y = refQ y := by
  simp [refF, refBump.one_of_mem_closedBall hy]

theorem extDeriv_refF_eq_zero {y : Fin 3 → ℝ} (hy : y ∉ Metric.closedBall refCenter 1) :
    extDeriv refF y = 0 := by
  funext s
  rw [extDeriv_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hts : y ∉ tsupport fun z => refF z (s.erase j) := fun h => hy (by
    have := tsupport_mul_subset_left (f := fun z => refBump z) (g := fun z => refQ z (s.erase j)) h
    rwa [refBump.tsupport_eq] at this)
  rw [partialDeriv_eq_zero_of_notMem_tsupport hts]
  simp

theorem exists_bound_extDeriv_refF : ∃ G, 0 ≤ G ∧ ∀ y, ‖extDeriv refF y‖ ≤ G := by
  have hc : Continuous (extDeriv refF) := continuous_extDeriv (contDiff_refF (r := 1))
  obtain ⟨G, hG⟩ := (isCompact_closedBall refCenter (1 : ℝ)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max G 0, le_max_right _ _, fun y => ?_⟩
  by_cases hy : y ∈ Metric.closedBall refCenter 1
  · exact (hG y hy).trans (le_max_left _ _)
  · rw [extDeriv_refF_eq_zero hy, norm_zero]; exact le_max_right _ _


/-! #### The counterexample fields on the level-`(N + 3)` meshes -/

/-- The lattice index `(1, 1, 1)`. -/
def cornerIdx (N : ℕ) : Fin 3 → Fin (N + 2 + 1) := fun _ => ⟨1, by omega⟩

/-- The corner `t_N = h (1, 1, 1)` of the simplex `T₀ = t_N + h K_id`. -/
def corner (N : ℕ) : Fin 3 → ℝ := hN (N + 2) • latticePoint (finLattice (cornerIdx N))

theorem corner_apply (N : ℕ) (i : Fin 3) : corner N i = hN (N + 2) := by
  simp [corner, latticePoint_apply, finLattice, cornerIdx]

/-- The simplex `T₀ = t_N + h_N K_id`. -/
abbrev simplex₀ (N : ℕ) : Affine.Simplex ℝ (Fin 3 → ℝ) 3 :=
  cubeSimplex (N + 2) (cornerIdx N) 1

theorem simplex₀_eq (N : ℕ) : simplex₀ N =
    mapEquiv (boxMap (corner N) (hN (N + 2)) (hN_pos (N + 2)).ne') (kuhnSimplex 1) :=
  cubeSimplex_eq _ _ _

/-- The rescaled coordinates `y = h⁻¹ (x − t_N)`. -/
def resc (N : ℕ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (hN (N + 2))⁻¹ • x + -((hN (N + 2))⁻¹ • corner N)

theorem resc_apply (N : ℕ) (x : Fin 3 → ℝ) (i : Fin 3) :
    resc N x i = x i / hN (N + 2) - 1 := by
  have h := (hN_pos (N + 2)).ne'
  simp only [resc, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, corner_apply]
  field_simp
  ring

/-- The pullback of a field to the mesh scale: `x ↦ G(h⁻¹ (x − t_N))`. -/
def scaled (N : ℕ) (G : FormField 3) : FormField 3 :=
  affinePullback (scalarMat 3 (hN (N + 2))⁻¹) (-((hN (N + 2))⁻¹ • corner N)) G

theorem scaled_apply_of_isDeg_zero (N : ℕ) {G : FormField 3} (hG : ∀ y, IsDeg 0 (G y))
    (x : Fin 3 → ℝ) : scaled N G x = G (resc N x) := by
  rw [scaled, affinePullback_scalarMat _ _ hG, pow_zero, one_smul]
  rfl

theorem extDeriv_scaled (N : ℕ) {G : FormField 3} (hG : Differentiable ℝ G)
    (hG0 : ∀ y, IsDeg 0 (G y)) (x : Fin 3 → ℝ) :
    extDeriv (scaled N G) x = (hN (N + 2))⁻¹ • extDeriv G (resc N x) := by
  rw [scaled, extDeriv_affinePullback_apply _ _ (hG _),
    affinePullback_scalarMat _ _ (fun y => IsDeg.extDeriv hG0 y), pow_one]
  rfl

theorem pullback_scaled (N : ℕ) (G : FormField 3) :
    affinePullback (scalarMat 3 (hN (N + 2))) (corner N) (scaled N G) = G :=
  affinePullback_scalarMat_inv (hN_pos (N + 2)).ne' _ G

theorem resc_mem_closedBall {N : ℕ} {x : Fin 3 → ℝ} (hx : x ∈ (simplex₀ N).closedInterior) :
    resc N x ∈ Metric.closedBall refCenter (1 / 2) := by
  rw [mem_closedInterior_cubeSimplex] at hx
  rw [Metric.mem_closedBall, dist_pi_le_iff (by norm_num)]
  intro i
  have h01 := hx.1 i
  have hh := hN_pos (N + 2)
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, latticePoint_apply, finLattice,
    cornerIdx] at h01
  rw [Real.dist_eq, resc_apply, abs_le]
  have e : (hN (N + 2))⁻¹ * x i = x i / hN (N + 2) := by rw [inv_mul_eq_div]
  rw [e] at h01
  push_cast at h01
  constructor <;> linarith [h01.1, h01.2]

/-- The profile at the mesh scale, `f_N(x) = F(h⁻¹(x − t_N))`. -/
def fN (N : ℕ) : FormField 3 := scaled N refF

/-- The quadratic `q_N(x) = Q(h⁻¹(x − t_N))`. -/
def qN (N : ℕ) : FormField 3 := scaled N refQ

theorem fN_eq_qN {N : ℕ} {x : Fin 3 → ℝ} (hx : x ∈ (simplex₀ N).closedInterior) :
    fN N x = qN N x := by
  rw [fN, qN, scaled_apply_of_isDeg_zero _ isDeg_refF, scaled_apply_of_isDeg_zero _ isDeg_refQ,
    refF_eq_refQ (resc_mem_closedBall hx)]

theorem fN_eq_zero_of_notMem {N : ℕ} {x : Fin 3 → ℝ} (hx : x ∉ cubeDomain 3) : fN N x = 0 := by
  rw [fN, scaled_apply_of_isDeg_zero _ isDeg_refF]
  have hy : resc N x ∉ Metric.ball refCenter 1 := by
    simp only [cubeDomain, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, not_forall,
      not_and_or, not_lt] at hx
    obtain ⟨i, hi⟩ := hx
    rw [Metric.mem_ball, not_lt]
    refine le_trans ?_ (dist_le_pi_dist _ _ i)
    rw [Real.dist_eq, resc_apply]
    have hh := hN_pos (N + 2)
    have hinv : 1 / 2 / hN (N + 2) = ((N + 2 + 1 : ℕ) : ℝ) := by
      unfold hN; field_simp
    rcases hi with hi | hi
    · have : x i / hN (N + 2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hi hh.le
      rw [abs_of_neg (by linarith)]; linarith
    · have : 1 / 2 / hN (N + 2) ≤ x i / hN (N + 2) := div_le_div_of_nonneg_right hi hh.le
      rw [hinv] at this
      push_cast at this
      rw [abs_of_pos (by linarith)]; linarith
  have : refBump (resc N x) = 0 := by
    by_contra h
    exact hy (refBump.support_eq ▸ h)
  simp [refF, this]


theorem extDeriv_fN (N : ℕ) (x : Fin 3 → ℝ) :
    extDeriv (fN N) x = (hN (N + 2))⁻¹ • extDeriv refF (resc N x) :=
  extDeriv_scaled N (contDiff_refF (r := 1)).differentiable_one isDeg_refF x

/-- The centre `c_N = t_N + h_N p₀` of the cube of `T₀`. -/
def centerN (N : ℕ) : Fin 3 → ℝ := corner N + hN (N + 2) • refCenter

theorem norm_extDeriv_fN_le {G : ℝ} (hG : ∀ y, ‖extDeriv refF y‖ ≤ G) (N : ℕ)
    (x : Fin 3 → ℝ) : ‖extDeriv (fN N) x‖ ≤ (hN (N + 2))⁻¹ * G := by
  rw [extDeriv_fN, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (hN_pos _).le)]
  exact mul_le_mul_of_nonneg_left (hG _) (inv_nonneg.2 (hN_pos _).le)

theorem extDeriv_fN_eq_zero {N : ℕ} {x : Fin 3 → ℝ} (hx : 2 * hN (N + 2) < dist x (centerN N)) :
    extDeriv (fN N) x = 0 := by
  rw [extDeriv_fN, extDeriv_refF_eq_zero, smul_zero]
  have hh := hN_pos (N + 2)
  have e : resc N x - refCenter = (hN (N + 2))⁻¹ • (x - centerN N) := by
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, centerN, Pi.add_apply, resc_apply,
      corner_apply]
    field_simp
    ring
  rw [Metric.mem_closedBall, not_le, dist_eq_norm, e, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.2 hh.le), ← dist_eq_norm]
  rw [lt_inv_mul_iff₀ hh]
  linarith

/-- **`L∞`-stability of the canonical interpolant** of a global family on the cube meshes:
`|(Π_h w)_T| ≤ A sup_T |w|` on every simplex, `A` independent of the mesh. -/
theorem exists_abs_globalInterp_le (S : PolySeq) (k : ℕ) :
    ∃ A, 0 ≤ A ∧ ∀ (N : ℕ) (T : (mesh n N).simplices) (w : contForms n) {β : ℝ}, 0 ≤ β →
      (∀ x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ∀ s,
        |(w : FormField n) x s| ≤ β) →
      ∀ x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ∀ s,
        |((((polyElement n S).globalInterp (mesh n N) k w : (polyElement n S).Piecewise
          (mesh n N) k) T : (polyElement n S).space T k) : FormField n) x s| ≤ A * β := by
  obtain ⟨B, hB0, hB⟩ := Poly.exists_dofBound (n := n) S k
  obtain ⟨D, hD0, hD⟩ := Poly.exists_coeffBound (n := n) S k
  refine ⟨B * Module.finrank ℝ (S.space n k) * D, by positivity, fun N T w β hβ hw x hx s => ?_⟩
  set Iw : (polyElement n S).space T k := (((polyElement n S).globalInterp (mesh n N) k w :
    (polyElement n S).Piecewise (mesh n N) k) T)
  have hIw : (Iw : FormField n) ∈ S.space n k := Iw.2
  have hdof : ∀ g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n), ∀ i : S.DofIdx g k,
      |S.dof g k i ⟨Iw, S.space_le_contForms n k hIw⟩| ≤ hN N ^ k * (D * β) := by
    intro g hgT i
    have e1 : S.dof g k i ⟨(Iw : FormField n), S.space_le_contForms n k hIw⟩ = S.dof g k i w :=
      (polyElement n S).localDof_globalInterp (mesh n N) k w T g hgT i
    rw [e1]
    refine (Poly.abs_dof_le S hD T.2 hgT i w hβ hw).trans (le_of_eq (by ring))
  have := Poly.abs_le_of_abs_dof_le S hB hB0 T.2 hIw hdof hx s
  rw [← mul_assoc] at this
  exact this


theorem qN_mem (N : ℕ) : qN N ∈ polySpace 3 2 0 := affinePullback_mem_polySpace _ _ refQ_mem

theorem contDiff_fN (N : ℕ) : ContDiff ℝ 1 (fN N) :=
  contDiff_affinePullback _ _ (contDiff_refF (r := 1))

/-- `f_N` as a `C¹` form. -/
def fN1 (N : ℕ) : c1Forms 3 := ⟨fN N, contDiff_fN N⟩

/-- `φ_N = Π̃⁰ f_N ∈ P₂Λ̊⁰`. -/
def phiN (N : ℕ) : (polyElement 3 PolySeq.lagrangeP2).globalSpace (mesh 3 (N + 2)) 0 :=
  (polyElement 3 PolySeq.lagrangeP2).globalInterp (mesh 3 (N + 2)) 0
    (Submodule.inclusion c1Forms_le_contForms (fN1 N))

/-- **The counterexample** `v_N = (0, 0, grad φ_N) ∈ P₂⁻Λ¹ ⊗ ℝ³`. -/
def vN (N : ℕ) : Fin 3 → (polyElement 3 PolySeq.lagrangeP2).globalSpace (mesh 3 (N + 2)) 1 :=
  Pi.single 2 ((polyElement 3 PolySeq.lagrangeP2).dGlobal (mesh 3 (N + 2)) 0 (phiN N))

theorem vN_two (N : ℕ) : vN N 2 = (polyElement 3 PolySeq.lagrangeP2).globalInterp (mesh 3 (N + 2)) 1
    (extDerivC1 (fN1 N)) := by
  rw [vN, Pi.single_eq_same, phiN, LocalElement.globalInterp_extDeriv]

theorem vN_ne_two {N : ℕ} {a : Fin 3} (ha : a ≠ 2) : vN N a = 0 := by
  rw [vN, Pi.single_eq_of_ne ha]

/-- `T₀` as a mesh simplex. -/
def simplex₀' (N : ℕ) : (mesh 3 (N + 2)).simplices :=
  ⟨simplex₀ N, cubeSimplex_mem _ _ _⟩

theorem phiN_simplex₀ (N : ℕ) :
    ((((phiN N : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 0) (simplex₀' N)) :
      (polyElement 3 PolySeq.lagrangeP2).space _ 0) : FormField 3) = qN N := by
  have hq : qN N ∈ (polyElement 3 PolySeq.lagrangeP2).space (simplex₀ N) 0 := qN_mem N
  have : ((phiN N : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 0) (simplex₀' N)) =
      ⟨qN N, hq⟩ := by
    refine (polyElement 3 PolySeq.lagrangeP2).localSpace_ext _ 0 fun g hg i => ?_
    rw [phiN, LocalElement.localDof_globalInterp _ _ _ _ _ _ hg, LocalElement.localDof_apply]
    refine (polyElement 3 PolySeq.lagrangeP2).dof_congr i fun x hx V _ => ?_
    have hxT : x ∈ (simplex₀ N).closedInterior := by
      rw [← convexHull_vertexSet]
      exact convexHull_mono (Finset.coe_subset.2 hg) hx
    change pullback V (fN N x) Finset.univ = pullback V (qN N x) Finset.univ
    rw [fN_eq_qN hxT]
  rw [this]


/-- `Z_N = S¹(0, 0, d q_N)`. -/
def ZN (N : ℕ) : FormField 3 := coordWedgeField (Pi.single (2 : Fin 3) (extDeriv (qN N)))

theorem vN_simplex₀ (N : ℕ) (a : Fin 3) :
    (((vN N a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1) (simplex₀' N) :
      (polyElement 3 PolySeq.lagrangeP2).space _ 1) : FormField 3) =
      (Pi.single (2 : Fin 3) (extDeriv (qN N)) : Fin 3 → FormField 3) a := by
  by_cases ha : a = 2
  · subst ha
    rw [Pi.single_eq_same, vN, Pi.single_eq_same]
    change extDeriv (((phiN N : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 0)
      (simplex₀' N) : (polyElement 3 PolySeq.lagrangeP2).space _ 0) : FormField 3) = _
    rw [phiN_simplex₀]
  · rw [vN_ne_two ha, Pi.single_eq_of_ne ha]
    rfl

theorem coordWedgeField_vN_simplex₀ (N : ℕ) :
    coordWedgeField (fun a => (((vN N a : (polyElement 3 PolySeq.lagrangeP2).Piecewise
      (mesh 3 (N + 2)) 1) (simplex₀' N) : (polyElement 3 PolySeq.lagrangeP2).space _ 1) :
        FormField 3)) = ZN N :=
  congrArg coordWedgeField (funext (vN_simplex₀ N))

theorem ZN_mem (N : ℕ) : ZN N ∈ polySpace 3 1 2 := by
  refine coordWedgeField_mem_polySpace (k := 1) fun a => ?_
  by_cases ha : a = 2
  · subst ha
    simpa using extDeriv_mem_polySpace (qN_mem N)
  · simp [ha]

theorem affinePullback_zero {m : ℕ} (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) :
    affinePullback B b (0 : FormField n) = 0 := by
  simpa using affinePullback_smul B b 0 (0 : FormField n)

theorem pullback_ZN (N : ℕ) :
    affinePullback (scalarMat 3 (hN (N + 2))) (corner N) (ZN N) = hN (N + 2) • refZ := by
  rw [ZN, affinePullback_scalarMat_coordWedgeField, refZ]
  congr 1
  congr 1
  funext i
  by_cases hi : i = 2
  · subst hi
    rw [Pi.single_eq_same, Pi.single_eq_same]
    funext x
    have hdiff : DifferentiableAt ℝ (qN N)
        (affine (scalarMat 3 (hN (N + 2))) (corner N) x) :=
      (contDiff_affinePullback _ _ (contDiff_refQ (r := 1))).differentiable_one _
    rw [← extDeriv_affinePullback_apply _ _ hdiff]
    change extDeriv (affinePullback (scalarMat 3 (hN (N + 2))) (corner N) (scaled N refQ)) x = _
    rw [pullback_scaled]
  · rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, affinePullback_zero]

/-- **The lower bound on `T₀`**: `‖(I − Π²) S¹ v_N‖²_{L²(T₀)} = h_N c₀`. -/
theorem formL2Sq_simplex₀ (N : ℕ) :
    formL2Sq (simplex₀ N).closedInterior
      (coordWedgeField (fun a => (((vN N a : (polyElement 3 PolySeq.lagrangeP2).Piecewise
        (mesh 3 (N + 2)) 1) (simplex₀' N) : (polyElement 3 PolySeq.lagrangeP2).space _ 1) :
          FormField 3)) -
        ((((PolySeq.bggS1h (mesh 3 (N + 2)) (vN N) :
          (polyElement 3 PolySeq.lowestOrder).globalSpace (mesh 3 (N + 2)) 2) :
            (polyElement 3 PolySeq.lowestOrder).Piecewise (mesh 3 (N + 2)) 2) (simplex₀' N) :
              (polyElement 3 PolySeq.lowestOrder).space _ 2) : FormField 3)) =
      hN (N + 2) * refGap := by
  have hw : coordWedgeField (fun a => (((vN N a : (polyElement 3 PolySeq.lagrangeP2).Piecewise
      (mesh 3 (N + 2)) 1) (simplex₀' N) : (polyElement 3 PolySeq.lagrangeP2).space _ 1) :
        FormField 3)) ∈ polySpace 3 1 (1 + 1) := by
    rw [coordWedgeField_vN_simplex₀]; exact ZN_mem N
  have e := wsPiecewise_apply_eq PolySeq.lagrangeP2 (fun a => (vN N a :
    (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1)) (simplex₀' N) hw
  change formL2Sq _ (_ - ((PolySeq.lagrangeP2.wsPiecewise (mesh 3 (N + 2)) 1 (fun a => (vN N a :
    (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1)) (simplex₀' N) :
      (polyElement 3 PolySeq.lowestOrder).space _ (1 + 1)) : FormField 3)) = _
  rw [e]
  refine formL2Sq_sub_localInterp_of_pullback (hN_pos (N + 2)) (corner N) (simplex₀_eq N) hw ?_
  rw [coordWedgeField_vN_simplex₀]
  exact pullback_ZN N


open Classical in
/-- The pointwise bound on `d f_N`, localized at `c_N`. -/
theorem abs_extDeriv_fN_le {G : ℝ} (hG : ∀ y, ‖extDeriv refF y‖ ≤ G) (N : ℕ)
    (T : Affine.Simplex ℝ (Fin 3 → ℝ) 3) :
    ∀ x ∈ T.closedInterior, ∀ s, |extDeriv (fN N) x s| ≤
      (if centerN N ∈ Metric.cthickening (2 * hN (N + 2)) T.closedInterior then
        (hN (N + 2))⁻¹ * G else 0) := by
  intro x hx s
  split_ifs with hc
  · refine le_trans ?_ (norm_extDeriv_fN_le hG N x)
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (extDeriv (fN N) x) s
  · have hd : 2 * hN (N + 2) < dist x (centerN N) := by
      by_contra! hd
      exact hc (Metric.mem_cthickening_of_dist_le _ x _ _ hx (by rwa [dist_comm]))
    rw [extDeriv_fN_eq_zero hd]
    simp

/-- **The upper bound** `‖v_N‖²_{L²(Q)} ≤ C h_N`. -/
theorem exists_sum_formL2Sq_vN_le : ∃ C, 0 ≤ C ∧ ∀ N : ℕ,
    ∑ T : (mesh 3 (N + 2)).simplices, formL2Sq (T : Affine.Simplex ℝ (Fin 3 → ℝ) 3).closedInterior
      ((((vN N 2 : (polyElement 3 PolySeq.lagrangeP2).globalSpace (mesh 3 (N + 2)) 1) :
        (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1) T :
          (polyElement 3 PolySeq.lagrangeP2).space T 1) : FormField 3) ≤ C * hN (N + 2) := by
  classical
  obtain ⟨G, hG0, hG⟩ := exists_bound_extDeriv_refF
  obtain ⟨A, hA0, hA⟩ := exists_abs_globalInterp_le (n := 3) PolySeq.lagrangeP2 1
  set V₀ : ℝ := ∑ σ : Equiv.Perm (Fin 3), volume.real (kuhnSimplex σ).closedInterior
  have hV₀ : 0 ≤ V₀ := Finset.sum_nonneg fun _ _ => measureReal_nonneg
  set c8 : ℝ := ((Fintype.card (Finset (Fin 3)) : ℕ) : ℝ)
  refine ⟨c8 * V₀ * A ^ 2 * G ^ 2 * ((6 ^ 3 * Nat.factorial 3 : ℕ) : ℝ), by positivity,
    fun N => ?_⟩
  set h := hN (N + 2)
  have hh : 0 < h := hN_pos (N + 2)
  set P : Affine.Simplex ℝ (Fin 3 → ℝ) 3 → Prop := fun T =>
    centerN N ∈ Metric.cthickening (2 * h) T.closedInterior
  have hloc : ∀ T : (mesh 3 (N + 2)).simplices,
      formL2Sq (T : Affine.Simplex ℝ (Fin 3 → ℝ) 3).closedInterior
        ((((vN N 2 : (polyElement 3 PolySeq.lagrangeP2).globalSpace (mesh 3 (N + 2)) 1) :
          (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1) T :
            (polyElement 3 PolySeq.lagrangeP2).space T 1) : FormField 3) ≤
        (if P T then c8 * V₀ * A ^ 2 * G ^ 2 * h else 0) := by
    intro T
    obtain ⟨σ, t, hT⟩ := exists_mesh_simplex_eq T.2
    set β := if P T then h⁻¹ * G else 0
    have hβ0 : 0 ≤ β := by
      simp only [β]; split_ifs <;> positivity
    have hpt := hA (N + 2) T (extDerivC1 (fN1 N)) hβ0 (abs_extDeriv_fN_le hG N T)
    have hnorm : ∀ x ∈ (T : Affine.Simplex ℝ (Fin 3 → ℝ) 3).closedInterior,
        ‖((((vN N 2 : (polyElement 3 PolySeq.lagrangeP2).globalSpace (mesh 3 (N + 2)) 1) :
          (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1) T :
            (polyElement 3 PolySeq.lagrangeP2).space T 1) : FormField 3) x‖ ≤ A * β := by
      intro x hx
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun s => ?_
      rw [Real.norm_eq_abs, vN_two]
      exact hpt x hx s
    have hvol : volume.real (T : Affine.Simplex ℝ (Fin 3 → ℝ) 3).closedInterior ≤ h ^ 3 * V₀ := by
      rw [hT, measureReal_closedInterior_mapEquiv_boxMap _ _ hh]
      exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun σ : Equiv.Perm (Fin 3) =>
        volume.real (kuhnSimplex σ).closedInterior) (fun _ _ => measureReal_nonneg)
          (Finset.mem_univ σ)) (by positivity)
    refine (formL2Sq_le_of_norm_le (T : Affine.Simplex ℝ (Fin 3 → ℝ) 3).isCompact_closedInterior.measure_lt_top
      hnorm).trans ?_
    simp only [β]
    split_ifs with hP
    · calc c8 * volume.real (T : Affine.Simplex ℝ (Fin 3 → ℝ) 3).closedInterior *
            (A * (h⁻¹ * G)) ^ 2
          ≤ c8 * (h ^ 3 * V₀) * (A * (h⁻¹ * G)) ^ 2 := by gcongr
        _ = c8 * V₀ * A ^ 2 * G ^ 2 * h := by field_simp
    · simp
  calc _ ≤ ∑ T : (mesh 3 (N + 2)).simplices,
        (if P T then c8 * V₀ * A ^ 2 * G ^ 2 * h else 0) := Finset.sum_le_sum fun T _ => hloc T
    _ = ∑ T ∈ (mesh 3 (N + 2)).simplices, (if P T then c8 * V₀ * A ^ 2 * G ^ 2 * h else 0) :=
        Finset.sum_coe_sort _ (fun T => if P T then c8 * V₀ * A ^ 2 * G ^ 2 * h else 0)
    _ = ((mesh 3 (N + 2)).simplices.filter P).card * (c8 * V₀ * A ^ 2 * G ^ 2 * h) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((6 ^ 3 * Nat.factorial 3 : ℕ) : ℝ) * (c8 * V₀ * A ^ 2 * G ^ 2 * h) := by
        gcongr
        exact_mod_cast card_filter_mem_cthickening_le (N + 2) (centerN N)
    _ = _ := by ring


/-- `‖S(glue ψ) − glue u‖² = Σ_T ‖S ψ_T − u_T‖²_{L²(T)}` on the cube meshes. -/
theorem norm_sq_wsL2_sub_glue_eq {n N k : ℕ} (E E' : LocalElement n)
    (ψ : Fin n → E.Piecewise (mesh n N) k) (u : E'.Piecewise (mesh n N) (k + 1)) :
    ‖wsL2 (Ω := (mesh n N).domain) (k : ℤ) (E.tensorGlue (mesh n N) n (k : ℤ) ψ) -
        E'.glue (mesh n N) ((k : ℤ) + 1) u‖ ^ 2 =
      ∑ T : (mesh n N).simplices, formL2Sq (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior
        (coordWedgeField (fun a => ((ψ a T : E.space T k) : FormField n)) -
          ((u T : E'.space T (k + 1)) : FormField n)) := by
  rw [wsL2_tensorGlue]
  have hg : E'.glue (mesh n N) ((k : ℤ) + 1) u = pieceL2 (mesh n N) (mesh n N).domain
      (fun T => formComp (k := (k : ℤ) + 1) (E'.extendPW (mesh n N) u T))
      (fun T hT s => continuous_formComp (E'.contDiff_extendPW (mesh n N) u hT).continuous s) :=
    rfl
  rw [hg, pieceL2_sub, norm_sq_pieceL2_eq _ interior_subset_mesh_domain, ← Finset.sum_coe_sort]
  refine Finset.sum_congr rfl fun T _ => ?_
  have hdeg : ∀ x, IsDeg (k + 1) ((coordWedgeField (fun a => ((ψ a T : E.space T k) : FormField n)) -
      ((u T : E'.space T (k + 1)) : FormField n)) x) := fun x s hs => by
    simp only [Pi.sub_apply]
    rw [isDeg_coordWedgeField (fun a x => E.isDeg_of_mem (ψ a T).2 x) x s hs,
      E'.isDeg_of_mem (u T).2 x s hs, sub_zero]
  refine Eq.trans ?_ (sum_formIdx_integral_eq_formL2Sq hdeg)
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [formComp, E.extendPW_of_mem _ _ T.2, E'.extendPW_of_mem _ _ T.2,
    coordWedgeField_apply, Pi.sub_apply]


theorem phiN_mem₀ (N : ℕ) : (phiN N : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 0) ∈
    (polyElement 3 PolySeq.lagrangeP2).globalSpace₀ (mesh 3 (N + 2)) 0 :=
  LocalElement.globalInterp_mem_globalSpace₀ _ _ 0 fun x hx => fN_eq_zero_of_notMem (by
    have := (mesh 3 (N + 2)).notMem_domain_of_mem_frontier (isOpen_mesh_domain 3 (N + 2)) hx
    rwa [mesh_domain] at this)

theorem vN_mem₀ (N : ℕ) (a : Fin 3) :
    (vN N a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1) ∈
      (polyElement 3 PolySeq.lagrangeP2).globalSpace₀ (mesh 3 (N + 2)) 1 := by
  by_cases ha : a = 2
  · subst ha
    rw [vN, Pi.single_eq_same]
    exact (polyElement 3 PolySeq.lagrangeP2).dPiecewise_mem_globalSpace₀ _ (phiN_mem₀ N)
  · rw [vN_ne_two ha]
    exact Submodule.zero_mem _

/-- `curl v_N = 0`: `v_N` is a row-wise gradient. -/
theorem dPiecewise_vN (N : ℕ) :
    (fun a => (polyElement 3 PolySeq.lagrangeP2).dPiecewise (mesh 3 (N + 2)) 1
      (vN N a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1)) = 0 := by
  funext a
  by_cases ha : a = 2
  · subst ha
    funext T
    refine Subtype.ext ?_
    rw [vN, Pi.single_eq_same]
    change extDeriv (extDeriv (((phiN N : (polyElement 3 PolySeq.lagrangeP2).Piecewise
      (mesh 3 (N + 2)) 0) T : (polyElement 3 PolySeq.lagrangeP2).space _ 0) : FormField 3)) = 0
    exact extDeriv_extDeriv ((PolyKind.contDiff_of_mem_space
      (((phiN N : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 0) T).2)).of_le
        le_top)
  · rw [vN_ne_two ha]
    simp

theorem norm_sq_tensorGlue_vN (N : ℕ) :
    ‖(polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 (N + 2)) 3 ((1 : ℕ) : ℤ)
        (fun a => (vN N a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1))‖ ^ 2 =
      ∑ T : (mesh 3 (N + 2)).simplices, formL2Sq (T : Affine.Simplex ℝ (Fin 3 → ℝ) 3).closedInterior
        ((((vN N 2 : (polyElement 3 PolySeq.lagrangeP2).globalSpace (mesh 3 (N + 2)) 1) :
          (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1) T :
            (polyElement 3 PolySeq.lagrangeP2).space T 1) : FormField 3) := by
  rw [norm_sq_tensorGlue, Fin.sum_univ_three, vN_ne_two (by decide : (0 : Fin 3) ≠ 2),
    vN_ne_two (by decide : (1 : Fin 3) ≠ 2)]
  simp only [ZeroMemClass.coe_zero, map_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_add]
  exact norm_sq_glue_eq _ _

theorem le_norm_sq_wsL2_sub_glue_vN (N : ℕ) :
    hN (N + 2) * refGap ≤
      ‖wsL2 (Ω := (mesh 3 (N + 2)).domain) ((1 : ℕ) : ℤ)
          ((polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 (N + 2)) 3 ((1 : ℕ) : ℤ)
            fun a => (vN N a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1)) -
        (polyElement 3 PolySeq.lowestOrder).glue (mesh 3 (N + 2)) (((1 : ℕ) : ℤ) + 1)
          ((PolySeq.bggS1h (mesh 3 (N + 2)) (vN N) :
            (polyElement 3 PolySeq.lowestOrder).globalSpace (mesh 3 (N + 2)) 2) :
              (polyElement 3 PolySeq.lowestOrder).Piecewise (mesh 3 (N + 2)) 2)‖ ^ 2 := by
  refine le_of_le_of_eq ?_ (norm_sq_wsL2_sub_glue_eq (n := 3) (N := N + 2) (k := 1)
    (polyElement 3 PolySeq.lagrangeP2) (polyElement 3 PolySeq.lowestOrder)
    (fun a => (vN N a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1))
    ((PolySeq.bggS1h (mesh 3 (N + 2)) (vN N) :
      (polyElement 3 PolySeq.lowestOrder).globalSpace (mesh 3 (N + 2)) 2) :
        (polyElement 3 PolySeq.lowestOrder).Piecewise (mesh 3 (N + 2)) 2)).symm
  have h1 := Finset.single_le_sum (f := fun T : (mesh 3 (N + 2)).simplices =>
    formL2Sq (T : Affine.Simplex ℝ (Fin 3 → ℝ) 3).closedInterior
      (coordWedgeField (fun a => (((vN N a : (polyElement 3 PolySeq.lagrangeP2).Piecewise
        (mesh 3 (N + 2)) 1) T : (polyElement 3 PolySeq.lagrangeP2).space _ 1) : FormField 3)) -
        ((((PolySeq.bggS1h (mesh 3 (N + 2)) (vN N) :
          (polyElement 3 PolySeq.lowestOrder).globalSpace (mesh 3 (N + 2)) 2) :
            (polyElement 3 PolySeq.lowestOrder).Piecewise (mesh 3 (N + 2)) 2) T :
              (polyElement 3 PolySeq.lowestOrder).space _ 2) : FormField 3)))
    (fun T _ => formL2Sq_nonneg
      (T : Affine.Simplex ℝ (Fin 3 → ℝ) 3).isCompact_closedInterior.measurableSet _)
    (Finset.mem_univ (simplex₀' N))
  exact (formL2Sq_simplex₀ N).symm.le.trans h1


/-- **[QuennevilleBelair2015], Prop 5.9(2) is false.** There is `c > 0` such that on every mesh
`(mesh 3 (N + 2))` there is `v ∈ P₂⁻Λ̊¹ ⊗ ℝ³` (vanishing boundary DOFs), `v ≠ 0`, with
`‖(I − Π²) S¹ v‖_{L²(Q)} ≥ c ‖v‖_{H(curl)}`, where `S¹ v` is the `L²` field `wsL2 1`,
`Π² S¹ v = S₁,ₕ v` and `‖v‖²_{H(curl)} = ‖v‖² + ‖curl v‖²` (row-wise). The field is
`v_N = (0, 0, grad Π̃⁰ f_N)` (`vN`); `curl v_N = 0` (`dPiecewise_vN`). -/
theorem exists_interpolationError_ge : ∃ c, 0 < c ∧ ∀ N : ℕ,
    ∃ v : Fin 3 → (polyElement 3 PolySeq.lagrangeP2).globalSpace (mesh 3 (N + 2)) 1,
      (∀ a, (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1) ∈
        (polyElement 3 PolySeq.lagrangeP2).globalSpace₀ (mesh 3 (N + 2)) 1) ∧
      0 < ‖(polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 (N + 2)) 3 ((1 : ℕ) : ℤ)
        (fun a => (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1))‖ ∧
      c * √(‖(polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 (N + 2)) 3 ((1 : ℕ) : ℤ)
          (fun a => (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1))‖ ^ 2 +
        ‖(polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 (N + 2)) 3 ((1 + 1 : ℕ) : ℤ)
          (fun a => (polyElement 3 PolySeq.lagrangeP2).dPiecewise (mesh 3 (N + 2)) 1
            (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1))‖ ^ 2) ≤
      ‖wsL2 (Ω := (mesh 3 (N + 2)).domain) ((1 : ℕ) : ℤ)
          ((polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 (N + 2)) 3 ((1 : ℕ) : ℤ)
            fun a => (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1)) -
        (polyElement 3 PolySeq.lowestOrder).glue (mesh 3 (N + 2)) (((1 : ℕ) : ℤ) + 1)
          ((PolySeq.bggS1h (mesh 3 (N + 2)) v :
            (polyElement 3 PolySeq.lowestOrder).globalSpace (mesh 3 (N + 2)) 2) :
              (polyElement 3 PolySeq.lowestOrder).Piecewise (mesh 3 (N + 2)) 2)‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_sum_formL2Sq_vN_le
  have hC1 : 0 < C + 1 := by linarith
  have hg := refGap_pos
  refine ⟨√(refGap / (C + 1)), Real.sqrt_pos.2 (div_pos hg hC1), fun N => ⟨vN N, vN_mem₀ N, ?_⟩⟩
  have hh := hN_pos (N + 2)
  have hL := le_norm_sq_wsL2_sub_glue_vN N
  set L := ‖wsL2 (Ω := (mesh 3 (N + 2)).domain) ((1 : ℕ) : ℤ)
          ((polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 (N + 2)) 3 ((1 : ℕ) : ℤ)
            fun a => (vN N a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1)) -
        (polyElement 3 PolySeq.lowestOrder).glue (mesh 3 (N + 2)) (((1 : ℕ) : ℤ) + 1)
          ((PolySeq.bggS1h (mesh 3 (N + 2)) (vN N) :
            (polyElement 3 PolySeq.lowestOrder).globalSpace (mesh 3 (N + 2)) 2) :
              (polyElement 3 PolySeq.lowestOrder).Piecewise (mesh 3 (N + 2)) 2)‖ with hLdef
  set X := ‖(polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 (N + 2)) 3 ((1 : ℕ) : ℤ)
    (fun a => (vN N a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1))‖
    with hXdef
  have hX : X ^ 2 ≤ (C + 1) * hN (N + 2) := by
    rw [hXdef, norm_sq_tensorGlue_vN]
    exact (hC N).trans (by nlinarith)
  have hd : (polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 (N + 2)) 3 ((1 + 1 : ℕ) : ℤ)
      (fun a => (polyElement 3 PolySeq.lagrangeP2).dPiecewise (mesh 3 (N + 2)) 1
        (vN N a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1)) = 0 := by
    rw [dPiecewise_vN N]; exact map_zero _
  refine ⟨?_, ?_⟩
  · refine lt_of_le_of_ne (norm_nonneg _) fun h0 => ?_
    have h0' := (norm_eq_zero.1 h0.symm)
    have hv : ∀ a, (vN N a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1) = 0 :=
      fun a => (polyElement 3 PolySeq.lagrangeP2).glue_injective _ (isOpen_mesh_domain 3 (N + 2)) 1
        ((congrArg (fun w => w a) h0').trans (map_zero _).symm)
    have hv' : vN N = 0 := funext fun a => Subtype.ext (hv a)
    have : L = 0 := by
      rw [hLdef, h0', hv', map_zero]
      simp
    rw [this] at hL
    nlinarith
  · rw [hd, norm_zero]
    have e : X ^ 2 + 0 ^ 2 = X ^ 2 := by ring
    rw [e, Real.sqrt_sq (norm_nonneg _)]
    have hX0 : 0 ≤ X := norm_nonneg _
    have hL0 : 0 ≤ L := norm_nonneg _
    calc √(refGap / (C + 1)) * X = √(refGap / (C + 1) * X ^ 2) := by
          rw [Real.sqrt_mul (div_pos hg hC1).le, Real.sqrt_sq hX0]
      _ ≤ √(L ^ 2) := by
          refine Real.sqrt_le_sqrt ?_
          calc refGap / (C + 1) * X ^ 2 ≤ refGap / (C + 1) * ((C + 1) * hN (N + 2)) :=
                mul_le_mul_of_nonneg_left hX (div_pos hg hC1).le
            _ = hN (N + 2) * refGap := by field_simp
            _ ≤ _ := hL
      _ = L := Real.sqrt_sq hL0

/-- **No `O(h)` bound for `(I − Π²) S¹` on `P₂⁻Λ̊¹ ⊗ ℝ³`**, `Π²` the canonical interpolant: the
estimate `‖(I − Π²) S¹ v‖ ≤ C h ‖v‖_{H(curl)}` of [QuennevilleBelair2015], Prop 5.9(2) fails for
every `C`. For an arbitrary projection onto the Raviart–Thomas space (the hypothesis `happ1` of
`Feec.BGG.Discrete.error_estimate`) see `not_exists_bestApprox_bound`. -/
theorem not_exists_interpolationError_bound : ¬ ∃ C : ℝ, ∀ (N : ℕ)
    (v : Fin 3 → (polyElement 3 PolySeq.lagrangeP2).globalSpace (mesh 3 N) 1),
    (∀ a, (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 N) 1) ∈
      (polyElement 3 PolySeq.lagrangeP2).globalSpace₀ (mesh 3 N) 1) →
    ‖wsL2 (Ω := (mesh 3 N).domain) ((1 : ℕ) : ℤ)
          ((polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 N) 3 ((1 : ℕ) : ℤ)
            fun a => (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 N) 1)) -
        (polyElement 3 PolySeq.lowestOrder).glue (mesh 3 N) (((1 : ℕ) : ℤ) + 1)
          ((PolySeq.bggS1h (mesh 3 N) v :
            (polyElement 3 PolySeq.lowestOrder).globalSpace (mesh 3 N) 2) :
              (polyElement 3 PolySeq.lowestOrder).Piecewise (mesh 3 N) 2)‖ ≤
      C * hN N * √(‖(polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 N) 3 ((1 : ℕ) : ℤ)
          (fun a => (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 N) 1))‖ ^ 2 +
        ‖(polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 N) 3 ((1 + 1 : ℕ) : ℤ)
          (fun a => (polyElement 3 PolySeq.lagrangeP2).dPiecewise (mesh 3 N) 1
            (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 N) 1))‖ ^ 2) := by
  rintro ⟨C, hC⟩
  obtain ⟨c, hc, hex⟩ := exists_interpolationError_ge
  obtain ⟨N, hN'⟩ := exists_nat_gt (C / c)
  obtain ⟨v, hv0, hpos, hlow⟩ := hex N
  have hup := hC (N + 2) v hv0
  set Y := √(‖(polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 (N + 2)) 3 ((1 : ℕ) : ℤ)
          (fun a => (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1))‖ ^ 2 +
        ‖(polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 (N + 2)) 3 ((1 + 1 : ℕ) : ℤ)
          (fun a => (polyElement 3 PolySeq.lagrangeP2).dPiecewise (mesh 3 (N + 2)) 1
            (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1))‖ ^ 2)
  have hY : 0 < Y := Real.sqrt_pos.2 (by positivity)
  have h1 : c * Y ≤ C * hN (N + 2) * Y := hlow.trans hup
  have h2 : c ≤ C * hN (N + 2) := le_of_mul_le_mul_right (by linarith) hY
  have hh : hN (N + 2) = 1 / 2 / ((N + 3 : ℕ) : ℝ) := rfl
  rw [hh] at h2
  have hN3 : (0 : ℝ) < ((N + 3 : ℕ) : ℝ) := by positivity
  rw [div_lt_iff₀ hc] at hN'
  have : C * (1 / 2 / ((N + 3 : ℕ) : ℝ)) * ((N + 3 : ℕ) : ℝ) = C / 2 := by field_simp
  have h3 : c * ((N + 3 : ℕ) : ℝ) ≤ C / 2 := by
    rw [← this]; exact mul_le_mul_of_nonneg_right h2 hN3.le
  push_cast at h3
  nlinarith

/-! #### Projection independence: no `O(h)` approximation of `S¹ v_N` by `P₁⁻Λ²` fields -/

/-- `v_N` is also a piecewise linear field: `v_N ∈ P₁Λ¹ ⊗ ℝ³` (piecewise `grad` of `P₂`), the space
over which [QuennevilleBelair2015], Prop 5.9(2) literally quantifies. -/
theorem vN_mem_polySpace (N : ℕ) (a : Fin 3) (T : (mesh 3 (N + 2)).simplices) :
    (((vN N a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1) T :
      (polyElement 3 PolySeq.lagrangeP2).space _ 1) : FormField 3) ∈ polySpace 3 1 1 := by
  by_cases ha : a = 2
  · subst ha
    rw [vN, Pi.single_eq_same]
    have h0 : ((((phiN N : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 0) T :
        (polyElement 3 PolySeq.lagrangeP2).space _ 0) : FormField 3)) ∈ polySpace 3 2 0 :=
      ((phiN N : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 0) T).2
    change extDeriv (((phiN N : (polyElement 3 PolySeq.lagrangeP2).Piecewise
      (mesh 3 (N + 2)) 0) T : (polyElement 3 PolySeq.lagrangeP2).space _ 0) : FormField 3) ∈ _
    simpa using extDeriv_mem_polySpace h0
  · rw [vN_ne_two ha]
    exact Submodule.zero_mem _

/-- `‖S¹(glue v_N) − glue w‖² ≥ h δ₀²` for **every** piecewise `P₁⁻Λ²` field `w` (in particular
every element of the global Raviart–Thomas space, whatever projection produced it). -/
theorem le_norm_sq_wsL2_vN_sub_glue (N : ℕ)
    (w : (polyElement 3 PolySeq.lowestOrder).Piecewise (mesh 3 (N + 2)) 2) :
    hN (N + 2) * refDist ^ 2 ≤
      ‖wsL2 (Ω := (mesh 3 (N + 2)).domain) ((1 : ℕ) : ℤ)
          ((polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 (N + 2)) 3 ((1 : ℕ) : ℤ)
            fun a => (vN N a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1)) -
        (polyElement 3 PolySeq.lowestOrder).glue (mesh 3 (N + 2)) (((1 : ℕ) : ℤ) + 1) w‖ ^ 2 := by
  refine le_of_le_of_eq ?_ (norm_sq_wsL2_sub_glue_eq (n := 3) (N := N + 2) (k := 1)
    (polyElement 3 PolySeq.lagrangeP2) (polyElement 3 PolySeq.lowestOrder)
    (fun a => (vN N a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1)) w).symm
  have h1 := Finset.single_le_sum (f := fun T : (mesh 3 (N + 2)).simplices =>
    formL2Sq (T : Affine.Simplex ℝ (Fin 3 → ℝ) 3).closedInterior
      (coordWedgeField (fun a => (((vN N a : (polyElement 3 PolySeq.lagrangeP2).Piecewise
        (mesh 3 (N + 2)) 1) T : (polyElement 3 PolySeq.lagrangeP2).space _ 1) : FormField 3)) -
        ((w T : (polyElement 3 PolySeq.lowestOrder).space _ 2) : FormField 3)))
    (fun T _ => formL2Sq_nonneg
      (T : Affine.Simplex ℝ (Fin 3 → ℝ) 3).isCompact_closedInterior.measurableSet _)
    (Finset.mem_univ (simplex₀' N))
  refine le_trans ?_ h1
  change hN (N + 2) * refDist ^ 2 ≤ formL2Sq (simplex₀ N).closedInterior
    (coordWedgeField (fun a => (((vN N a : (polyElement 3 PolySeq.lagrangeP2).Piecewise
      (mesh 3 (N + 2)) 1) (simplex₀' N) : (polyElement 3 PolySeq.lagrangeP2).space _ 1) :
        FormField 3)) - ((w (simplex₀' N) : (polyElement 3 PolySeq.lowestOrder).space _ 2) :
          FormField 3))
  rw [coordWedgeField_vN_simplex₀, simplex₀_eq]
  exact mul_refDist_sq_le_formL2Sq (hN_pos (N + 2)) (corner N) (ZN_mem N) (pullback_ZN N)
    (by exact (w (simplex₀' N)).2)

/-- **[QuennevilleBelair2015], Prop 5.9(2) is false, independently of the projection.** There is
`c > 0` such that on every mesh `mesh 3 (N + 2)` there is `v ∈ P₂⁻Λ̊¹ ⊗ ℝ³` (vanishing boundary
DOFs), which is also in `P₁Λ¹ ⊗ ℝ³` (piecewise linear), `v ≠ 0`, with
`‖S¹ v − w‖_{L²(Q)} ≥ c ‖v‖_{H(curl)}` for **every** piecewise `P₁⁻Λ²` field `w`. Hence
`inf_{w_h ∈ P₁⁻Λ²_h} ‖S¹ v − w_h‖` is not `O(h) ‖v‖_{H(curl)}`: no map `P²` with values in the
Raviart–Thomas space (canonical, smoothed, or `L²` projection) satisfies the bound
`‖(I − P²) S¹ v‖ ≤ C h ‖v‖_{H(curl)}` on `P₂⁻Λ̊¹ ⊗ ℝ³`. The field is `v_N` (`vN`). -/
theorem exists_bestApproxError_ge : ∃ c, 0 < c ∧ ∀ N : ℕ,
    ∃ v : Fin 3 → (polyElement 3 PolySeq.lagrangeP2).globalSpace (mesh 3 (N + 2)) 1,
      (∀ a, (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1) ∈
        (polyElement 3 PolySeq.lagrangeP2).globalSpace₀ (mesh 3 (N + 2)) 1) ∧
      (∀ a T, (((v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1) T :
        (polyElement 3 PolySeq.lagrangeP2).space _ 1) : FormField 3) ∈ polySpace 3 1 1) ∧
      0 < ‖(polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 (N + 2)) 3 ((1 : ℕ) : ℤ)
        (fun a => (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1))‖ ∧
      ∀ w : (polyElement 3 PolySeq.lowestOrder).Piecewise (mesh 3 (N + 2)) 2,
        c * √(‖(polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 (N + 2)) 3 ((1 : ℕ) : ℤ)
            (fun a => (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1))‖ ^ 2 +
          ‖(polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 (N + 2)) 3 ((1 + 1 : ℕ) : ℤ)
            (fun a => (polyElement 3 PolySeq.lagrangeP2).dPiecewise (mesh 3 (N + 2)) 1
              (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1))‖ ^ 2) ≤
        ‖wsL2 (Ω := (mesh 3 (N + 2)).domain) ((1 : ℕ) : ℤ)
            ((polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 (N + 2)) 3 ((1 : ℕ) : ℤ)
              fun a => (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1)) -
          (polyElement 3 PolySeq.lowestOrder).glue (mesh 3 (N + 2)) (((1 : ℕ) : ℤ) + 1) w‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_sum_formL2Sq_vN_le
  have hC1 : 0 < C + 1 := by linarith
  have hg : 0 < refDist ^ 2 := pow_pos refDist_pos 2
  refine ⟨√(refDist ^ 2 / (C + 1)), Real.sqrt_pos.2 (div_pos hg hC1), fun N =>
    ⟨vN N, vN_mem₀ N, vN_mem_polySpace N, ?_, fun w => ?_⟩⟩
  · have hh := hN_pos (N + 2)
    have hL := le_norm_sq_wsL2_vN_sub_glue N 0
    rw [map_zero, sub_zero] at hL
    refine lt_of_le_of_ne (norm_nonneg _) fun h0 => ?_
    rw [(norm_eq_zero.1 h0.symm), map_zero, norm_zero] at hL
    nlinarith
  · have hL := le_norm_sq_wsL2_vN_sub_glue N w
    set L := ‖wsL2 (Ω := (mesh 3 (N + 2)).domain) ((1 : ℕ) : ℤ)
            ((polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 (N + 2)) 3 ((1 : ℕ) : ℤ)
              fun a => (vN N a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1)) -
          (polyElement 3 PolySeq.lowestOrder).glue (mesh 3 (N + 2)) (((1 : ℕ) : ℤ) + 1) w‖
      with hLdef
    set X := ‖(polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 (N + 2)) 3 ((1 : ℕ) : ℤ)
      (fun a => (vN N a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1))‖
      with hXdef
    have hX : X ^ 2 ≤ (C + 1) * hN (N + 2) := by
      rw [hXdef, norm_sq_tensorGlue_vN]
      exact (hC N).trans (by nlinarith [hN_pos (N + 2)])
    have hd : (polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 (N + 2)) 3 ((1 + 1 : ℕ) : ℤ)
        (fun a => (polyElement 3 PolySeq.lagrangeP2).dPiecewise (mesh 3 (N + 2)) 1
          (vN N a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1)) = 0 := by
      rw [dPiecewise_vN N]; exact map_zero _
    rw [hd, norm_zero]
    have e : X ^ 2 + 0 ^ 2 = X ^ 2 := by ring
    rw [e, Real.sqrt_sq (norm_nonneg _)]
    have hX0 : 0 ≤ X := norm_nonneg _
    have hL0 : 0 ≤ L := norm_nonneg _
    calc √(refDist ^ 2 / (C + 1)) * X = √(refDist ^ 2 / (C + 1) * X ^ 2) := by
          rw [Real.sqrt_mul (div_pos hg hC1).le, Real.sqrt_sq hX0]
      _ ≤ √(L ^ 2) := by
          refine Real.sqrt_le_sqrt ?_
          calc refDist ^ 2 / (C + 1) * X ^ 2 ≤ refDist ^ 2 / (C + 1) * ((C + 1) * hN (N + 2)) :=
                mul_le_mul_of_nonneg_left hX (div_pos hg hC1).le
            _ = hN (N + 2) * refDist ^ 2 := by field_simp
            _ ≤ _ := hL
      _ = L := Real.sqrt_sq hL0

/-- **No `O(h)` best approximation of `S¹` on `P₂⁻Λ̊¹ ⊗ ℝ³` by `P₁⁻Λ²`**: there is no `C` with
`inf_{w} ‖S¹ v − w‖ ≤ C h ‖v‖_{H(curl)}` (`w` over piecewise `P₁⁻Λ²` fields) for all meshes and all
`v ∈ P₂⁻Λ̊¹ ⊗ ℝ³`. Consequently the hypothesis
`happ1 : ‖S¹ v − P² S¹ v‖ ≤ C_app h ‖v‖_{H(curl)}` of `Feec.BGG.Discrete.error_estimate` cannot hold,
with `N`-independent `C_app`, for any choice of `P²` with values in the Raviart–Thomas spaces of
Table 5.1 ([QuennevilleBelair2015], Prop 5.9(2)). -/
theorem not_exists_bestApprox_bound : ¬ ∃ C : ℝ, ∀ (N : ℕ)
    (v : Fin 3 → (polyElement 3 PolySeq.lagrangeP2).globalSpace (mesh 3 N) 1),
    (∀ a, (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 N) 1) ∈
      (polyElement 3 PolySeq.lagrangeP2).globalSpace₀ (mesh 3 N) 1) →
    ∃ w : (polyElement 3 PolySeq.lowestOrder).Piecewise (mesh 3 N) 2,
    ‖wsL2 (Ω := (mesh 3 N).domain) ((1 : ℕ) : ℤ)
          ((polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 N) 3 ((1 : ℕ) : ℤ)
            fun a => (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 N) 1)) -
        (polyElement 3 PolySeq.lowestOrder).glue (mesh 3 N) (((1 : ℕ) : ℤ) + 1) w‖ ≤
      C * hN N * √(‖(polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 N) 3 ((1 : ℕ) : ℤ)
          (fun a => (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 N) 1))‖ ^ 2 +
        ‖(polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 N) 3 ((1 + 1 : ℕ) : ℤ)
          (fun a => (polyElement 3 PolySeq.lagrangeP2).dPiecewise (mesh 3 N) 1
            (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 N) 1))‖ ^ 2) := by
  rintro ⟨C, hC⟩
  obtain ⟨c, hc, hex⟩ := exists_bestApproxError_ge
  obtain ⟨N, hN'⟩ := exists_nat_gt (C / c)
  obtain ⟨v, hv0, -, hpos, hlow⟩ := hex N
  obtain ⟨w, hup⟩ := hC (N + 2) v hv0
  set Y := √(‖(polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 (N + 2)) 3 ((1 : ℕ) : ℤ)
          (fun a => (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1))‖ ^ 2 +
        ‖(polyElement 3 PolySeq.lagrangeP2).tensorGlue (mesh 3 (N + 2)) 3 ((1 + 1 : ℕ) : ℤ)
          (fun a => (polyElement 3 PolySeq.lagrangeP2).dPiecewise (mesh 3 (N + 2)) 1
            (v a : (polyElement 3 PolySeq.lagrangeP2).Piecewise (mesh 3 (N + 2)) 1))‖ ^ 2)
  have hY : 0 < Y := Real.sqrt_pos.2 (by positivity)
  have h1 : c * Y ≤ C * hN (N + 2) * Y := (hlow w).trans hup
  have h2 : c ≤ C * hN (N + 2) := le_of_mul_le_mul_right (by linarith) hY
  have hh : hN (N + 2) = 1 / 2 / ((N + 3 : ℕ) : ℝ) := rfl
  rw [hh] at h2
  have hN3 : (0 : ℝ) < ((N + 3 : ℕ) : ℝ) := by positivity
  rw [div_lt_iff₀ hc] at hN'
  have : C * (1 / 2 / ((N + 3 : ℕ) : ℝ)) * ((N + 3 : ℕ) : ℝ) = C / 2 := by field_simp
  have h3 : c * ((N + 3 : ℕ) : ℝ) ≤ C / 2 := by
    rw [← this]; exact mul_le_mul_of_nonneg_right h2 hN3.le
  push_cast at h3
  nlinarith

end Prop59Two

end Feec.Models.Cube.WeakSymmetry
