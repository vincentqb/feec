module

public import Feec.FiniteElement.CubeMesh
public import Feec.FiniteElement.Conformity
public import Feec.FiniteElement.LocalSpace
public import Feec.Mesh.Freudenthal

/-!
# `HΛ`-conformity of the cubical spaces `Q_r⁻Λᵏ(𝒯_h)`

On the uniform cubical mesh of `(0, 1)ⁿ` with `N` cells per direction
(`Feec.FiniteElement.CubeMesh`), a piecewise polynomial form `(ω_m)_m` (in local coordinates)
is the field `cellField ω m = F_m^{-*} ω_m` on the cell `m`, `F_m(y) = (m + y) / N`. We show that
tangential continuity (`cubeCompatible`: equal traces on common faces) gives
`HΛᵏ((0, 1)ⁿ)`-conformity, with the weak exterior derivative the piecewise one
([AFW2006], §5; [ArnoldBoffiBonizzoni2015], §3).

The proof reuses the simplicial conformity theorem `extDeriv_pieceL2_mem_maximal_domain` on the
Freudenthal refinement of the cubical mesh (`cubeRefinement`, whose simplices `(m + K_σ) / N`
lie in the cells `m`): two simplices sharing a facet `F` lie in cells `m`, `m'` whose closures
contain `F`; in the directions fixed by the common face, the tangent vectors of `F` vanish and
the local coordinates are the fixed values, so the tangential traces of the two cell fields are
those of the (equal) polynomial traces of `ω_m` and `ω_{m'}` (`tangentialTraceEq_cellField`).

## Main definitions

* `Feec.FiniteElement.cellField ω m`: the field of the cell `m` in global coordinates;
* `Feec.FiniteElement.cubeRefinement n N`, `simplexCell`, `closedCell`: the Freudenthal
  refinement and the cell of each of its simplices.

## Main results

* `extDeriv_cellField`: `d` of a cell field is the cell field of `d`;
* `tangentialTraceEq_cellField`: tangential continuity across common faces;
* `cellField_mem_maximal_domain`: **`HΛᵏ`-conformity of tangentially continuous piecewise
  polynomial forms**, `d_max` being the piecewise `d`, and
  `cellField_mem_maximal_domain_of_mem`: the global spaces `Q_b⁻Λᵏ(𝒯_h) ⊆ HΛᵏ((0, 1)ⁿ)`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §5 (piecewise smooth forms with single-valued traces lie in `HΛᵏ`)
* [D. N. Arnold, D. Boffi, F. Bonizzoni, *Finite element differential forms on curvilinear cubic meshes and their approximation properties*][ArnoldBoffiBonizzoni2015],
  §3
* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MvPolynomial

@[expose] public noncomputable section

namespace Feec.FiniteElement

open Feec.Domain Feec.Mesh Koszul ExteriorFibre

variable {n N : ℕ}

/-! ### The cell fields in global coordinates -/

/-- The scaling matrix `N I` of the local coordinates `y = N x - m` of the cells. -/
def cellMatrix (n N : ℕ) : Fin n → Fin n → ℝ := fun i l => if i = l then (N : ℝ) else 0

/-- The offset `-m` of the local coordinates of the cell `m`. -/
def cellOffset (m : CubeCell fun _ : Fin n => N) : Fin n → ℝ := fun i => -((m i : ℕ) : ℝ)

theorem affine_cellMatrix (m : CubeCell fun _ : Fin n => N) (x : Fin n → ℝ) (i : Fin n) :
    affine (cellMatrix n N) (cellOffset m) x i = N * x i - m i := by
  simp [affine_apply, cellMatrix, cellOffset, sub_eq_add_neg]

/-- The field of the cell `m` in the global coordinates: `ω_m` pulled back by `x ↦ N x - m`. -/
def cellField (ω : CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n))
    (m : CubeCell fun _ : Fin n => N) : FormField n :=
  affinePullback (cellMatrix n N) (cellOffset m) (evalForm n (ω m))

theorem contDiff_cellField (ω : CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n))
    (m : CubeCell fun _ : Fin n => N) {r : WithTop ℕ∞} : ContDiff ℝ r (cellField ω m) := by
  rw [cellField, ← evalForm_polyPullback]
  exact contDiff_evalForm _

/-- `d` of a cell field is the cell field of `d`. -/
theorem extDeriv_cellField (ω : CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n))
    (m : CubeCell fun _ : Fin n => N) :
    extDeriv (cellField ω m) = cellField (fun m => Koszul.extDeriv (ω m)) m := by
  funext x
  rw [cellField, extDeriv_affinePullback_apply _ _
    ((contDiff_evalForm (ω m) (r := 1)).differentiable one_ne_zero _), extDeriv_evalForm]
  rfl

theorem isDeg_cellField {k : ℕ} {ω : CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n)}
    {m : CubeCell fun _ : Fin n => N} (hk : IsDeg k (ω m)) (x : Fin n → ℝ) :
    IsDeg k (cellField ω m x) :=
  IsDeg.affinePullback (fun y s hs => by simp [evalForm_apply, hk s hs]) _ _ x

/-! ### The Freudenthal refinement -/

variable [NeZero N]

variable (n N) in
/-- The Freudenthal refinement of the cubical mesh of `(0, 1)ⁿ` with `N` cells per direction:
each cell `m` is split into the `n!` simplices `(m + K_σ) / N`. -/
abbrev cubeRefinement : SimplicialMesh n := freudenthalMesh 0 1 one_pos N

/-- The cell of a simplex of the refinement, read off its first vertex `m / N`. -/
def simplexCell (T : Affine.Simplex ℝ (Fin n → ℝ) n) : CubeCell fun _ : Fin n => N := fun j =>
  (⟨min ⌊(N : ℝ) * T.points 0 j⌋₊ (N - 1), by have := NeZero.pos N; omega⟩ : Fin N)

/-- The closed cell `∏ⱼ [m_j, m_j + 1] / N`. -/
def closedCell (m : CubeCell fun _ : Fin n => N) : Set (Fin n → ℝ) :=
  {x | ∀ j, ((m j : ℕ) : ℝ) ≤ N * x j ∧ (N : ℝ) * x j ≤ (m j : ℕ) + 1}

theorem simplexCell_freudenthal (m : Fin n → Fin N) (σ : Equiv.Perm (Fin n)) :
    simplexCell (mapEquiv (boxMap 0 (1 / N) (freudenthalScale_ne_zero one_pos N))
      (freudenthalSimplex (finLattice m) σ)) = m := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  funext j
  refine Fin.ext ?_
  change min ⌊(N : ℝ) * _⌋₊ (N - 1) = _
  rw [mapEquiv_points, freudenthalSimplex_points, kuhnVertex_zero, add_zero, boxMap_apply,
    zero_add, Pi.smul_apply, latticePoint_apply, smul_eq_mul]
  simp only [finLattice, Int.cast_natCast]
  rw [show (N : ℝ) * (1 / N * (m j : ℕ)) = (m j : ℕ) by field_simp, Nat.floor_natCast]
  have := (m j).isLt
  omega

theorem simplexCell_closedInterior_subset {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (cubeRefinement n N).simplices) :
    T.closedInterior ⊆ closedCell (simplexCell (N := N) T) := by
  obtain ⟨m, σ, rfl⟩ := mem_freudenthalMesh_simplices.1 hT
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  rw [simplexCell_freudenthal, closedInterior_freudenthalMesh_simplex]
  rintro _ ⟨x, hx, rfl⟩ j
  have := hx.1 j
  simp only [Pi.sub_apply, latticePoint_apply, finLattice, Int.cast_natCast] at this
  simp only [zero_add, Pi.smul_apply, smul_eq_mul]
  rw [show (N : ℝ) * (1 / N * x j) = x j by field_simp]
  constructor <;> linarith [this.1, this.2]

omit [NeZero N] in
/-- A point of two closed cells: the cells meet. -/
theorem adj_of_mem_closedCell {m m' : CubeCell fun _ : Fin n => N} {x : Fin n → ℝ}
    (hx : x ∈ closedCell m) (hx' : x ∈ closedCell m') : CubeCell.Adj _ m m' := fun j => by
  have h1 := hx j
  have h2 := hx' j
  have e1 : ((m j : ℕ) : ℝ) ≤ (m' j : ℕ) + 1 := by linarith [h1.1, h2.2]
  have e2 : ((m' j : ℕ) : ℝ) ≤ (m j : ℕ) + 1 := by linarith [h1.2, h2.1]
  exact ⟨by exact_mod_cast e1, by exact_mod_cast e2⟩

omit [NeZero N] in
/-- The local coordinates of a point of two closed cells are the values fixed by their common
face. -/
theorem localCoord_eq_of_commonFace {m m' : CubeCell fun _ : Fin n => N} {x : Fin n → ℝ}
    (hx : x ∈ closedCell m) (hx' : x ∈ closedCell m') {j : Fin n} {c : ℝ}
    (hc : commonFace _ m m' j = some c) : N * x j - m j = c := by
  have h1 := hx j
  have h2 := hx' j
  rcases commonFace_cases (adj_of_mem_closedCell hx hx') j with ⟨h, -, h3⟩ | ⟨h, -, h3⟩ |
    ⟨h, -, -⟩
  · rw [h] at hc; cases hc
    have : ((m' j : ℕ) : ℝ) = (m j : ℕ) + 1 := by exact_mod_cast h3
    linarith [h1.2, h2.1]
  · rw [h] at hc; cases hc
    have : ((m j : ℕ) : ℝ) = (m' j : ℕ) + 1 := by exact_mod_cast h3
    linarith [h1.1, h2.2]
  · rw [h] at hc; cases hc

/-- **Tangential continuity of the cell fields**: on a set `F` of points of two closed cells, the
fields of the cells have the same tangential traces (the tangent vectors of `F` vanish in the
directions fixed by the common face, where the local coordinates are the fixed values). -/
theorem tangentialTraceEq_cellField {ω : CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n)}
    (hω : ω ∈ cubeCompatible fun _ : Fin n => N) (k : ℕ) {m m' : CubeCell fun _ : Fin n => N}
    {F : Finset (Fin n → ℝ)} (hF : ∀ v ∈ F, v ∈ closedCell m ∧ v ∈ closedCell m')
    {x : Fin n → ℝ} (hx : x ∈ closedCell m) (hx' : x ∈ closedCell m') :
    TangentialTraceEq F k (cellField ω m x) (cellField ω m' x) := by
  intro V hV
  have hadj := adj_of_mem_closedCell hx hx'
  set g := commonFace _ m m'
  set g' := commonFace _ m' m
  -- the tangent vectors of `F` vanish in the fixed directions
  have hzero : ∀ j, g j ≠ none → ∀ l, V j l = 0 := fun j hj l => by
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hj
    have hle : vectorSpan ℝ (F : Set (Fin n → ℝ)) ≤ LinearMap.ker (LinearMap.proj j) := by
      rw [vectorSpan_def, Submodule.span_le]
      rintro _ ⟨p, hp, q, hq, rfl⟩
      have h1 := localCoord_eq_of_commonFace (hF p hp).1 (hF p hp).2 hc
      have h2 := localCoord_eq_of_commonFace (hF q hq).1 (hF q hq).2 hc
      have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_proj, Function.eval,
        vsub_eq_sub, Pi.sub_apply]
      have : (N : ℝ) * (p j - q j) = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hN
    simpa using hle (hV l)
  have hnone : ∀ j, g' j = none ↔ g j = none := fun j => by
    rcases commonFace_cases hadj j with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ <;>
      simp [g, g', h1, h2]
  have hy : ∀ j c, g j = some c → affine (cellMatrix n N) (cellOffset m) x j = c :=
    fun j c hc => by rw [affine_cellMatrix]; exact localCoord_eq_of_commonFace hx hx' hc
  have hy' : ∀ j c, g' j = some c → affine (cellMatrix n N) (cellOffset m') x j = c :=
    fun j c hc => by rw [affine_cellMatrix]; exact localCoord_eq_of_commonFace hx' hx hc
  have hyy : ∀ j, g' j = none → affine (cellMatrix n N) (cellOffset m) x j =
      affine (cellMatrix n N) (cellOffset m') x j := fun j hj => by
    rcases commonFace_cases hadj j with ⟨-, h2, -⟩ | ⟨-, h2, -⟩ | ⟨-, -, h3⟩
    · simp [g', h2] at hj
    · simp [g', h2] at hj
    · rw [affine_cellMatrix, affine_cellMatrix, h3]
  simp only [cellField, affinePullback_apply]
  rw [pullback_pullback, pullback_pullback, pullback_apply, pullback_apply]
  refine sum_congr rfl fun s _ => ?_
  by_cases hs : ∀ j ∈ s, g j = none
  · congr 1
    have hsf : ∀ j ∈ s, (g j).isNone := fun j hj => by simp [hs j hj]
    have hsf' : ∀ j ∈ s, (g' j).isNone := fun j hj => by simp [(hnone j).2 (hs j hj)]
    simp only [evalForm_apply]
    rw [← eval_faceSubst hy, show faceSubst g (ω m s) = cubeTrace g (ω m) s by
        simp only [cubeTrace]; rw [ite_eq_left hsf], hω m m' hadj,
      show cubeTrace g' (ω m') s = faceSubst g' (ω m' s) by
        simp only [cubeTrace]; rw [ite_eq_left hsf'],
      eval_faceSubst_congr hyy, eval_faceSubst hy']
  · push Not at hs
    obtain ⟨j, hj, hgj⟩ := hs
    have hrow : (fun l => ∑ i, cellMatrix n N j i * V i l) = 0 := funext fun l => by
      simp [cellMatrix, hzero j hgj l]
    rw [wedgeProd_eq_zero_of_mem hj hrow]
    simp

theorem cubeRefinement_domain :
    (cubeRefinement n N).domain = Set.univ.pi fun _ => Set.Ioo 0 1 := by
  rw [freudenthalMesh_domain]
  simp

/-- **`HΛᵏ`-conformity of the cubical spaces** ([AFW2006], §5; [ArnoldBoffiBonizzoni2015], §3): a
tangentially continuous piecewise polynomial `k`-form on the cubical mesh of `(0, 1)ⁿ` with `N`
cells per direction lies in `HΛᵏ((0, 1)ⁿ) = D(d_max)`, and `d_max` is the piecewise exterior
derivative. The piecewise field is glued on the Freudenthal refinement, each simplex carrying the
field of its cell. -/
theorem cellField_mem_maximal_domain [NeZero n] (k : ℕ)
    {ω : CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n)}
    (hω : ω ∈ cubeCompatible fun _ : Fin n => N) (hk : ∀ m, IsDeg k (ω m)) :
    ∃ h : pieceL2 (cubeRefinement n N) (cubeRefinement n N).domain
        (fun T => formComp (k := k) (cellField ω (simplexCell T)))
        (fun _ _ s => continuous_formComp (contDiff_cellField ω _ (r := 0)).continuous s) ∈
        ((extDerivOp ℝ n k).maximal (cubeRefinement n N).domain).domain,
      (extDerivOp ℝ n k).maximal (cubeRefinement n N).domain ⟨_, h⟩ =
        pieceL2 (cubeRefinement n N) (cubeRefinement n N).domain
          (fun T => formComp (k := (k : ℤ) + 1)
            (cellField (fun m => Koszul.extDeriv (ω m)) (simplexCell T)))
          (fun _ _ t => continuous_formComp (contDiff_cellField _ _ (r := 0)).continuous t) := by
  have hΩ : IsOpen (cubeRefinement n N).domain := by
    rw [cubeRefinement_domain]; exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
  obtain ⟨h, hval⟩ := extDeriv_pieceL2_mem_maximal_domain k (cubeRefinement n N) hΩ
    (η := fun T => cellField ω (simplexCell T)) (fun T _ => contDiff_cellField _ _)
    (fun T _ x => isDeg_cellField (hk _) x) fun F _ T hT T' hT' x hx => by
      obtain ⟨hT, hFT⟩ := (cubeRefinement n N).mem_cofaces.1 hT
      obtain ⟨hT', hFT'⟩ := (cubeRefinement n N).mem_cofaces.1 hT'
      have hsub : convexHull ℝ (F : Set (Fin n → ℝ)) ⊆ T.closedInterior ∩ T'.closedInterior := by
        rw [(cubeRefinement n N).inter_closedInterior T hT T' hT']
        exact convexHull_mono fun v hv => ⟨hFT hv, hFT' hv⟩
      have hmem : ∀ y ∈ convexHull ℝ (F : Set (Fin n → ℝ)),
          y ∈ closedCell (simplexCell (N := N) T) ∧ y ∈ closedCell (simplexCell (N := N) T') :=
        fun y hy => ⟨simplexCell_closedInterior_subset hT (hsub hy).1,
          simplexCell_closedInterior_subset hT' (hsub hy).2⟩
      exact tangentialTraceEq_cellField hω k
        (fun v hv => hmem v (subset_convexHull ℝ _ hv)) (hmem x hx).1 (hmem x hx).2
  refine ⟨h, hval.trans (pieceL2_congr _ _ _ _ fun T _ => ?_)⟩
  simp only [extDeriv_cellField]

/-- The global spaces `Q_b⁻Λᵏ(𝒯_h)` are `HΛᵏ`-conforming. -/
theorem cellField_mem_maximal_domain_of_mem [NeZero n] {b : Fin n → ℕ} (k : ℕ)
    {ω : CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n)}
    (hω : ω ∈ cubeGlobalSpace (fun _ : Fin n => N) b k) :
    pieceL2 (cubeRefinement n N) (cubeRefinement n N).domain
        (fun T => formComp (k := k) (cellField ω (simplexCell T)))
        (fun _ _ s => continuous_formComp (contDiff_cellField ω _ (r := 0)).continuous s) ∈
      ((extDerivOp ℝ n k).maximal (cubeRefinement n N).domain).domain :=
  (cellField_mem_maximal_domain k (mem_cubeGlobalSpace.1 hω).1
    fun m => ((mem_cubeGlobalSpace.1 hω).2 m).1).1

end Feec.FiniteElement
