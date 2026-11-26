module

public import Feec.FiniteElement.CubeMesh
public import Feec.FiniteElement.Assembly
public import Feec.FiniteElement.LocalSpace
public import Feec.FiniteElement.PolyInverseEstimate
public import Feec.Mesh.Freudenthal

/-!
# `HΛ`-conformity of the cubical spaces `Q_r⁻Λᵏ(𝒯_h)`

On the uniform cubical mesh of `(0, L)ⁿ`, tangentially continuous piecewise polynomial forms lie in
`HΛᵏ((0, L)ⁿ)` ([AFW2006], §5; [ArnoldBoffiBonizzoni2015], §5) and form a subcomplex.

## Main results

* `Cube.cellField_mem_maximal_domain`: tangentially continuous piecewise forms lie in `HΛᵏ`.
* `Cube.finrank_cubeV`: `dim Vₕᵏ = Σ_{#s = k} Πⱼ (N b_j + 1 - [j ∈ s])` for `b_j ≥ 1`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]
* [D. N. Arnold, D. Boffi, F. Bonizzoni, *Finite element differential forms on curvilinear cubic meshes and their approximation properties*][ArnoldBoffiBonizzoni2015]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MvPolynomial

@[expose] public noncomputable section

namespace Feec.FiniteElement.Cube

open Feec.Domain Feec.Mesh Koszul ExteriorFibre

variable {n : ℕ} {L : ℝ} {N : ℕ}

/-! ### The cell fields in global coordinates -/

/-- The offset `-m` of the local coordinates of the cell `m`. -/
def cellOffset (m : CubeCell fun _ : Fin n => N) : Fin n → ℝ := fun i => -((m i : ℕ) : ℝ)

theorem affine_cellOffset (m : CubeCell fun _ : Fin n => N) (x : Fin n → ℝ) (i : Fin n) :
    affine (scalarMat n (N / L)) (cellOffset m) x i = N / L * x i - m i := by
  simp [affine_scalarMat, cellOffset, sub_eq_add_neg]

variable (L) in
/-- The field of the cell `m` in global coordinates: `ω_m` pulled back by `x ↦ x / h - m`. -/
def cellField (ω : CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n))
    (m : CubeCell fun _ : Fin n => N) : FormField n :=
  affinePullback (scalarMat n (N / L)) (cellOffset m) (evalForm n (ω m))

theorem contDiff_cellField (ω : CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n))
    (m : CubeCell fun _ : Fin n => N) {r : WithTop ℕ∞} : ContDiff ℝ r (cellField L ω m) := by
  rw [cellField, ← evalForm_polyPullback]
  exact contDiff_evalForm _

theorem extDeriv_cellField (ω : CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n))
    (m : CubeCell fun _ : Fin n => N) :
    extDeriv (cellField L ω m) = cellField L (fun m => Koszul.extDeriv (ω m)) m := by
  funext x
  rw [cellField, extDeriv_affinePullback_apply _ _
    ((contDiff_evalForm (ω m) (r := 1)).differentiable one_ne_zero _), extDeriv_evalForm]
  rfl

theorem isDeg_cellField {k : ℕ} {ω : CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n)}
    {m : CubeCell fun _ : Fin n => N} (hk : IsDeg k (ω m)) (x : Fin n → ℝ) :
    IsDeg k (cellField L ω m x) :=
  IsDeg.affinePullback (fun y s hs => by simp [evalForm_apply, hk s hs]) _ _ x

variable (L) in
/-- The pullback `F_m^* w` of a form field to the local coordinates of the cell `m`. -/
def cellPullback (m : CubeCell fun _ : Fin n => N) (w : FormField n) : FormField n :=
  affinePullback (scalarMat n (L / N)) (fun i => L / N * ((m i : ℕ) : ℝ)) w

theorem affine_cellPullback (m : CubeCell fun _ : Fin n => N) (y : Fin n → ℝ) :
    affine (scalarMat n (L / N)) (fun i => L / N * ((m i : ℕ) : ℝ)) y =
      (fun i => L / N * ((m i : ℕ) : ℝ)) + (L / N) • y := by
  rw [affine_scalarMat, add_comm]

variable [Fact (0 < L)]

theorem cellScale_ne_zero [NeZero N] : (N : ℝ) / L ≠ 0 :=
  div_ne_zero (Nat.cast_ne_zero.2 (NeZero.ne N)) (Fact.out : 0 < L).ne'

theorem cellPullback_cellField [NeZero N]
    (ω : CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n)) (m : CubeCell fun _ : Fin n => N) :
    cellPullback L m (cellField L ω m) = evalForm n (ω m) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hL : L ≠ 0 := (Fact.out : 0 < L).ne'
  refine affinePullback_affinePullback_of_comp_eq_id _ _ _ _ (fun y => funext fun i => ?_) _
  rw [affine_cellOffset, affine_scalarMat]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem affinePullback_cellPullback [NeZero N] (m : CubeCell fun _ : Fin n => N)
    (w : FormField n) :
    affinePullback (scalarMat n (N / L)) (cellOffset m) (cellPullback L m w) = w := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hL : L ≠ 0 := (Fact.out : 0 < L).ne'
  refine affinePullback_affinePullback_of_comp_eq_id _ _ _ _ (fun x => funext fun i => ?_) w
  rw [affine_scalarMat, Pi.add_apply, Pi.smul_apply, affine_cellOffset, smul_eq_mul]
  field_simp
  ring

/-! ### The Freudenthal refinement -/

variable [NeZero N]

variable (n L N) in
/-- The Freudenthal refinement of the cubical mesh of `(0, L)ⁿ` with `N` cells per direction. -/
abbrev cubeRefinement : SimplicialMesh n := freudenthalMesh 0 L Fact.out N

variable (L) in
/-- The cell of a simplex of the refinement, read off its first vertex `h m`. -/
def simplexCell (T : Affine.Simplex ℝ (Fin n → ℝ) n) : CubeCell fun _ : Fin n => N := fun j =>
  (⟨min ⌊(N / L : ℝ) * T.points 0 j⌋₊ (N - 1), by have := NeZero.pos N; omega⟩ : Fin N)

omit [Fact (0 < L)] [NeZero N] in
variable (L) in
/-- The closed cell `∏ⱼ h [m_j, m_j + 1]`. -/
def closedCell (m : CubeCell fun _ : Fin n => N) : Set (Fin n → ℝ) :=
  {x | ∀ j, ((m j : ℕ) : ℝ) ≤ N / L * x j ∧ N / L * x j ≤ (m j : ℕ) + 1}

theorem simplexCell_freudenthal (m : Fin n → Fin N) (σ : Equiv.Perm (Fin n)) :
    simplexCell L (mapEquiv (boxMap 0 (L / N) (freudenthalScale_ne_zero Fact.out N))
      (freudenthalSimplex (finLattice m) σ)) = m := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hL : L ≠ 0 := (Fact.out : 0 < L).ne'
  funext j
  refine Fin.ext ?_
  change min ⌊(N / L : ℝ) * _⌋₊ (N - 1) = _
  rw [mapEquiv_points, freudenthalSimplex_points, kuhnVertex_zero, add_zero, boxMap_apply,
    zero_add, Pi.smul_apply, latticePoint_apply, smul_eq_mul]
  simp only [finLattice, Int.cast_natCast]
  rw [show (N / L : ℝ) * (L / N * (m j : ℕ)) = (m j : ℕ) by field_simp, Nat.floor_natCast]
  have := (m j).isLt
  omega

theorem simplexCell_closedInterior_subset {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (cubeRefinement n L N).simplices) :
    T.closedInterior ⊆ closedCell L (simplexCell (N := N) L T) := by
  obtain ⟨m, σ, rfl⟩ := mem_freudenthalMesh_simplices.1 hT
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hL : L ≠ 0 := (Fact.out : 0 < L).ne'
  rw [simplexCell_freudenthal, closedInterior_freudenthalMesh_simplex]
  rintro _ ⟨x, hx, rfl⟩ j
  have := hx.1 j
  simp only [Pi.sub_apply, latticePoint_apply, finLattice, Int.cast_natCast] at this
  simp only [zero_add, Pi.smul_apply, smul_eq_mul]
  rw [show (N / L : ℝ) * (L / N * x j) = x j by field_simp]
  constructor <;> linarith [this.1, this.2]

omit [NeZero N] in
theorem closedCell_eq_pi (m : CubeCell fun _ : Fin n => N) :
    closedCell L m = Set.univ.pi fun j =>
      Set.Icc (L / N * ((m j : ℕ) : ℝ)) (L / N * (((m j : ℕ) : ℝ) + 1)) := by
  have hL : 0 < L := Fact.out
  ext x
  simp only [closedCell, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  refine forall_congr' fun j => ?_
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; exact absurd (m j).isLt (by simp)
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hL, div_le_iff₀ hL, div_mul_eq_mul_div,
    div_le_iff₀ hN', le_div_iff₀ hN']
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

omit [NeZero N] in
theorem dist_le_of_mem_closedCell {m : CubeCell fun _ : Fin n => N} {x z : Fin n → ℝ}
    (hx : x ∈ closedCell L m) (hz : z ∈ closedCell L m) : dist x z ≤ L / N := by
  rw [closedCell_eq_pi] at hx hz
  refine (dist_pi_le_iff (div_nonneg (Fact.out : 0 < L).le (Nat.cast_nonneg N))).2 fun j => ?_
  have h1 := hx j (Set.mem_univ j)
  have h2 := hz j (Set.mem_univ j)
  rw [Real.dist_eq, abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

omit [Fact (0 < L)] [NeZero N] in
theorem adj_of_mem_closedCell {m m' : CubeCell fun _ : Fin n => N} {x : Fin n → ℝ}
    (hx : x ∈ closedCell L m) (hx' : x ∈ closedCell L m') : CubeCell.Adj _ m m' := fun j => by
  have h1 := hx j
  have h2 := hx' j
  have e1 : ((m j : ℕ) : ℝ) ≤ (m' j : ℕ) + 1 := by linarith [h1.1, h2.2]
  have e2 : ((m' j : ℕ) : ℝ) ≤ (m j : ℕ) + 1 := by linarith [h1.2, h2.1]
  exact ⟨by exact_mod_cast e1, by exact_mod_cast e2⟩

omit [Fact (0 < L)] [NeZero N] in
theorem localCoord_eq_of_commonFace {m m' : CubeCell fun _ : Fin n => N} {x : Fin n → ℝ}
    (hx : x ∈ closedCell L m) (hx' : x ∈ closedCell L m') {j : Fin n} {c : ℝ}
    (hc : commonFace _ m m' j = some c) : N / L * x j - m j = c := by
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

omit [Fact (0 < L)] [NeZero N] in
theorem cellField_apply_eq_of_free {ω : CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n)}
    (hω : ω ∈ cubeCompatible fun _ : Fin n => N) {m m' : CubeCell fun _ : Fin n => N}
    {x : Fin n → ℝ} (hx : x ∈ closedCell L m) (hx' : x ∈ closedCell L m') {s : Finset (Fin n)}
    (hs : ∀ j ∈ s, commonFace _ m m' j = none) :
    cellField L ω m x s = cellField L ω m' x s := by
  have hadj := adj_of_mem_closedCell hx hx'
  set g := commonFace _ m m'
  set g' := commonFace _ m' m
  have hnone : ∀ j, g' j = none ↔ g j = none := fun j => by
    rcases commonFace_cases hadj j with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ <;>
      simp [g, g', h1, h2]
  have hy : ∀ j c, g j = some c → affine (scalarMat n (N / L)) (cellOffset m) x j = c :=
    fun j c hc => by rw [affine_cellOffset]; exact localCoord_eq_of_commonFace hx hx' hc
  have hy' : ∀ j c, g' j = some c → affine (scalarMat n (N / L)) (cellOffset m') x j = c :=
    fun j c hc => by rw [affine_cellOffset]; exact localCoord_eq_of_commonFace hx' hx hc
  have hyy : ∀ j, g' j = none → affine (scalarMat n (N / L)) (cellOffset m) x j =
      affine (scalarMat n (N / L)) (cellOffset m') x j := fun j hj => by
    rcases commonFace_cases hadj j with ⟨-, h2, -⟩ | ⟨-, h2, -⟩ | ⟨-, -, h3⟩
    · simp [g', h2] at hj
    · simp [g', h2] at hj
    · rw [affine_cellOffset, affine_cellOffset, h3]
  have hsf : ∀ j ∈ s, (g j).isNone := fun j hj => by simp [hs j hj]
  have hsf' : ∀ j ∈ s, (g' j).isNone := fun j hj => by simp [(hnone j).2 (hs j hj)]
  simp only [cellField, affinePullback_apply, pullback_scalarMat_apply, evalForm_apply]
  congr 1
  rw [← eval_faceSubst hy, show faceSubst g (ω m s) = cubeTrace g (ω m) s by
      simp only [cubeTrace]; rw [ite_eq_left hsf], hω m m' hadj,
    show cubeTrace g' (ω m') s = faceSubst g' (ω m' s) by
      simp only [cubeTrace]; rw [ite_eq_left hsf'],
    eval_faceSubst_congr hyy, eval_faceSubst hy']

theorem tangentialTraceEq_cellField {ω : CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n)}
    (hω : ω ∈ cubeCompatible fun _ : Fin n => N) (k : ℕ) {m m' : CubeCell fun _ : Fin n => N}
    {F : Finset (Fin n → ℝ)} (hF : ∀ v ∈ F, v ∈ closedCell L m ∧ v ∈ closedCell L m')
    {x : Fin n → ℝ} (hx : x ∈ closedCell L m) (hx' : x ∈ closedCell L m') :
    TangentialTraceEq F k (cellField L ω m x) (cellField L ω m' x) := by
  intro V hV
  -- the tangent vectors of `F` vanish in the fixed directions
  have hzero : ∀ j, commonFace _ m m' j ≠ none → V j = 0 := fun j hj => funext fun l => by
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hj
    have hle : vectorSpan ℝ (F : Set (Fin n → ℝ)) ≤ LinearMap.ker (LinearMap.proj j) := by
      rw [vectorSpan_def, Submodule.span_le]
      rintro _ ⟨p, hp, q, hq, rfl⟩
      have h1 := localCoord_eq_of_commonFace (hF p hp).1 (hF p hp).2 hc
      have h2 := localCoord_eq_of_commonFace (hF q hq).1 (hF q hq).2 hc
      have hNL : (N : ℝ) / L ≠ 0 := cellScale_ne_zero
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_proj, Function.eval,
        vsub_eq_sub, Pi.sub_apply]
      have : (N : ℝ) / L * (p j - q j) = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hNL
    simpa using hle (hV l)
  rw [pullback_apply, pullback_apply]
  refine sum_congr rfl fun s _ => ?_
  by_cases hs : ∀ j ∈ s, commonFace _ m m' j = none
  · rw [cellField_apply_eq_of_free hω hx hx' hs]
  · push Not at hs
    obtain ⟨j, hj, hgj⟩ := hs
    rw [wedgeProd_eq_zero_of_mem hj (hzero j hgj)]
    simp

theorem cubeRefinement_domain :
    (cubeRefinement n L N).domain = Set.univ.pi fun _ => Set.Ioo 0 L := by
  rw [freudenthalMesh_domain]
  simp

theorem isOpen_cubeRefinement_domain : IsOpen (cubeRefinement n L N).domain := by
  rw [cubeRefinement_domain]; exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

/-- A tangentially continuous piecewise polynomial `k`-form on the cubical mesh lies in
`HΛᵏ((0, L)ⁿ)`, with the piecewise `d` ([AFW2006], §5; [ArnoldBoffiBonizzoni2015], §5). -/
theorem cellField_mem_maximal_domain [NeZero n] (k : ℕ)
    {ω : CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n)}
    (hω : ω ∈ cubeCompatible fun _ : Fin n => N) (hk : ∀ m, IsDeg k (ω m)) :
    ∃ h : pieceL2 (cubeRefinement n L N) (cubeRefinement n L N).domain
        (fun T => formComp (k := k) (cellField L ω (simplexCell L T)))
        (fun _ _ s => continuous_formComp (contDiff_cellField ω _ (r := 0)).continuous s) ∈
        ((extDerivOp ℝ n k).maximal (cubeRefinement n L N).domain).domain,
      (extDerivOp ℝ n k).maximal (cubeRefinement n L N).domain ⟨_, h⟩ =
        pieceL2 (cubeRefinement n L N) (cubeRefinement n L N).domain
          (fun T => formComp (k := (k : ℤ) + 1)
            (cellField L (fun m => Koszul.extDeriv (ω m)) (simplexCell L T)))
          (fun _ _ t => continuous_formComp (contDiff_cellField _ _ (r := 0)).continuous t) := by
  have hΩ := isOpen_cubeRefinement_domain (n := n) (L := L) (N := N)
  obtain ⟨h, hval⟩ := extDeriv_pieceL2_mem_maximal_domain k (cubeRefinement n L N) hΩ
    (η := fun T => cellField L ω (simplexCell L T)) (fun T _ => contDiff_cellField _ _)
    (fun T _ x => isDeg_cellField (hk _) x) fun F _ T hT T' hT' x hx => by
      obtain ⟨hT, hFT⟩ := (cubeRefinement n L N).mem_cofaces.1 hT
      obtain ⟨hT', hFT'⟩ := (cubeRefinement n L N).mem_cofaces.1 hT'
      have hsub : convexHull ℝ (F : Set (Fin n → ℝ)) ⊆ T.closedInterior ∩ T'.closedInterior := by
        rw [(cubeRefinement n L N).inter_closedInterior T hT T' hT']
        exact convexHull_mono fun v hv => ⟨hFT hv, hFT' hv⟩
      have hmem : ∀ y ∈ convexHull ℝ (F : Set (Fin n → ℝ)),
          y ∈ closedCell L (simplexCell (N := N) L T) ∧
            y ∈ closedCell L (simplexCell (N := N) L T') :=
        fun y hy => ⟨simplexCell_closedInterior_subset hT (hsub hy).1,
          simplexCell_closedInterior_subset hT' (hsub hy).2⟩
      exact tangentialTraceEq_cellField hω k
        (fun v hv => hmem v (subset_convexHull ℝ _ hv)) (hmem x hx).1 (hmem x hx).2
  refine ⟨h, hval.trans (pieceL2_congr _ _ _ _ fun T _ => ?_)⟩
  simp only [extDeriv_cellField]

theorem cellField_mem_maximal_domain_of_mem [NeZero n] {b : Fin n → ℕ} (k : ℕ)
    {ω : CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n)}
    (hω : ω ∈ cubeGlobalSpace (fun _ : Fin n => N) b k) :
    pieceL2 (cubeRefinement n L N) (cubeRefinement n L N).domain
        (fun T => formComp (k := k) (cellField L ω (simplexCell L T)))
        (fun _ _ s => continuous_formComp (contDiff_cellField ω _ (r := 0)).continuous s) ∈
      ((extDerivOp ℝ n k).maximal (cubeRefinement n L N).domain).domain :=
  (cellField_mem_maximal_domain k (mem_cubeGlobalSpace.1 hω).1
    fun m => ((mem_cubeGlobalSpace.1 hω).2 m).1).1

/-! ### The glued spaces form a subcomplex of `HΛ((0, L)ⁿ)` -/

omit [Fact (0 < L)] [NeZero N] in
theorem cellField_add (ω η : CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n))
    (m : CubeCell fun _ : Fin n => N) :
    cellField L (ω + η) m = cellField L ω m + cellField L η m := by
  funext x
  simp [cellField, affinePullback_apply, map_add, pullback_add]

omit [Fact (0 < L)] [NeZero N] in
theorem cellField_smul (c : ℝ) (ω : CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n))
    (m : CubeCell fun _ : Fin n => N) : cellField L (c • ω) m = c • cellField L ω m := by
  funext x
  simp [cellField, affinePullback_apply, map_smul, pullback_smul]

omit [Fact (0 < L)] [NeZero N] in
theorem cellField_sub (ω η : CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n))
    (m : CubeCell fun _ : Fin n => N) :
    cellField L (ω - η) m = cellField L ω m - cellField L η m := by
  funext x
  simp [cellField, affinePullback_apply, map_sub, pullback_sub]

variable (n L N) in
/-- The gluing of a piecewise polynomial form into `L²((0, L)ⁿ; Λᵏ)`. -/
def cubeGlue (k : ℤ) : (CubeCell (fun _ : Fin n => N) → PolyForm ℝ (Fin n)) →ₗ[ℝ]
    L2F ℝ (cubeRefinement n L N).domain (formIdx n k) where
  toFun ω := pieceL2 (cubeRefinement n L N) (cubeRefinement n L N).domain
    (fun T => formComp (k := k) (cellField L ω (simplexCell L T)))
    (fun _ _ s => continuous_formComp (contDiff_cellField ω _ (r := 0)).continuous s)
  map_add' ω η := by
    refine (pieceL2_congr _ _ _ _ fun T _ => ?_).trans (pieceL2_add _ _ _ _)
    funext s x
    simp [formComp, cellField_add]
  map_smul' c ω := by
    refine (pieceL2_congr _ _ _ _ fun T _ => ?_).trans (pieceL2_smul _ _ c _)
    funext s x
    simp [formComp, cellField_smul]

variable (n L N) in
/-- The glued global spaces `Vₕᵏ = Q_b⁻Λᵏ(𝒯_h) ⊆ L²((0, L)ⁿ; Λᵏ)`. -/
def cubeV (b : Fin n → ℕ) (k : ℤ) :
    Submodule ℝ (L2F ℝ (cubeRefinement n L N).domain (formIdx n k)) :=
  LinearMap.range (cubeGlue n L N k ∘ₗ (cubeGlobalSpace (fun _ : Fin n => N) b k.toNat).subtype)

instance (b : Fin n → ℕ) (k : ℤ) : FiniteDimensional ℝ (cubeV n L N b k) :=
  LinearMap.finiteDimensional_range _

theorem cubeV_le_maximal_domain [NeZero n] (b : Fin n → ℕ) (i : ℤ) :
    cubeV n L N b i ≤ ((extDerivOp ℝ n i).maximal (cubeRefinement n L N).domain).domain := by
  rintro x ⟨u, rfl⟩
  rcases i with k | k
  · exact cellField_mem_maximal_domain_of_mem k u.2
  · have := LocalElement.subsingleton_L2F_negSucc (cubeRefinement n L N).domain (n := n) k
    rw [Subsingleton.elim (LinearMap.comp _ _ u) 0]
    exact Submodule.zero_mem _

theorem maximal_apply_mem_cubeV [NeZero n] (b : Fin n → ℕ) (i : ℤ)
    (y : ((extDerivOp ℝ n i).maximal (cubeRefinement n L N).domain).domain)
    (hy : (y : L2F ℝ (cubeRefinement n L N).domain (formIdx n i)) ∈ cubeV n L N b i) :
    (extDerivOp ℝ n i).maximal (cubeRefinement n L N).domain y ∈ cubeV n L N b (i + 1) := by
  obtain ⟨u, hu⟩ := hy
  rcases i with k | k
  · have hω := mem_cubeGlobalSpace.1 u.2
    obtain ⟨h, hval⟩ := cellField_mem_maximal_domain (L := L) k hω.1 fun m => (hω.2 m).1
    have hy' : y = ⟨_, h⟩ := Subtype.ext hu.symm
    show (extDerivOp ℝ n (k : ℤ)).maximal (cubeRefinement n L N).domain y ∈
      cubeV n L N b ((k : ℤ) + 1)
    rw [hy', hval]
    exact ⟨⟨_, extDeriv_mem_cubeGlobalSpace u.2⟩, rfl⟩
  · have := LocalElement.subsingleton_L2F_negSucc (cubeRefinement n L N).domain (n := n) k
    have : y = 0 := Subtype.ext (Subsingleton.elim _ _)
    rw [this, LinearPMap.map_zero]
    exact Submodule.zero_mem _

variable (n L N) in
/-- The cubical finite element subcomplex `Q_b⁻Λ(𝒯_h)` of `HΛ((0, L)ⁿ)`. -/
def cubeSubcomplex [NeZero n] (b : Fin n → ℕ) :
    ((deRham ℝ n).maximalComplex
      (isOpen_cubeRefinement_domain (n := n) (L := L) (N := N))).Subcomplex where
  V := cubeV n L N b
  le_domain i j := by
    by_cases hij : i + 1 = j
    · subst hij
      rw [deRham_maximalComplex_d]
      exact cubeV_le_maximal_domain b i
    · rw [HilbertComplex.domain_eq_top_of_not_rel _ (by simpa using hij)]
      exact le_top
  mapsTo i j x hx := by
    by_cases hij : i + 1 = j
    · subst hij
      exact LocalElement.apply_mem_of_eq (deRham_maximalComplex_d
        (isOpen_cubeRefinement_domain (n := n) (L := L) (N := N)) i) _
        (· ∈ cubeV n L N b (i + 1))
        fun y' hy' => maximal_apply_mem_cubeV b i y' (hy' ▸ hx)
    · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hij)]
      exact Submodule.zero_mem _

instance (b : Fin n → ℕ) (k : ℤ) [NeZero n] :
    FiniteDimensional ℝ ((cubeSubcomplex n L N b).V k) :=
  inferInstanceAs (FiniteDimensional ℝ (cubeV n L N b k))

/-! ### Injectivity of the gluing and the dimension of `Vₕᵏ` -/

theorem cubeGlue_injective [NeZero n] (b : Fin n → ℕ) (k : ℕ) :
    Function.Injective (cubeGlue n L N k ∘ₗ
      (cubeGlobalSpace (fun _ : Fin n => N) b k).subtype) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  refine Subtype.ext (funext fun m => ?_)
  set M := cubeRefinement n L N
  have hΩ := isOpen_cubeRefinement_domain (n := n) (L := L) (N := N)
  have hk : IsDeg k (u.1 m) := ((mem_cubeGlobalSpace.1 u.2).2 m).1
  set T := mapEquiv (boxMap 0 (L / N) (freudenthalScale_ne_zero Fact.out N))
    (freudenthalSimplex (finLattice m) 1)
  have hT : T ∈ M.simplices := mem_freudenthalMesh_simplices.2 ⟨m, 1, rfl⟩
  have hcell : simplexCell (N := N) L T = m := simplexCell_freudenthal m 1
  set U := interior T.closedInterior ∩ M.domain
  have hU : IsOpen U := isOpen_interior.inter hΩ
  have hUne : U.Nonempty := by
    obtain ⟨z, hz⟩ := interior_closedInterior_nonempty T
    have hz' : z ∈ closure M.domain := M.closedInterior_subset_closure hT (interior_subset hz)
    obtain ⟨w, hw, hwΩ⟩ := mem_closure_iff.1 hz' _ isOpen_interior hz
    exact ⟨w, hw, hwΩ⟩
  -- the cell field vanishes on `U`
  have hzero : ∀ x ∈ U, cellField L u.1 m x = 0 := fun x hx => funext fun s => by
    by_cases hs : #s = k
    · set s' : formIdx n (k : ℤ) := ⟨s, by rw [hs]⟩
      set f : (Fin n → ℝ) → ℝ := fun y => cellField L u.1 m y s
      have hf : Continuous f :=
        (continuous_apply s).comp (contDiff_cellField u.1 m (r := 0)).continuous
      have hcomp := coeFn_pieceL2 M M.domain
        (fun T' => formComp (k := (k : ℤ)) (cellField L u.1 (simplexCell L T')))
        (fun _ _ s => continuous_formComp (contDiff_cellField u.1 _ (r := 0)).continuous s) s'
      have h0 : (cubeGlue n L N k u.1) s' = 0 := by
        have := congrArg (fun v : L2F ℝ M.domain (formIdx n (k : ℤ)) => v s') hu
        simpa using this
      have hae : f =ᵐ[MeasureTheory.volume.restrict U] 0 := by
        have h1 : (fun y => pieceFun M
            (fun T' => formComp (k := (k : ℤ)) (cellField L u.1 (simplexCell L T')) s') y)
            =ᵐ[MeasureTheory.volume.restrict M.domain] 0 := by
          refine hcomp.symm.trans ?_
          have := MeasureTheory.Lp.coeFn_zero ℝ 2 (MeasureTheory.volume.restrict M.domain)
          change ((cubeGlue n L N k u.1) s' : (Fin n → ℝ) → ℝ) =ᵐ[_] 0
          rw [h0]
          exact this
        have h2 := MeasureTheory.ae_restrict_of_ae_restrict_of_subset (s := U)
          Set.inter_subset_right h1
        filter_upwards [h2, MeasureTheory.ae_restrict_mem hU.measurableSet] with y hy hyU
        rw [← hy, pieceFun_of_mem_interior M _ hT hyU.1]
        simp [formComp, f, hcell, s']
      exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae hU hf.continuousOn continuousOn_const hx
    · exact isDeg_cellField hk x s hs
  -- hence `u_m` vanishes on an open set of local coordinates
  funext s
  set C : Fin n → Fin n → ℝ := scalarMat n (L / N)
  set c : Fin n → ℝ := fun i => L / N * ((m i : ℕ) : ℝ)
  obtain ⟨x₀, hx₀⟩ := hUne
  refine eq_zero_of_eval_eq_zero_of_isOpen (U := affine C c ⁻¹' U)
    (hU.preimage (continuous_affine C c)) (y₀ := affine (scalarMat n (N / L)) (cellOffset m) x₀) ?_
    fun y hy => ?_
  · show affine C c (affine (scalarMat n (N / L)) (cellOffset m) x₀) ∈ U
    convert hx₀ using 1
    have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
    have hL : L ≠ 0 := (Fact.out : 0 < L).ne'
    have hy : ∀ i, affine (scalarMat n (N / L)) (cellOffset m) x₀ i = N / L * x₀ i - m i :=
      affine_cellOffset m x₀
    generalize affine (scalarMat n (N / L)) (cellOffset m) x₀ = y at hy ⊢
    funext i
    rw [affine_scalarMat]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, c, hy]
    field_simp
    ring
  · have := congrFun (congrFun (cellPullback_cellField (L := L) u.1 m) y) s
    rw [evalForm_apply] at this
    rw [← this, cellPullback, affinePullback_apply, hzero _ hy, pullback_zero]
    rfl

/-- `dim Vₕᵏ = Σ_{#s = k} Πⱼ (N b_j + 1 - [j ∈ s])` for `b_j ≥ 1`. -/
theorem finrank_cubeV [NeZero n] {b : Fin n → ℕ} (hb : ∀ j, 1 ≤ b j) (k : ℕ) :
    Module.finrank ℝ (cubeV n L N b k) =
      ∑ s ∈ powersetCard k univ, ∏ j, (N * b j + 1 - if j ∈ s then 1 else 0) := by
  exact (LinearMap.finrank_range_of_inj (cubeGlue_injective (L := L) (N := N) b k)).trans
    (finrank_cubeGlobalSpace (fun _ => Nat.one_le_iff_ne_zero.2 (NeZero.ne N)) hb)

end Feec.FiniteElement.Cube
