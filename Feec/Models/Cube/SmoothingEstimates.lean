module

public import Feec.FiniteElement.InverseEstimate
public import Feec.Models.Cube.FiniteElementMethod

/-!
# The smoothed-projection estimates on the Freudenthal meshes of the cube

**The estimates `FEM.SmoothingEstimates` and `FEM.SmoothingEstimatesMin` hold**
(`FEM.smoothingEstimates_pMax`, `FEM.smoothingEstimatesMin_pMin`; as bare existence statements
`FEM.smoothingEstimates_exists`, `FEM.smoothingEstimatesMin_exists`): for the parameters
`pMax γ` (dilation factor `1 - γ h_N` about the centre of `Q = (0, ½)ⁿ`) and `pMin γ` (factor
`1 + γ h_N`), with bump radii `γ h_N / 64 < γ h_N / 32`, `h_N = 1 / (2 (N + 1))` and `γ` small
depending only on `n`, the smoothed canonical interpolants `Q_N = Π_h R_N` of the Whitney
complexes of the level-`(N + 1)` Freudenthal meshes (with vanishing boundary DOFs for `pMin`) are
bounded in `L²` uniformly in `N` and satisfy `‖v - Q_N v‖ ≤ ½ ‖v‖` on the Whitney spaces
([AFW2010], §5.4; [ChristiansenWinther2008]). All the consequences proved under these estimates in
`Feec.Models.Cube.FiniteElementMethod` therefore hold unconditionally for these parameters, for
instance uniformly bounded cochain projections (`exists_uniform_cochainProjection`,
`exists_uniform_cochainProjectionMin`).

The proof uses that every simplex of the mesh is `h_N (m + K_σ)`, a homothetic copy of one of the
`n!` Kuhn simplices ([Freudenthal1942], [Kuhn1960]), so the inverse estimates of
`Feec.FiniteElement.InverseEstimate` hold with one constant (`DofBound`, `InvBound`). Both
families are treated at once through the admissible parameters `IsAdm` (centre of the cube,
`|c - 1| = γ h_N`, the bump radii above).

* **Uniform bound** (`exists_norm_smoothedInterp_le`). On a simplex `T`, the local DOF estimate
  bounds `Q_N x` by the face integrals of the smoothed field, `O(h_Nᵏ sup_T |R x|)`
  (`abs_simplexIntegral_face_le`), and by Jensen's inequality for the mollifier
  `|R x (y)|² ≤ c^{2k} |B(0, rIn)|⁻¹ ∫_{B̄(ŷ, rOut)} |x̄|²` (`abs_smoothForm_le`), so
  `‖Q_N x‖²_{L²(T)} ≲ (32/γ)ⁿ m_T(x)` with the local mass `m_T(x)` of `x` on the
  `2 h_N`-neighbourhood of `T` (`sum_integral_sq_interp_le`). A point lies in at most `6ⁿ n!`
  such neighbourhoods (`card_filter_mem_cthickening_le`, `sum_locMass_le`).
* **Closeness on `Vₕ`** (`exists_gamma`). For `v ∈ Vₕ` and a `k`-face `g` of `T`, the face
  integrand of `v_T - R v` is a mollified average of `Σₛ (v_T(x) - cᵏ v̄(t))ₛ minorₛ`
  (`sum_sub_smoothForm_mul_eq`). At points of `g` whose barycentric coordinates are `≥ γ`, every
  simplex `T'` met by the smoother contains `g` (`subset_vertexSet_of_near`, through the
  separation of the lattice points `isSep_latticePoint_add_sum`,
  `mem_freudenthalSet_of_isSep`, and the face-to-face property); there the traces of `v_T` and
  `v_{T'}` agree (`sum_mul_minor_eq`, `simplexIntegral_eq_of_mem_globalSpace`). The error
  there, normalized by `h^{n/2} / hᵏ`, is `O(γ)`: the dilation defect `1 - cᵏ = O(γ h)` is of lower
  order, and the dominant term is the displacement `O(γ h)` of the sample points against the
  Lipschitz inverse estimate `Lip(v_T) ≲ h⁻¹ h^{-n/2} ‖v_T‖`. The remaining boundary layer of `g` has measure `O(γ)`
  (`volume_real_nearBdry_le`). Hence `h^{n/2} |∫_g (v_T - R v)| ≲ γ hᵏ m_T(v)^{1/2}`
  (`sqrt_mul_abs_dof_err_le`) and `‖v - Q_N v‖² ≲ γ² ‖v‖²` (`norm_sq_sub_smoothedInterp_le`).
  Samples of the smoother outside `Q` are controlled by the condition `SampleOK`: vacuous for
  the maximal family (`sampleOK_pMax`); for the minimal family a sample outside `Q` near a point
  of `g` with weights `≥ γ` forces `g` into a coordinate face of the cube, hence into a boundary
  facet of the mesh (`exists_boundaryFacet_of_lower`, `exists_boundaryFacet_of_upper`,
  `not_isInteriorFacet_of_coord`), where the DOFs of `V̊ₕ` vanish (`sampleOK_pMin`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.4 (smoothed projections: the estimates for `ε ≈ h`)
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]
* [H. W. Kuhn, *Some combinatorial lemmas in topology*][Kuhn1960]

Bibliography: [references.bib](../../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset Filter

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex ExteriorFibre

variable {n : ℕ}

/-! ### Separated points of the lattice -/

/-- A point is **`θ`-separated** if its coordinates and their differences are integers or at
distance at least `θ` from every integer. -/
def IsSep (θ : ℝ) (x : Fin n → ℝ) : Prop :=
  (∀ l (z : ℤ), x l = z ∨ θ ≤ |x l - z|) ∧ (∀ l l' (z : ℤ), x l - x l' = z ∨ θ ≤ |x l - x l' - z|)

theorem sep_aux {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 2) {X σ : ℝ} (N : ℤ)
    (hσ : σ = 0 ∨ σ = 1 ∨ (θ ≤ σ ∧ σ ≤ 1 - θ)) (hX : X = N + σ ∨ X = N - σ) (z : ℤ) :
    X = z ∨ θ ≤ |X - z| := by
  have hint : ∀ m : ℤ, (m : ℝ) = 0 ∨ θ ≤ |(m : ℝ)| := by
    intro m
    rcases eq_or_ne m 0 with h | h
    · left; simp [h]
    · right
      have : (1 : ℝ) ≤ |(m : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h
      linarith
  set M := N - z
  have hM : (N : ℝ) - z = M := by simp [M]
  rcases hσ with rfl | rfl | ⟨h1, h2⟩
  · have hX' : X - z = M := by rcases hX with rfl | rfl <;> simp [← hM]
    rcases hint M with h | h
    · left; linarith
    · right; rwa [hX']
  · rcases hX with rfl | rfl
    · rcases hint (M + 1) with h | h
      · left; push_cast at h; linarith
      · right; push_cast at h; rwa [show (N : ℝ) + 1 - z = M + 1 by linarith]
    · rcases hint (M - 1) with h | h
      · left; push_cast at h; linarith
      · right; push_cast at h; rwa [show (N : ℝ) - 1 - z = M - 1 by linarith]
  · right
    rcases hX with rfl | rfl
    · rw [show (N : ℝ) + σ - z = M + σ by linarith]
      rcases le_or_gt 0 M with hM0 | hM0
      · have : (0 : ℝ) ≤ M := by exact_mod_cast hM0
        rw [abs_of_nonneg (by linarith)]; linarith
      · have : (M : ℝ) ≤ -1 := by exact_mod_cast (show M ≤ -1 by omega)
        rw [abs_of_nonpos (by linarith)]; linarith
    · rw [show (N : ℝ) - σ - z = M - σ by linarith]
      rcases le_or_gt 1 M with hM0 | hM0
      · have : (1 : ℝ) ≤ M := by exact_mod_cast hM0
        rw [abs_of_nonneg (by linarith)]; linarith
      · have : (M : ℝ) ≤ 0 := by exact_mod_cast (show M ≤ 0 by omega)
        rw [abs_of_nonpos (by linarith)]; linarith

theorem sum_subset_cases {k : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ) {μ : Fin (k + 1) → ℝ} (hμ : ∀ a, θ ≤ μ a)
    (hμ1 : ∑ a, μ a = 1) (J : Finset (Fin (k + 1))) :
    ∑ a ∈ J, μ a = 0 ∨ ∑ a ∈ J, μ a = 1 ∨ (θ ≤ ∑ a ∈ J, μ a ∧ ∑ a ∈ J, μ a ≤ 1 - θ) := by
  classical
  rcases J.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · left; simp
  by_cases hJ : J = Finset.univ
  · right; left; rw [hJ, hμ1]
  · right; right
    obtain ⟨b, hb⟩ : ∃ b, b ∉ J := by
      by_contra h; push Not at h; exact hJ (Finset.eq_univ_of_forall h)
    have hsplit := Finset.sum_add_sum_compl J μ
    rw [hμ1] at hsplit
    have hnn : ∀ c, 0 ≤ μ c := fun c => hθ0.trans (hμ c)
    refine ⟨(hμ a).trans (Finset.single_le_sum (fun c _ => hnn c) ha), ?_⟩
    have : μ b ≤ ∑ c ∈ Jᶜ, μ c :=
      Finset.single_le_sum (fun c _ => hnn c) (Finset.mem_compl.2 hb)
    linarith [hμ b]


theorem apply_latticePoint_add_sum (m : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) {k : ℕ}
    (j : Fin (k + 1) → Fin (n + 1)) (μ : Fin (k + 1) → ℝ) (l : Fin n) :
    (latticePoint m + ∑ a, μ a • kuhnVertex σ (j a)) l =
      m l + ∑ a ∈ Finset.univ.filter fun a => (σ.symm l : ℕ) < (j a : ℕ), μ a := by
  simp only [Pi.add_apply, latticePoint_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    kuhnVertex, mul_ite, mul_one, mul_zero, Finset.sum_ite, Finset.sum_const_zero, add_zero]

/-- **Points of a face with weights `≥ θ` are `θ`-separated** (in lattice coordinates). -/
theorem isSep_latticePoint_add_sum {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 2) (m : Fin n → ℤ)
    (σ : Equiv.Perm (Fin n)) {k : ℕ} (j : Fin (k + 1) → Fin (n + 1)) {μ : Fin (k + 1) → ℝ}
    (hμ : ∀ a, θ ≤ μ a) (hμ1 : ∑ a, μ a = 1) :
    IsSep θ (latticePoint m + ∑ a, μ a • kuhnVertex σ (j a)) := by
  classical
  set J : Fin n → Finset (Fin (k + 1)) := fun l =>
    Finset.univ.filter fun a => (σ.symm l : ℕ) < (j a : ℕ)
  have hx := apply_latticePoint_add_sum m σ j μ
  refine ⟨fun l z => ?_, fun l l' z => ?_⟩
  · rw [hx l]
    exact sep_aux hθ0 hθ (m l) (sum_subset_cases hθ0 hμ hμ1 _) (Or.inl rfl) z
  · rw [hx l, hx l']
    rcases le_total (σ.symm l : ℕ) (σ.symm l') with hle | hle
    · have hsub : J l' ⊆ J l := fun a ha => by
        simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢; omega
      have hs := Finset.sum_sdiff (f := μ) hsub
      refine sep_aux hθ0 hθ (m l - m l') (sum_subset_cases hθ0 hμ hμ1 (J l \ J l'))
        (Or.inl ?_) z
      push_cast
      change (m l : ℝ) + ∑ a ∈ J l, μ a - ((m l' : ℝ) + ∑ a ∈ J l', μ a) = _
      linarith
    · have hsub : J l ⊆ J l' := fun a ha => by
        simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢; omega
      have hs := Finset.sum_sdiff (f := μ) hsub
      refine sep_aux hθ0 hθ (m l - m l') (sum_subset_cases hθ0 hμ hμ1 (J l' \ J l))
        (Or.inr ?_) z
      push_cast
      change (m l : ℝ) + ∑ a ∈ J l, μ a - ((m l' : ℝ) + ∑ a ∈ J l', μ a) = _
      linarith

/-- **A separated point near a Freudenthal simplex lies in it.** -/
theorem mem_freudenthalSet_of_isSep {θ : ℝ} {x y : Fin n → ℝ} (hx : IsSep θ x)
    {m : Fin n → ℤ} {σ : Equiv.Perm (Fin n)} (hy : y ∈ freudenthalSet m σ)
    (hxy : ∀ l, |x l - y l| < θ / 2) : x ∈ freudenthalSet m σ := by
  obtain ⟨h01, hanti⟩ := hy
  have key : ∀ (q qy : ℝ), (q = 0 ∨ θ ≤ |q|) → 0 ≤ qy → |q - qy| < θ → 0 ≤ q := by
    intro q qy hq hqy hd
    rcases hq with rfl | hq
    · exact le_rfl
    · by_contra hneg; push Not at hneg
      rw [abs_of_neg hneg] at hq
      rw [abs_lt] at hd
      linarith
  refine ⟨fun i => ⟨?_, ?_⟩, fun a b hab => ?_⟩
  · have h := (h01 i).1
    simp only [Pi.sub_apply, latticePoint_apply] at h ⊢
    refine key _ _ ((hx.1 i (m i)).imp (by intro e; rw [e]; ring) id) h ?_
    have := hxy i
    rw [show x i - m i - (y i - m i) = x i - y i by ring]
    linarith [abs_nonneg (x i - y i)]
  · have h := (h01 i).2
    simp only [Pi.sub_apply, latticePoint_apply] at h ⊢
    have h' := key ((m i + 1 : ℤ) - x i) (1 - (y i - m i)) ?_ (by linarith) ?_
    · push_cast at h'; linarith
    · rcases hx.1 i (m i + 1) with e | e
      · left; rw [e]; ring
      · right; rwa [abs_sub_comm]
    · rw [show ((m i + 1 : ℤ) : ℝ) - x i - (1 - (y i - m i)) = -(x i - y i) by push_cast; ring,
        abs_neg]
      linarith [hxy i, abs_nonneg (x i - y i)]
  · have h := hanti hab
    simp only [Function.comp_apply, Pi.sub_apply, latticePoint_apply] at h ⊢
    have h' := key (x (σ a) - x (σ b) - ((m (σ a) - m (σ b) : ℤ) : ℝ))
      (y (σ a) - m (σ a) - (y (σ b) - m (σ b))) ?_ (by linarith) ?_
    · push_cast at h'; linarith
    · rcases hx.2 (σ a) (σ b) (m (σ a) - m (σ b)) with e | e
      · left; rw [e]; ring
      · right; exact e
    · have h1 := hxy (σ a)
      have h2 := hxy (σ b)
      rw [abs_lt] at h1 h2 ⊢
      push_cast
      constructor <;> linarith


/-! ### The simplices of the Freudenthal meshes of the cube -/

/-- The scale `h_N = 1 / (2 (N + 1))` of the level-`(N + 1)` Freudenthal mesh. -/
def hN (N : ℕ) : ℝ := 1 / 2 / ((N + 1 : ℕ) : ℝ)

theorem hN_pos (N : ℕ) : 0 < hN N := by unfold hN; positivity

theorem hN_le (N : ℕ) : hN N ≤ 1 / 2 := by
  unfold hN
  rw [div_le_iff₀ (by positivity)]
  have : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
  nlinarith

theorem hN_eq_meshSize (N : ℕ) : hN N = meshSize N := by
  unfold hN meshSize; push_cast; rfl

theorem hN_ne_zero (N : ℕ) : hN N ≠ 0 := (hN_pos N).ne'

/-- The simplex `h_N (m + K_σ)` of the level-`(N + 1)` Freudenthal mesh of the cube. -/
def cubeSimplex (N : ℕ) (m : Fin n → Fin (N + 1)) (σ : Equiv.Perm (Fin n)) :
    Affine.Simplex ℝ (Fin n → ℝ) n :=
  mapEquiv (boxMap 0 (hN N) (hN_ne_zero N)) (freudenthalSimplex (finLattice m) σ)

theorem mem_mesh_simplices {N : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n} :
    T ∈ (mesh n N).simplices ↔ ∃ m σ, cubeSimplex N m σ = T :=
  mem_freudenthalMesh_simplices

theorem cubeSimplex_mem (N : ℕ) (m : Fin n → Fin (N + 1)) (σ : Equiv.Perm (Fin n)) :
    cubeSimplex N m σ ∈ (mesh n N).simplices :=
  mem_mesh_simplices.2 ⟨m, σ, rfl⟩

theorem cubeSimplex_points (N : ℕ) (m : Fin n → Fin (N + 1)) (σ : Equiv.Perm (Fin n))
    (j : Fin (n + 1)) :
    (cubeSimplex N m σ).points j = hN N • (latticePoint (finLattice m) + kuhnVertex σ j) := by
  simp [cubeSimplex]

/-- `h_N (m + K_σ) = t + h_N K_σ`, `t = h_N m`. -/
theorem cubeSimplex_eq (N : ℕ) (m : Fin n → Fin (N + 1)) (σ : Equiv.Perm (Fin n)) :
    cubeSimplex N m σ = mapEquiv (boxMap (hN N • latticePoint (finLattice m)) (hN N)
      (hN_ne_zero N)) (kuhnSimplex σ) := by
  refine Affine.Simplex.ext fun j => ?_
  rw [cubeSimplex_points, mapEquiv_points, boxMap_apply, kuhnSimplex_points, smul_add]

theorem mem_closedInterior_cubeSimplex {N : ℕ} {m : Fin n → Fin (N + 1)}
    {σ : Equiv.Perm (Fin n)} {x : Fin n → ℝ} :
    x ∈ (cubeSimplex N m σ).closedInterior ↔
      (hN N)⁻¹ • x ∈ freudenthalSet (finLattice m) σ := by
  rw [cubeSimplex, closedInterior_freudenthalMesh_simplex]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [smul_smul, hN_ne_zero N] using hw
  · intro hx
    exact ⟨(hN N)⁻¹ • x, hx, by simp [smul_smul, hN_ne_zero N]⟩

/-- The simplices have sup-norm diameter `≤ h_N`. -/
theorem norm_sub_le_of_mem_cubeSimplex {N : ℕ} {m : Fin n → Fin (N + 1)}
    {σ : Equiv.Perm (Fin n)} {x y : Fin n → ℝ} (hx : x ∈ (cubeSimplex N m σ).closedInterior)
    (hy : y ∈ (cubeSimplex N m σ).closedInterior) : ‖x - y‖ ≤ hN N := by
  rw [mem_closedInterior_cubeSimplex] at hx hy
  have h := hN_pos N
  have key : ‖(hN N)⁻¹ • x - (hN N)⁻¹ • y‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    have h1 := hx.1 i
    have h2 := hy.1 i
    simp only [Pi.sub_apply, latticePoint_apply] at h1 h2
    rw [Real.norm_eq_abs, Pi.sub_apply, abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 h.le)] at key
  rwa [inv_mul_le_iff₀ h, mul_one] at key

/-- **Faces through nearby points.** Let `x = Σₐ λₐ qₐ` be a point of a `k`-face `g` of a mesh
simplex `T`, with all barycentric weights `λₐ ≥ θ`, `0 < θ ≤ ½`. Every mesh simplex `T'` containing
a point at sup-distance `< θ h_N / 2` from `x` has `g` among its faces. -/
theorem subset_vertexSet_of_near {N : ℕ} {T T' : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) (hT' : T' ∈ (mesh n N).simplices) {k : ℕ}
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T) (hg : g.card = k + 1) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) {μ : Fin (k + 1) → ℝ} (hμ : ∀ a, θ ≤ μ a)
    (hμ1 : ∑ a, μ a = 1) {t : Fin n → ℝ} (ht : t ∈ T'.closedInterior)
    (hxt : ‖∑ a, μ a • faceEnum g (k + 1) a - t‖ < θ * hN N / 2) : g ⊆ vertexSet T' := by
  classical
  set q := faceEnum g (k + 1)
  have hq := injective_faceEnum hg
  have hqT : ∀ a, q a ∈ vertexSet T := fun a => hgT (by
    have : q a ∈ Set.range q := ⟨a, rfl⟩
    rwa [range_faceEnum hg] at this)
  obtain ⟨m, σ, rfl⟩ := mem_mesh_simplices.1 hT
  obtain ⟨m', σ', rfl⟩ := mem_mesh_simplices.1 hT'
  have hj : ∀ a, ∃ j, q a = hN N • (latticePoint (finLattice m) + kuhnVertex σ j) := fun a => by
    obtain ⟨j, hj⟩ := mem_vertexSet.1 (hqT a)
    exact ⟨j, by rw [← hj, cubeSimplex_points]⟩
  choose j hj using hj
  set x := ∑ a, μ a • q a
  have hxs : (hN N)⁻¹ • x = latticePoint (finLattice m) + ∑ a, μ a • kuhnVertex σ (j a) := by
    have hh := hN_ne_zero N
    simp only [x, hj, Finset.smul_sum, smul_smul, smul_add, Finset.sum_add_distrib,
      ← Finset.sum_smul]
    have e1 : (hN N)⁻¹ * ∑ i, μ i * hN N = 1 := by
      rw [← Finset.sum_mul, hμ1]; field_simp
    have e2 : ∀ a, (hN N)⁻¹ * (μ a * hN N) = μ a := fun a => by field_simp
    simp only [e1, e2, one_smul]
  have hsep := isSep_latticePoint_add_sum hθ0.le hθ (finLattice m) σ j hμ hμ1
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
  have : v ∈ Set.range q := by rw [range_faceEnum hg]; exact hv
  obtain ⟨a, rfl⟩ := this
  exact SimplicialMesh.subset_vertexSet_of_mem hT hT' hq hqT
    (fun a => hθ0.trans_le (hμ a)) hμ1 hx' a


/-! ### Bounded overlap -/

theorem card_filter_Icc_le (N : ℕ) (c : ℝ) :
    ((Finset.univ : Finset (Fin (N + 1))).filter fun j : Fin (N + 1) => c ≤ ((j : ℕ) : ℝ) ∧
      ((j : ℕ) : ℝ) ≤ c + 5).card ≤ 6 := by
  classical
  set f : Fin (N + 1) → ℕ := fun j => (((j : ℕ) : ℤ) - ⌈c⌉).toNat
  have hmaps : ∀ j ∈ (Finset.univ : Finset (Fin (N + 1))).filter (fun j : Fin (N + 1) => c ≤ ((j : ℕ) : ℝ) ∧
      ((j : ℕ) : ℝ) ≤ c + 5), f j ∈ Finset.range 6 := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have h1 : ((j : ℕ) : ℤ) ≤ ⌈c⌉ + 5 := by
      have : ((j : ℕ) : ℝ) ≤ ⌈c⌉ + 5 := hj.2.trans (by linarith [Int.le_ceil c])
      exact_mod_cast this
    simp only [Finset.mem_range, f]
    omega
  have hinj : Set.InjOn f ((Finset.univ : Finset (Fin (N + 1))).filter fun j : Fin (N + 1) =>
      c ≤ ((j : ℕ) : ℝ) ∧ ((j : ℕ) : ℝ) ≤ c + 5) := by
    intro j hj j' hj' e
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hj hj'
    have h1 : ⌈c⌉ ≤ ((j : ℕ) : ℤ) := Int.ceil_le.2 (by exact_mod_cast hj.1)
    have h2 : ⌈c⌉ ≤ ((j' : ℕ) : ℤ) := Int.ceil_le.2 (by exact_mod_cast hj'.1)
    simp only [f] at e
    apply Fin.ext
    omega
  have := Finset.card_le_card_of_injOn f hmaps hinj
  simpa using this

open Classical in
/-- **Bounded overlap**: a point lies in the `2 h_N`-neighbourhoods of at most `6ⁿ n!` simplices
of the level-`(N + 1)` mesh. -/
theorem card_filter_mem_cthickening_le (N : ℕ) (t : Fin n → ℝ) :
    ((mesh n N).simplices.filter fun T : Affine.Simplex ℝ (Fin n → ℝ) n =>
      t ∈ Metric.cthickening (2 * hN N) T.closedInterior).card ≤ 6 ^ n * n.factorial := by
  set h := hN N
  have hh := hN_pos N
  set A : Fin n → Finset (Fin (N + 1)) := fun i => Finset.univ.filter fun j : Fin (N + 1) =>
    t i / h - 3 ≤ ((j : ℕ) : ℝ) ∧ ((j : ℕ) : ℝ) ≤ t i / h - 3 + 5
  set S := Fintype.piFinset A ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin n)))
  have hsub : (mesh n N).simplices.filter (fun T : Affine.Simplex ℝ (Fin n → ℝ) n =>
      t ∈ Metric.cthickening (2 * h) T.closedInterior) ⊆
      S.image fun p => cubeSimplex N p.1 p.2 := by
    intro T hT
    rw [Finset.mem_filter] at hT
    obtain ⟨m, σ, rfl⟩ := mem_mesh_simplices.1 hT.1
    have hc := hT.2
    rw [Metric.cthickening_eq_biUnion_closedBall _ (by positivity),
      (cubeSimplex N m σ).isClosed_closedInterior.closure_eq, Set.mem_iUnion₂] at hc
    obtain ⟨y, hy, hty⟩ := hc
    refine Finset.mem_image.2 ⟨(m, σ), Finset.mem_product.2 ⟨Fintype.mem_piFinset.2 fun i => ?_,
      Finset.mem_univ _⟩, rfl⟩
    rw [mem_closedInterior_cubeSimplex] at hy
    have h01 := hy.1 i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, latticePoint_apply, finLattice] at h01
    have hdist : |t i - y i| ≤ 2 * h := by
      have := norm_le_pi_norm (t - y) i
      rw [Real.norm_eq_abs, Pi.sub_apply] at this
      exact this.trans (by rw [← dist_eq_norm]; exact hty)
    rw [abs_le] at hdist
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    have e : h⁻¹ * y i = y i / h := by rw [inv_mul_eq_div]
    rw [e] at h01
    have hy1 : (y i - 2 * h) / h ≤ t i / h := div_le_div_of_nonneg_right (by linarith) hh.le
    have hy2 : t i / h ≤ (y i + 2 * h) / h := div_le_div_of_nonneg_right (by linarith) hh.le
    rw [sub_div, mul_div_assoc, div_self hh.ne', mul_one] at hy1
    rw [add_div, mul_div_assoc, div_self hh.ne', mul_one] at hy2
    push_cast at h01
    constructor <;> linarith [h01.1, h01.2]
  calc _ ≤ (S.image fun p => cubeSimplex N p.1 p.2).card := Finset.card_le_card hsub
    _ ≤ S.card := Finset.card_image_le
    _ = (∏ i, (A i).card) * n.factorial := by
        rw [Finset.card_product, Fintype.card_piFinset, Finset.card_univ, Fintype.card_perm,
          Fintype.card_fin]
    _ ≤ (∏ _i : Fin n, 6) * n.factorial := by
        gcongr with i
        exact card_filter_Icc_le N _
    _ = 6 ^ n * n.factorial := by simp


/-- **Bounded overlap of the neighbourhoods**, integrated. -/
theorem sum_integral_cthickening_le (N : ℕ) {f : (Fin n → ℝ) → ℝ} (hf : Integrable f)
    (hf0 : ∀ x, 0 ≤ f x) :
    ∑ T ∈ (mesh n N).simplices, ∫ x in Metric.cthickening (2 * hN N) T.closedInterior, f x ≤
      (6 ^ n * n.factorial : ℕ) * ∫ x, f x := by
  classical
  have hmeas : ∀ T : Affine.Simplex ℝ (Fin n → ℝ) n,
      MeasurableSet (Metric.cthickening (2 * hN N) T.closedInterior) := fun T =>
    Metric.isClosed_cthickening.measurableSet
  have hint : ∀ T ∈ (mesh n N).simplices, Integrable
      ((Metric.cthickening (2 * hN N) T.closedInterior).indicator f) :=
    fun T _ => hf.indicator (hmeas T)
  calc ∑ T ∈ (mesh n N).simplices, ∫ x in Metric.cthickening (2 * hN N) T.closedInterior, f x
      = ∫ x, ∑ T ∈ (mesh n N).simplices,
          (Metric.cthickening (2 * hN N) T.closedInterior).indicator f x := by
        rw [integral_finsetSum _ hint]
        exact Finset.sum_congr rfl fun T _ => (integral_indicator (hmeas T)).symm
    _ ≤ ∫ x, ((6 ^ n * n.factorial : ℕ) : ℝ) * f x := by
        refine integral_mono (integrable_finsetSum _ hint) (hf.const_mul _) fun x => ?_
        simp only [Set.indicator_apply]
        rw [← Finset.sum_filter]
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_mem_cthickening_le N x)
          (hf0 x)
    _ = _ := integral_const_mul _ _

/-! ### The smoother at a point -/

section Smoother

variable (φ : ContDiffBump (0 : Fin n → ℝ))

theorem isTest_normed_comp_sub (y : Fin n → ℝ) :
    IsTest (univ : Set (Fin n → ℝ)) fun t => φ.normed volume (y - t) :=
  IsTest.comp_sub ⟨φ.contDiff_normed, φ.hasCompactSupport_normed, subset_univ _⟩ y

theorem integral_normed_comp_sub (y : Fin n → ℝ) : ∫ t, φ.normed volume (y - t) = 1 := by
  rw [integral_sub_left_eq_self (fun t => φ.normed volume t) volume y, φ.integral_normed]

/-- **Jensen's inequality for the mollifier**: `(∫ f ρ(y - ·))² ≤ ∫ f² ρ(y - ·)`. -/
theorem sq_integral_mul_normed_le {f : (Fin n → ℝ) → ℝ} (hf : LocallyIntegrable f volume)
    (hf2 : LocallyIntegrable (fun t => f t ^ 2) volume) (y : Fin n → ℝ) :
    (∫ t, f t * φ.normed volume (y - t)) ^ 2 ≤ ∫ t, f t ^ 2 * φ.normed volume (y - t) := by
  set g : (Fin n → ℝ) → ℝ := fun t => φ.normed volume (y - t)
  have hg := isTest_normed_comp_sub φ y
  have h1 : Integrable fun t => f t * g t := integrable_mul_isTest hf hg
  have h2 : Integrable fun t => f t ^ 2 * g t := integrable_mul_isTest hf2 hg
  have h0 : Integrable g := hg.continuous.integrable_of_hasCompactSupport hg.hasCompactSupport
  set a := ∫ t, f t * g t
  have hpos : 0 ≤ ∫ t, (f t - a) ^ 2 * g t :=
    integral_nonneg fun t => mul_nonneg (sq_nonneg _) (φ.nonneg_normed _)
  have e : (fun t => (f t - a) ^ 2 * g t) =
      fun t => f t ^ 2 * g t - (2 * a) * (f t * g t) + a ^ 2 * g t := by
    funext t; ring
  have hA : Integrable fun t => f t ^ 2 * g t - (2 * a) * (f t * g t) :=
    h2.sub (h1.const_mul _)
  have hB : Integrable fun t => a ^ 2 * g t := h0.const_mul _
  have e2 : ∫ t, (f t ^ 2 * g t - (2 * a) * (f t * g t) + a ^ 2 * g t) =
      (∫ t, f t ^ 2 * g t) - (2 * a) * a + a ^ 2 * 1 := by
    rw [integral_add hA hB, integral_sub h2 (h1.const_mul _), integral_const_mul,
      integral_const_mul, integral_normed_comp_sub φ y]
  rw [e, e2] at hpos
  change a ^ 2 ≤ ∫ t, f t ^ 2 * g t
  nlinarith

/-- The mollified square is controlled by the mass on the ball of radius `rOut`:
`∫ f² ρ(y - ·) ≤ |B(0, rIn)|⁻¹ ∫_{B̄(y, rOut)} f²`. -/
theorem integral_sq_mul_normed_le {f : (Fin n → ℝ) → ℝ}
    (hf2 : Integrable (fun t => f t ^ 2) volume) (y : Fin n → ℝ) :
    ∫ t, f t ^ 2 * φ.normed volume (y - t) ≤
      1 / volume.real (Metric.closedBall (0 : Fin n → ℝ) φ.rIn) *
        ∫ t in Metric.closedBall y φ.rOut, f t ^ 2 := by
  set Mρ := 1 / volume.real (Metric.closedBall (0 : Fin n → ℝ) φ.rIn)
  have hg := isTest_normed_comp_sub φ y
  rw [← integral_const_mul, ← integral_indicator Metric.isClosed_closedBall.measurableSet]
  refine integral_mono (integrable_mul_isTest hf2.locallyIntegrable hg)
    ((hf2.const_mul Mρ).indicator Metric.isClosed_closedBall.measurableSet) fun t => ?_
  simp only
  by_cases ht : t ∈ Metric.closedBall y φ.rOut
  · rw [Set.indicator_of_mem ht, mul_comm Mρ]
    exact mul_le_mul_of_nonneg_left (φ.normed_le_div_measure_closedBall_rIn volume _)
      (sq_nonneg _)
  · rw [Set.indicator_of_notMem ht]
    have : φ.normed volume (y - t) = 0 := by
      rw [← Function.notMem_support, φ.support_normed_eq, Metric.mem_ball, dist_zero_right,
        ← dist_eq_norm, dist_comm]
      exact fun h => ht (Metric.mem_closedBall.2 h.le)
    rw [this, mul_zero]

theorem normed_eq_zero_of_le {y t : Fin n → ℝ} (h : φ.rOut ≤ dist t y) :
    φ.normed volume (y - t) = 0 := by
  rw [← Function.notMem_support, φ.support_normed_eq, Metric.mem_ball, dist_zero_right,
    ← dist_eq_norm, dist_comm]
  exact not_lt.2 h

end Smoother


/-! ### Face integrals on the mesh simplices -/

theorem vertexSet_subset_closedInterior (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    (vertexSet T : Set (Fin n → ℝ)) ⊆ T.closedInterior := by
  rw [← convexHull_vertexSet]; exact subset_convexHull ℝ _

theorem simplexMap_faceEnum_mem {T : Affine.Simplex ℝ (Fin n → ℝ) n} {k : ℕ}
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T) (hg : g.card = k + 1) {x : Fin k → ℝ}
    (hx : x ∈ FiniteElement.refSimplex k) : simplexMap (faceEnum g (k + 1)) x ∈ T.closedInterior := by
  rw [← convexHull_vertexSet]
  refine convexHull_mono ?_ (simplexMap_mem_convexHull _ hx)
  rw [range_faceEnum hg]; exact Finset.coe_subset.2 hgT

/-- The minors of a face of a mesh simplex are `O(h_Nᵏ)`. -/
theorem sum_abs_minor_face_le {N : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) {k : ℕ} {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T)
    (hg : g.card = k + 1) :
    ∑ s, |wedgeProd (simplexMatrix (faceEnum g (k + 1))) s univ| ≤
      2 ^ n * (k.factorial * hN N ^ k) := by
  obtain ⟨m, σ, rfl⟩ := mem_mesh_simplices.1 hT
  refine sum_abs_wedgeProd_simplexMatrix_le (hN_pos N).le fun i l => ?_
  have hmem : ∀ a, faceEnum g (k + 1) a ∈ (cubeSimplex N m σ).closedInterior := fun a =>
    vertexSet_subset_closedInterior _ (hgT (by
      have : faceEnum g (k + 1) a ∈ Set.range (faceEnum g (k + 1)) := ⟨a, rfl⟩
      rwa [range_faceEnum hg] at this))
  have := norm_sub_le_of_mem_cubeSimplex (hmem l.succ) (hmem 0)
  refine le_trans ?_ this
  have h := norm_le_pi_norm (faceEnum g (k + 1) l.succ - faceEnum g (k + 1) 0) i
  rwa [Real.norm_eq_abs, Pi.sub_apply] at h

/-- **Face integrals on the mesh**: `|∫_g ω| ≤ 2ⁿ h_Nᵏ sup_T |ω|`. -/
theorem abs_simplexIntegral_face_le {N : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) {k : ℕ} {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T)
    (hg : g.card = k + 1) {ω : FormField n} {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ x ∈ T.closedInterior, ∀ s, |ω x s| ≤ A) :
    |simplexIntegral (faceEnum g (k + 1)) ω| ≤ 2 ^ n * hN N ^ k * A := by
  have h := abs_simplexIntegral_le (p := faceEnum g (k + 1)) (ω := ω) (M := A)
    fun x hx s => hA _ (simplexMap_faceEnum_mem hgT hg hx) s
  have hm := sum_abs_minor_face_le hT hgT hg
  have hk : (0 : ℝ) < k.factorial := by positivity
  refine h.trans ?_
  rw [div_le_iff₀ hk]
  calc (∑ s, |wedgeProd (simplexMatrix (faceEnum g (k + 1))) s univ|) * A
      ≤ 2 ^ n * (k.factorial * hN N ^ k) * A := mul_le_mul_of_nonneg_right hm hA0
    _ = _ := by ring


/-! ### The cube and the smoothing parameters -/

theorem closure_cubeDomain :
    closure (cubeDomain n) = Set.univ.pi fun _ => Set.Icc (0 : ℝ) (1 / 2) := by
  rw [cubeDomain, closure_pi_set]
  simp

theorem norm_sub_center_le {x : Fin n → ℝ} (hx : x ∈ closure (cubeDomain n)) :
    ‖x - center n‖ ≤ 1 / 4 := by
  rw [closure_cubeDomain] at hx
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
  have := hx i (Set.mem_univ i)
  rw [Real.norm_eq_abs, Pi.sub_apply, center, abs_le]
  constructor <;> linarith [this.1, this.2]

/-- **The smoothing parameters** of the maximal family on the level-`(N + 1)` mesh: dilation
factor `1 - γ h_N` about the centre, bump radii `γ h_N / 64 < γ h_N / 32`. -/
def pMax (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) : SmoothingParam (Fin n → ℝ) where
  center := center n
  factor := 1 - γ * hN N
  half_le_factor := by
    have h1 := hN_le N
    have h0 := hN_pos N
    nlinarith
  bump := ⟨γ * hN N / 64, γ * hN N / 32, by have := hN_pos N; positivity,
    by have := hN_pos N; nlinarith⟩

variable {γ : ℝ} {hγ : 0 < γ} {hγ1 : γ ≤ 1}

theorem pMax_isMaximal (N : ℕ) : (pMax (n := n) γ hγ hγ1 N).IsMaximal (center n) (1 / 4) where
  center_eq := rfl
  factor_lt_one := by
    change 1 - γ * hN N < 1
    have := hN_pos N; nlinarith
  rOut_lt := by
    change γ * hN N / 32 < 1 / 4 * (1 - (1 - γ * hN N)) / 4
    have := hN_pos N; nlinarith

/-- **The smoothing parameters** of the minimal family on the level-`(N + 1)` mesh: dilation
factor `1 + γ h_N` towards the centre, bump radii `γ h_N / 64 < γ h_N / 32`. -/
def pMin (γ : ℝ) (hγ : 0 < γ) (N : ℕ) : SmoothingParam (Fin n → ℝ) where
  center := center n
  factor := 1 + γ * hN N
  half_le_factor := by
    have h0 := hN_pos N
    nlinarith
  bump := ⟨γ * hN N / 64, γ * hN N / 32, by have := hN_pos N; positivity,
    by have := hN_pos N; nlinarith⟩

theorem pMin_isMinimal (N : ℕ) : (pMin (n := n) γ hγ N).IsMinimal (center n) (1 / 4) where
  center_eq := rfl
  one_lt_factor := by
    change 1 < 1 + γ * hN N
    have := hN_pos N; nlinarith
  rOut_lt := by
    change γ * hN N / 32 < 1 / 4 * (1 + γ * hN N - 1) / 2
    have := hN_pos N; nlinarith

/-- **Admissible smoothing parameters** at scale `γ` on the level-`(N + 1)` mesh: centre of the
cube, `|c - 1| = γ h_N`, bump radii `γ h_N / 64 < γ h_N / 32` (both families). -/
structure IsAdm (γ : ℝ) (N : ℕ) (p : SmoothingParam (Fin n → ℝ)) : Prop where
  center_eq : p.center = center n
  abs_factor_sub_one : |p.factor - 1| = γ * hN N
  rIn_eq : p.bump.rIn = γ * hN N / 64
  rOut_eq : p.bump.rOut = γ * hN N / 32

theorem pMax_isAdm (N : ℕ) : IsAdm γ N (pMax (n := n) γ hγ hγ1 N) where
  center_eq := rfl
  abs_factor_sub_one := by
    change |1 - γ * hN N - 1| = _
    rw [sub_sub_cancel_left, abs_neg, abs_of_pos (mul_pos hγ (hN_pos N))]
  rIn_eq := rfl
  rOut_eq := rfl

theorem pMin_isAdm (N : ℕ) : IsAdm γ N (pMin (n := n) γ hγ N) where
  center_eq := rfl
  abs_factor_sub_one := by
    change |1 + γ * hN N - 1| = _
    rw [add_sub_cancel_left, abs_of_pos (mul_pos hγ (hN_pos N))]
  rIn_eq := rfl
  rOut_eq := rfl

namespace IsAdm

variable {N : ℕ} {p : SmoothingParam (Fin n → ℝ)}

theorem gamma_h_nonneg (hp : IsAdm γ N p) : 0 ≤ γ * hN N :=
  hp.abs_factor_sub_one ▸ abs_nonneg _

theorem gamma_nonneg (hp : IsAdm γ N p) : 0 ≤ γ :=
  nonneg_of_mul_nonneg_left hp.gamma_h_nonneg (hN_pos N)

theorem gamma_h_le (hp : IsAdm γ N p) (hγ1 : γ ≤ 1) : γ * hN N ≤ 1 / 2 := by
  have h1 := hN_le N
  have h0 := hN_pos N
  have := hp.gamma_nonneg
  nlinarith

theorem factor_le_two (hp : IsAdm γ N p) (hγ1 : γ ≤ 1) : p.factor ≤ 2 := by
  have h := hp.abs_factor_sub_one
  have := le_abs_self (p.factor - 1)
  have := hp.gamma_h_le hγ1
  linarith

theorem pow_factor_le (hp : IsAdm γ N p) (hγ1 : γ ≤ 1) (k : ℕ) : p.factor ^ k ≤ 2 ^ k :=
  pow_le_pow_left₀ p.factor_pos.le (hp.factor_le_two hγ1) k

/-- `|1 - cᵏ| ≤ k 2ᵏ γ h_N`. -/
theorem abs_one_sub_pow_le (hp : IsAdm γ N p) (hγ1 : γ ≤ 1) (k : ℕ) :
    |1 - p.factor ^ k| ≤ k * 2 ^ k * (γ * hN N) := by
  have hg : p.factor ^ k - 1 = (∑ i ∈ Finset.range k, p.factor ^ i) * (p.factor - 1) :=
    (geom_sum_mul p.factor k).symm
  rw [abs_sub_comm, hg, abs_mul, hp.abs_factor_sub_one]
  refine mul_le_mul_of_nonneg_right ?_ hp.gamma_h_nonneg
  rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => pow_nonneg p.factor_pos.le i)]
  calc ∑ i ∈ Finset.range k, p.factor ^ i ≤ ∑ _i ∈ Finset.range k, (2 : ℝ) ^ k :=
        Finset.sum_le_sum fun i hi => (hp.pow_factor_le hγ1 i).trans
          (pow_le_pow_right₀ (by norm_num) (Finset.mem_range.1 hi).le)
    _ = k * 2 ^ k := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The dilated point is within `γ h_N / 4` of the original point on `cl Q`. -/
theorem norm_dil_sub_le (hp : IsAdm γ N p) {x : Fin n → ℝ} (hx : x ∈ closure (cubeDomain n)) :
    ‖(p.center + p.factor • (x - p.center)) - x‖ ≤ γ * hN N / 4 := by
  rw [hp.center_eq]
  have e : center n + p.factor • (x - center n) - x = (p.factor - 1) • (x - center n) := by
    rw [sub_smul, one_smul]; abel
  rw [e, norm_smul, Real.norm_eq_abs, hp.abs_factor_sub_one]
  have := norm_sub_center_le hx
  have h0 := hp.gamma_h_nonneg
  nlinarith

theorem gamma_pos (hp : IsAdm γ N p) : 0 < γ := by
  rcases hp.gamma_nonneg.lt_or_eq with h' | h'
  · exact h'
  · exfalso
    have hr := p.bump.rIn_pos
    rw [hp.rIn_eq, ← h', zero_mul, zero_div] at hr
    exact lt_irrefl _ hr

end IsAdm

/-! ### The smoothed form at a point -/

theorem smoothForm_apply_eq {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (p : SmoothingParam (Fin n → ℝ)) (k : ℕ) (x : L2F ℝ Ω (formIdx n k)) (y : Fin n → ℝ)
    (s : formIdx n k) :
    (smoothForm p hΩ k x : FormField n) y s.1 = p.factor ^ k *
      ∫ t, Ω.indicator ((x s : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) t *
        p.bump.normed volume (p.center + p.factor • (y - p.center) - t) := by
  rw [smoothForm_apply, formExt_val, smoothCoeff, smoothExt, dil, molli_apply, zpow_natCast]

/-- **Pointwise bound of the smoothed form**:
`|R x (y)ₛ|² ≤ c^{2k} |B(0, rIn)|⁻¹ Σ_{s'} ∫_{B̄(ŷ, rOut)} |x̄_{s'}|²`, `ŷ` the dilated point. -/
theorem abs_smoothForm_le {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (p : SmoothingParam (Fin n → ℝ)) (k : ℕ) (x : L2F ℝ Ω (formIdx n k))
    (y : Fin n → ℝ) (s : Finset (Fin n)) :
    |(smoothForm p hΩ k x : FormField n) y s| ≤ p.factor ^ k *
      √(1 / volume.real (Metric.closedBall (0 : Fin n → ℝ) p.bump.rIn) *
        ∑ s' : formIdx n k, ∫ t in Metric.closedBall (p.center + p.factor • (y - p.center))
          p.bump.rOut, (Ω.indicator ((x s' : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) t) ^ 2) := by
  set Mρ := 1 / volume.real (Metric.closedBall (0 : Fin n → ℝ) p.bump.rIn)
  have hMρ : 0 ≤ Mρ := by positivity
  set ŷ := p.center + p.factor • (y - p.center)
  have hterm : ∀ s' : formIdx n k, 0 ≤ ∫ t in Metric.closedBall ŷ p.bump.rOut,
      (Ω.indicator ((x s' : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) t) ^ 2 := fun s' =>
    setIntegral_nonneg Metric.isClosed_closedBall.measurableSet fun t _ => sq_nonneg _
  by_cases hs : #s = k
  · have hs' : ((#s : ℕ) : ℤ) = (k : ℤ) := by rw [hs]
    have e := smoothForm_apply_eq hΩ p k x y ⟨s, hs'⟩
    simp only at e
    rw [e]
    set f := Ω.indicator ((x ⟨s, hs'⟩ : L2 ℝ Ω) : (Fin n → ℝ) → ℝ)
    have hmem : MemLp f 2 volume := memLp_indicator hΩ _
    have hf : LocallyIntegrable f volume := hmem.locallyIntegrable (by norm_num)
    have hf2 : Integrable (fun t => f t ^ 2) volume := hmem.integrable_sq
    rw [abs_mul, abs_of_pos (pow_pos p.factor_pos k)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg p.factor_pos.le k)
    rw [← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    refine (sq_integral_mul_normed_le p.bump hf hf2.locallyIntegrable ŷ).trans
      ((integral_sq_mul_normed_le p.bump hf2 ŷ).trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ hMρ
    exact Finset.single_le_sum (f := fun s' : formIdx n k => ∫ t in Metric.closedBall ŷ p.bump.rOut,
      (Ω.indicator ((x s' : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) t) ^ 2) (fun s' _ => hterm s')
      (Finset.mem_univ _)
  · rw [isDeg_smoothForm p hΩ k x y s hs, abs_zero]
    exact mul_nonneg (pow_nonneg p.factor_pos.le k) (Real.sqrt_nonneg _)


/-! ### Local estimates on the mesh simplices -/

theorem simplexIntegral_localDof {M : SimplicialMesh n} {k : ℕ} (T : M.simplices)
    {g : Finset (Fin n → ℝ)} (hg : g.card = k + 1) (z : (whitneyElement n).space T k) :
    (whitneyElement n).localDof T k g ⟨(), hg⟩ z =
      simplexIntegral (faceEnum g (k + 1)) (z : FormField n) := rfl

theorem simplexIntegral_globalInterp {M : SimplicialMesh n} (k : ℕ) (w : contForms n)
    (T : M.simplices) {g : Finset (Fin n → ℝ)}
    (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n)) (hg : g.card = k + 1) :
    simplexIntegral (faceEnum g (k + 1))
        ((((whitneyElement n).globalInterp M k w : (whitneyElement n).Piecewise M k) T :
          (whitneyElement n).space T k) : FormField n) =
      simplexIntegral (faceEnum g (k + 1)) (w : FormField n) := by
  have h := (whitneyElement n).localDof_globalInterp M k w T g hgT
    (⟨(), hg⟩ : WhitneyDofIdx g k)
  exact (simplexIntegral_localDof T hg _).symm.trans (h.trans rfl)

theorem mem_p1MinusForms_of_space {T : Affine.Simplex ℝ (Fin n → ℝ) n} {k : ℕ}
    (z : (whitneyElement n).space T k) : (z : FormField n) ∈ p1MinusForms n k := by
  have := z.2
  change (z : FormField n) ∈ whitneySpace T.points k at this
  rwa [whitneySpace_eq_p1MinusForms_of_isUnit (isUnit_det_edgeMatrix _)] at this

/-- The local DOF estimate with a uniform bound on the face integrals. -/
theorem exists_local_dof_bound_of_le (K : Affine.Simplex ℝ (Fin n → ℝ) n) (k : ℕ) :
    ∃ B, 0 ≤ B ∧ ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {z : FormField n},
      z ∈ p1MinusForms n k → ∀ {D : ℝ}, 0 ≤ D →
        (∀ g ⊆ vertexSet (mapEquiv (boxMap t h hh.ne') K), g.card = k + 1 →
          |simplexIntegral (faceEnum g (k + 1)) z| ≤ D) →
        ∀ x ∈ (mapEquiv (boxMap t h hh.ne') K).closedInterior, ∀ s,
          h ^ k * |z x s| ≤ B * D := by
  classical
  obtain ⟨B, hB0, hB⟩ := exists_local_dof_bound K k
  refine ⟨B * Fintype.card (Σ g : (vertexSet K).powerset,
    WhitneyDofIdx (g : Finset (Fin n → ℝ)) k), by positivity,
    fun {h} hh t z hz D hD0 hD x hx s => (hB hh t hz x hx s).trans ?_⟩
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hB0
  calc _ ≤ ∑ _p : Σ g : (vertexSet K).powerset, WhitneyDofIdx (g : Finset (Fin n → ℝ)) k, D := by
        refine Finset.sum_le_sum fun p _ => hD _ ?_ ?_
        · intro v hv
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hv
          have hyK := (Finset.mem_powerset.1 p.1.2) hy
          have : (fun y => t + h • y) y ∈ (vertexSet (mapEquiv (boxMap t h hh.ne') K) :
              Set (Fin n → ℝ)) := by
            rw [vertexSet_mapEquiv, coe_boxMap]; exact ⟨y, hyK, rfl⟩
          exact this
        · rw [Finset.card_image_of_injective _ (fun y y' e => by
            have : h • y = h • y' := by simpa using e
            exact smul_right_injective _ hh.ne' this), p.2.2]
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

theorem volume_real_kuhnSet_le (σ : Equiv.Perm (Fin n)) : volume.real (kuhnSet σ) ≤ 1 := by
  have h1 : volume (kuhnSet σ) ≤ volume (Set.Icc (0 : Fin n → ℝ) 1) :=
    measure_mono (kuhnSet_subset_Icc σ)
  rw [Real.volume_Icc_pi] at h1
  simp only [Pi.one_apply, Pi.zero_apply, sub_zero, ENNReal.ofReal_one,
    Finset.prod_const_one] at h1
  rw [Measure.real]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h1)

/-- `∫_T f ≤ h_Nⁿ sup_T f` for `0 ≤ f` on the mesh simplices. -/
theorem integral_cubeSimplex_le {N : ℕ} (m : Fin n → Fin (N + 1)) (σ : Equiv.Perm (Fin n))
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) {A : ℝ}
    (hA : ∀ x ∈ (cubeSimplex N m σ).closedInterior, f x ≤ A) (hf0 : ∀ x, 0 ≤ f x) :
    ∫ x in (cubeSimplex N m σ).closedInterior, f x ≤ hN N ^ n * A := by
  have hh := hN_pos N
  rw [cubeSimplex_eq, integral_closedInterior_mapEquiv_boxMap _ _ hh]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hh.le n)
  have hA0 : 0 ≤ A := by
    have := hA _ (vertexSet_subset_closedInterior _ (points_mem_vertexSet _ 0))
    exact (hf0 _).trans this
  calc ∫ y in (kuhnSimplex σ).closedInterior, f (hN N • latticePoint (finLattice m) + hN N • y)
      ≤ ∫ _y in (kuhnSimplex σ).closedInterior, A := by
        have hfin : volume (kuhnSimplex σ).closedInterior ≠ ⊤ :=
          (kuhnSimplex σ).isCompact_closedInterior.measure_lt_top.ne
        refine setIntegral_mono_on ?_ (integrableOn_const hfin)
          (kuhnSimplex σ).isClosed_closedInterior.measurableSet fun y hy => ?_
        · exact ((hf.comp (continuous_const.add (continuous_const_smul _))).continuousOn
            ).integrableOn_compact (kuhnSimplex σ).isCompact_closedInterior
        · refine hA _ ?_
          rw [cubeSimplex_eq, closedInterior_mapEquiv_boxMap]
          exact ⟨y, hy, rfl⟩
    _ = volume.real (kuhnSimplex σ).closedInterior * A := by
        rw [setIntegral_const, smul_eq_mul]
    _ ≤ 1 * A := by
        refine mul_le_mul_of_nonneg_right ?_ hA0
        rw [closedInterior_kuhnSimplex]; exact volume_real_kuhnSet_le σ
    _ = A := one_mul A


/-- The local DOF estimate on all the Kuhn simplices, with one constant. -/
def DofBound (n k : ℕ) (B : ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {z : FormField n},
    z ∈ p1MinusForms n k → ∀ {D : ℝ}, 0 ≤ D →
      (∀ g ⊆ vertexSet (mapEquiv (boxMap t h hh.ne') (kuhnSimplex σ)), g.card = k + 1 →
        |simplexIntegral (faceEnum g (k + 1)) z| ≤ D) →
      ∀ x ∈ (mapEquiv (boxMap t h hh.ne') (kuhnSimplex σ)).closedInterior, ∀ s,
        h ^ k * |z x s| ≤ B * D

theorem exists_dofBound (k : ℕ) : ∃ B, 0 ≤ B ∧ DofBound n k B := by
  choose B hB0 hB using fun σ : Equiv.Perm (Fin n) => exists_local_dof_bound_of_le (kuhnSimplex σ) k
  refine ⟨∑ σ, B σ, Finset.sum_nonneg fun σ _ => hB0 σ,
    fun σ h hh t z hz D hD0 hD x hx s => (hB σ hh t hz hD0 hD x hx s).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun σ _ => hB0 σ) (Finset.mem_univ σ))
    hD0

theorem DofBound.apply {k : ℕ} {B : ℝ} (hB : DofBound n k B) {N : ℕ}
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ (mesh n N).simplices) {z : FormField n}
    (hz : z ∈ p1MinusForms n k) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ g ⊆ vertexSet T, g.card = k + 1 → |simplexIntegral (faceEnum g (k + 1)) z| ≤ D)
    {x : Fin n → ℝ} (hx : x ∈ T.closedInterior) (s : Finset (Fin n)) :
    hN N ^ k * |z x s| ≤ B * D := by
  obtain ⟨m, σ, rfl⟩ := mem_mesh_simplices.1 hT
  rw [cubeSimplex_eq] at hD hx
  exact hB σ (hN_pos N) _ hz hD0 hD x hx s

theorem card_formIdx_le (k : ℤ) : (Fintype.card (formIdx n k) : ℝ) ≤ 2 ^ n := by
  have h := Fintype.card_subtype_le (fun s : Finset (Fin n) => (#s : ℤ) = k)
  rw [Fintype.card_finset, Fintype.card_fin] at h
  exact_mod_cast h

theorem volume_real_closedBall_zero {r : ℝ} (hr : 0 ≤ r) :
    volume.real (Metric.closedBall (0 : Fin n → ℝ) r) = (2 * r) ^ n := by
  rw [Measure.real, Real.volume_pi_closedBall _ hr, Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity)]


/-! ### The uniform `L²` bound -/

/-- The `L²` mass of `x` near `T`. -/
def locMass {N : ℕ} {k : ℤ} (x : L2F ℝ (mesh n N).domain (formIdx n k))
    (T : Affine.Simplex ℝ (Fin n → ℝ) n) : ℝ :=
  ∑ s : formIdx n k, ∫ t in Metric.cthickening (2 * hN N) T.closedInterior,
    ((mesh n N).domain.indicator ((x s : L2 ℝ (mesh n N).domain) : (Fin n → ℝ) → ℝ) t) ^ 2

theorem locMass_nonneg {N : ℕ} {k : ℤ} (x : L2F ℝ (mesh n N).domain (formIdx n k))
    (T : Affine.Simplex ℝ (Fin n → ℝ) n) : 0 ≤ locMass x T :=
  Finset.sum_nonneg fun _ _ => setIntegral_nonneg Metric.isClosed_cthickening.measurableSet
    fun _ _ => sq_nonneg _

theorem integrable_sq_indicator {N : ℕ} (f : L2 ℝ (mesh n N).domain) :
    Integrable fun t => ((mesh n N).domain.indicator (f : (Fin n → ℝ) → ℝ) t) ^ 2 :=
  (memLp_indicator (isOpen_mesh_domain n N).measurableSet f).integrable_sq

theorem integral_sq_indicator {N : ℕ} (f : L2 ℝ (mesh n N).domain) :
    ∫ t, ((mesh n N).domain.indicator (f : (Fin n → ℝ) → ℝ) t) ^ 2 = ‖f‖ ^ 2 := by
  rw [norm_sq_eq_integral_sq]
  have e : (fun t => ((mesh n N).domain.indicator (f : (Fin n → ℝ) → ℝ) t) ^ 2) =
      (mesh n N).domain.indicator fun t => ((f : (Fin n → ℝ) → ℝ) t) ^ 2 := by
    funext t; by_cases ht : t ∈ (mesh n N).domain <;> simp [ht]
  rw [e, integral_indicator (isOpen_mesh_domain n N).measurableSet]

/-- **Bounded overlap of the local masses**: `Σ_T m_T(x) ≤ 6ⁿ n! ‖x‖²`. -/
theorem sum_locMass_le (N : ℕ) {k : ℤ} (x : L2F ℝ (mesh n N).domain (formIdx n k)) :
    ∑ T ∈ (mesh n N).simplices, locMass x T ≤ (6 ^ n * n.factorial : ℕ) * ‖x‖ ^ 2 := by
  set F : (Fin n → ℝ) → ℝ := fun t => ∑ s : formIdx n k,
    ((mesh n N).domain.indicator ((x s : L2 ℝ (mesh n N).domain) : (Fin n → ℝ) → ℝ) t) ^ 2
  have hF : Integrable F := integrable_finsetSum _ fun s _ => integrable_sq_indicator _
  have hF0 : ∀ t, 0 ≤ F t := fun t => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : ∀ T : Affine.Simplex ℝ (Fin n → ℝ) n, locMass x T =
      ∫ t in Metric.cthickening (2 * hN N) T.closedInterior, F t := fun T => by
    rw [locMass, integral_finsetSum _ fun s _ => (integrable_sq_indicator _).integrableOn]
  simp_rw [h1]
  refine (sum_integral_cthickening_le N hF hF0).trans (le_of_eq ?_)
  rw [integral_finsetSum _ fun s _ => integrable_sq_indicator _, PiLp.norm_sq_eq_of_L2]
  simp_rw [integral_sq_indicator]

/-- **The `L²` norm of a glued field by local integrals** (any element family and mesh):
`‖glue d‖² ≤ Σ_T f(T)` when `Σₛ ‖(d_T)ₛ‖²_{L²(T)} ≤ f(T)` for every simplex. -/
theorem norm_sq_glue_le (E : LocalElement n) (M : SimplicialMesh n) {k : ℕ} (d : E.Piecewise M k)
    (f : Affine.Simplex ℝ (Fin n → ℝ) n → ℝ)
    (hd : ∀ T (hT : T ∈ M.simplices), ∑ s : formIdx n k, ∫ y in T.closedInterior,
      (((d ⟨T, hT⟩ : E.space T k) : FormField n) y s.1) ^ 2 ≤ f T) :
    ‖E.glue M k d‖ ^ 2 ≤ ∑ T ∈ M.simplices, f T := by
  refine (norm_sq_pieceL2_le M M.domain (fun T => formComp (k := (k : ℤ)) (E.extendPW M d T))
    (fun T hT s => continuous_formComp (E.contDiff_extendPW M _ hT).continuous s)).trans
    (Finset.sum_le_sum fun T hT => ?_)
  have e : ∀ s : formIdx n k, ∀ y, formComp (k := (k : ℤ)) (E.extendPW M d T) s y =
      ((d ⟨T, hT⟩ : E.space T k) : FormField n) y s.1 := fun s y => by
    change E.extendPW M d T y s.1 = _
    rw [E.extendPW_of_mem M _ hT]
  simp_rw [e]
  exact hd T hT

/-- `Σₛ ‖zₛ‖²_{L²(T)} ≤ 2ⁿ hⁿ K²` on a simplex of the cube mesh when `|z| ≤ K` there. -/
theorem sum_integral_sq_le_of_abs_le {N k : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) {z : FormField n} (hzc : Continuous z) {K : ℝ}
    (hzb : ∀ y ∈ T.closedInterior, ∀ s, |z y s| ≤ K) :
    ∑ s : formIdx n k, ∫ y in T.closedInterior, (z y s.1) ^ 2 ≤ 2 ^ n * (hN N ^ n * K ^ 2) := by
  obtain ⟨m, σ, rfl⟩ := mem_mesh_simplices.1 hT
  have hh := hN_pos N
  calc ∑ s : formIdx n k, ∫ y in (cubeSimplex N m σ).closedInterior, (z y s.1) ^ 2
      ≤ ∑ _s : formIdx n k, hN N ^ n * K ^ 2 := Finset.sum_le_sum fun s _ =>
        integral_cubeSimplex_le m σ (f := fun y => (z y s.1) ^ 2)
          (((continuous_apply s.1).comp hzc).pow 2)
          (fun y hy => by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hzb y hy s.1) 2)
          (fun y => sq_nonneg _)
    _ = Fintype.card (formIdx n k) * (hN N ^ n * K ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 2 ^ n * (hN N ^ n * K ^ 2) :=
        mul_le_mul_of_nonneg_right (card_formIdx_le _) (by positivity)

/-- **The smoothed field on a simplex is bounded by the local mass**:
`|R x (y)ₛ| ≤ 2ᵏ ((32 / (γ h_N))ⁿ m_T(x))^{1/2}` on `T`. -/
theorem IsAdm.abs_smoothForm_le_locMass {N k : ℕ} {p : SmoothingParam (Fin n → ℝ)}
    (hp : IsAdm γ N p) (hγ1 : γ ≤ 1) (x : L2F ℝ (mesh n N).domain (formIdx n k))
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ (mesh n N).simplices) :
    ∀ y ∈ T.closedInterior, ∀ s,
      |(smoothForm p (isOpen_mesh_domain n N).measurableSet k x : FormField n) y s| ≤
        2 ^ k * √((32 / (γ * hN N)) ^ n * locMass x T) := by
  intro y hy s
  have hh := hN_pos N
  have hγ0 := hp.gamma_pos
  have hMρ : 1 / volume.real (Metric.closedBall (0 : Fin n → ℝ) p.bump.rIn) =
      (32 / (γ * hN N)) ^ n := by
    rw [hp.rIn_eq, volume_real_closedBall_zero (by positivity), one_div, ← inv_pow]
    congr 1
    field_simp
    ring
  refine (abs_smoothForm_le _ p k x y s).trans (mul_le_mul (hp.pow_factor_le hγ1 k) ?_
    (Real.sqrt_nonneg _) (by positivity))
  rw [hMρ]
  refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s' _ => ?_)
    (by positivity))
  refine setIntegral_mono_set (integrable_sq_indicator _).integrableOn
    (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall fun t ht => ?_)
  have hyc : y ∈ closure (cubeDomain n) := by
    rw [← mesh_domain n N]; exact (mesh n N).closedInterior_subset_closure hT hy
  have h1 := hp.norm_dil_sub_le hyc
  have h2 : dist t (p.center + p.factor • (y - p.center)) ≤ γ * hN N / 32 := by
    have := Metric.mem_closedBall.1 ht; rwa [hp.rOut_eq] at this
  refine Metric.mem_cthickening_of_dist_le t y _ _ hy ?_
  calc dist t y ≤ dist t (p.center + p.factor • (y - p.center)) +
        dist (p.center + p.factor • (y - p.center)) y := dist_triangle _ _ _
    _ ≤ γ * hN N / 32 + γ * hN N / 4 := add_le_add h2 (by rw [dist_eq_norm]; exact h1)
    _ ≤ 2 * hN N := by nlinarith

/-- **The local `L²` bound of `Q_N = Π_h R`** on a simplex: `‖Q_N x‖²_{L²(T)} ≲ m_T(x)`. -/
theorem sum_integral_sq_interp_le {N k : ℕ} {B : ℝ} (hB : DofBound n k B)
    {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm γ N p) (hγ1 : γ ≤ 1)
    (x : L2F ℝ (mesh n N).domain (formIdx n k)) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) :
    ∑ s : formIdx n k, ∫ y in T.closedInterior,
      (((((whitneyElement n).globalInterp (mesh n N) k
        (Submodule.inclusion c1Forms_le_contForms
          (smoothForm p (isOpen_mesh_domain n N).measurableSet k x)) :
          (whitneyElement n).Piecewise (mesh n N) k) ⟨T, hT⟩ : (whitneyElement n).space T k) :
          FormField n) y s.1) ^ 2 ≤
      2 ^ n * (B * 2 ^ n * 2 ^ k) ^ 2 * (32 / γ) ^ n * locMass x T := by
  set h := hN N
  have hh : 0 < h := hN_pos N
  have hγ0 := hp.gamma_pos
  set z : FormField n := ((((whitneyElement n).globalInterp (mesh n N) k
    (Submodule.inclusion c1Forms_le_contForms (smoothForm p (isOpen_mesh_domain n N).measurableSet
      k x)) : (whitneyElement n).Piecewise (mesh n N) k) ⟨T, hT⟩ :
        (whitneyElement n).space T k) : FormField n)
  have hz : z ∈ p1MinusForms n k := mem_p1MinusForms_of_space _
  set L := locMass x T
  have hL := locMass_nonneg x T
  set A := 2 ^ k * √((32 / (γ * h)) ^ n * L)
  have hA0 : 0 ≤ A := by positivity
  -- the face integrals of `z` are `O(hᵏ A)`, hence `|z| ≤ B 2ⁿ A` on `T`
  have hdof : ∀ g ⊆ vertexSet T, g.card = k + 1 →
      |simplexIntegral (faceEnum g (k + 1)) z| ≤ 2 ^ n * h ^ k * A := by
    intro g hgT hg
    rw [simplexIntegral_globalInterp k _ ⟨T, hT⟩ hgT hg]
    exact abs_simplexIntegral_face_le hT hgT hg hA0 (hp.abs_smoothForm_le_locMass hγ1 x hT)
  have hzb : ∀ y ∈ T.closedInterior, ∀ s, |z y s| ≤ B * 2 ^ n * A := fun y hy s =>
    le_of_mul_le_mul_left ((hB.apply hT hz (by positivity) hdof hy s).trans
      (le_of_eq (by ring))) (pow_pos hh k)
  calc ∑ s : formIdx n k, ∫ y in T.closedInterior, (z y s.1) ^ 2
      ≤ 2 ^ n * (h ^ n * (B * 2 ^ n * A) ^ 2) :=
        sum_integral_sq_le_of_abs_le hT (isAffineField_of_mem_p1MinusForms hz).continuous hzb
    _ = 2 ^ n * (B * 2 ^ n * 2 ^ k) ^ 2 * (h * (32 / (γ * h))) ^ n * L := by
        rw [mul_pow (B * 2 ^ n) A, mul_pow (2 ^ k), Real.sq_sqrt (by positivity), mul_pow h]; ring
    _ = 2 ^ n * (B * 2 ^ n * 2 ^ k) ^ 2 * (32 / γ) ^ n * L := by
        rw [show h * (32 / (γ * h)) = 32 / γ by field_simp]


theorem subsingleton_L2F_of_lt {Ω : Set (Fin n → ℝ)} {k : ℕ} (hk : n < k) :
    Subsingleton (L2F ℝ Ω (formIdx n k)) := by
  constructor
  intro x y
  refine PiLp.ext fun s => ?_
  exfalso
  have h1 := s.2
  have h2 : #s.1 ≤ n := by simpa using Finset.card_le_univ s.1
  omega

/-- **The `L²` norm of a glued field by local masses** (any element family on the cube meshes):
`‖glue u‖² ≤ K 6ⁿ n! ‖x‖²` when `Σₛ ‖(u_T)ₛ‖²_{L²(T)} ≤ K m_T(x)` for every simplex. -/
theorem norm_sq_glue_le_locMass (E : LocalElement n) {N k : ℕ}
    (x : L2F ℝ (mesh n N).domain (formIdx n k)) (u : E.Piecewise (mesh n N) k) {K : ℝ}
    (hK : 0 ≤ K) (hloc : ∀ T (hT : T ∈ (mesh n N).simplices), ∑ s : formIdx n k,
      ∫ y in T.closedInterior, (((u ⟨T, hT⟩ : E.space T k) : FormField n) y s.1) ^ 2 ≤
        K * locMass x T) :
    ‖E.glue (mesh n N) k u‖ ^ 2 ≤ K * ((6 ^ n * n.factorial : ℕ) * ‖x‖ ^ 2) := by
  refine (norm_sq_glue_le E (mesh n N) u _ hloc).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_locMass_le N x) hK

/-- A bound `‖y‖² ≤ K_k ‖x‖²` in the degrees `k ≤ n` gives `‖y‖ ≤ (Σ_{k ≤ n} K_k)^{1/2} ‖x‖` in
every degree (`L²(Ω; Λᵏ) = 0` for `k > n`). -/
theorem norm_le_sqrt_sum_of_sq_le {K : ℕ → ℝ} (hK : ∀ k, 0 ≤ K k) {Ω : Set (Fin n → ℝ)} {k : ℕ}
    {x y : L2F ℝ Ω (formIdx n k)} (h : k ≤ n → ‖y‖ ^ 2 ≤ K k * ‖x‖ ^ 2) :
    ‖y‖ ≤ √(∑ k ∈ Finset.range (n + 1), K k) * ‖x‖ := by
  by_cases hk : n < k
  · have := subsingleton_L2F_of_lt (Ω := Ω) hk
    rw [Subsingleton.elim y 0, norm_zero]
    positivity
  push Not at hk
  refine le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) ?_
  rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun k _ => hK k)]
  exact (h hk).trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun k _ => hK k)
    (Finset.mem_range.2 (by omega))) (sq_nonneg _))

/-- **The uniform `L²` bound of the smoothed interpolants** `Q_N = Π_h R_N`, for any family of
admissible parameters (`IsAdm`, either family): `‖Q_N x‖ ≤ C ‖x‖` for all `N`, all degrees and all
`x`. -/
theorem exists_norm_smoothedInterp_le (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ C, 0 ≤ C ∧ ∀ (N k : ℕ) (p : SmoothingParam (Fin n → ℝ)), IsAdm γ N p →
      ∀ x : L2F ℝ (mesh n N).domain (formIdx n k),
        ‖(whitneyElement n).smoothedInterp (mesh n N) p
          (isOpen_mesh_domain n N).measurableSet k x‖ ≤ C * ‖x‖ := by
  choose B hB0 hB using fun k : ℕ => exists_dofBound (n := n) k
  have hK : ∀ k, 0 ≤ 2 ^ n * (B k * 2 ^ n * 2 ^ k) ^ 2 * (32 / γ) ^ n *
      ((6 ^ n * n.factorial : ℕ) : ℝ) := fun k => by have := hB0 k; positivity
  refine ⟨_, Real.sqrt_nonneg _, fun N k p hp x => norm_le_sqrt_sum_of_sq_le hK fun _ => ?_⟩
  rw [(whitneyElement n).smoothedInterp_natCast, mul_assoc]
  exact norm_sq_glue_le_locMass _ x _ (by have := hB0 k; positivity)
    fun T hT => sum_integral_sq_interp_le (hB k) hp hγ1 x hT

/-! ### Ingredients of the closeness estimate -/

/-- **The trace of a trimmed linear form on a `k`-face is constant**:
`Σₛ u(F x̂)ₛ minorₛ = k! ∫_q u`. -/
theorem sum_mul_minor_eq {k : ℕ} {u : FormField n} (hu : u ∈ p1MinusForms n k)
    (q : Fin (k + 1) → Fin n → ℝ) (x : Fin k → ℝ) :
    ∑ s, u (simplexMap q x) s * wedgeProd (simplexMatrix q) s univ =
      k.factorial * simplexIntegral q u := by
  rw [← affinePullback_univ_eq_of_mem_p1MinusForms hu q x, affinePullback_apply, pullback_apply]
  rfl

/-- **DOFs of global Whitney fields agree on shared faces.** -/
theorem simplexIntegral_eq_of_mem_globalSpace {M : SimplicialMesh n} {k : ℕ}
    {u : (whitneyElement n).Piecewise M k} (hu : u ∈ (whitneyElement n).globalSpace M k)
    (T T' : M.simplices) {g : Finset (Fin n → ℝ)}
    (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n))
    (hgT' : g ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n)) (hg : g.card = k + 1) :
    simplexIntegral (faceEnum g (k + 1)) ((u T : (whitneyElement n).space T k) : FormField n) =
      simplexIntegral (faceEnum g (k + 1)) ((u T' : (whitneyElement n).space T' k) :
        FormField n) := by
  have := hu T T' g hgT hgT' (⟨(), hg⟩ : WhitneyDofIdx g k)
  rw [simplexIntegral_localDof T hg, simplexIntegral_localDof T' hg] at this
  exact this

theorem interior_closedInterior_subset_cubeDomain {N : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) : interior T.closedInterior ⊆ cubeDomain n := by
  have h := interior_mono ((mesh n N).closedInterior_subset_closure hT)
  rw [mesh_domain, closure_cubeDomain, interior_pi_set Set.finite_univ] at h
  simp only [interior_Icc] at h
  exact h

theorem integral_closedInterior_eq_interior (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    (f : (Fin n → ℝ) → ℝ) :
    ∫ x in T.closedInterior, f x = ∫ x in interior T.closedInterior, f x :=
  (setIntegral_congr_set (interior_ae_eq_of_null_frontier (μ := volume)
    (s := T.closedInterior) (Convex.addHaar_frontier volume (convex_closedInterior T)))).symm

/-! ### The set of points of a reference simplex near its boundary -/

/-- The points of `ℝᵏ` with a barycentric coordinate `< θ`. -/
def nearBdry (k : ℕ) (θ : ℝ) : Set (Fin k → ℝ) := {x | ∃ a, refBary x a < θ}

theorem isOpen_nearBdry (k : ℕ) (θ : ℝ) : IsOpen (nearBdry k θ) := by
  have : nearBdry k θ = ⋃ a, (fun x => refBary x a) ⁻¹' Set.Iio θ := by
    ext x; simp [nearBdry]
  rw [this]
  exact isOpen_iUnion fun a => isOpen_Iio.preimage (continuous_refBary_apply a)

/-- A coordinate slab of the reference simplex has volume at most its width. -/
theorem volume_slab_le {k : ℕ} (θ : ℝ) (j : Fin k) :
    volume (FiniteElement.refSimplex k ∩ {x | x j < θ}) ≤ ENNReal.ofReal θ := by
  classical
  have hsub : FiniteElement.refSimplex k ∩ {x | x j < θ} ⊆
      Set.Icc (0 : Fin k → ℝ) (Function.update 1 j θ) := by
    rintro x ⟨hx, hxj⟩
    have h := refSimplex_subset_pi k hx
    refine ⟨fun i => (h i (Set.mem_univ i)).1, fun i => ?_⟩
    by_cases hij : i = j
    · subst hij; simp only [Function.update_self]; exact le_of_lt hxj
    · simp only [Function.update_of_ne hij, Pi.one_apply]; exact (h i (Set.mem_univ i)).2
  refine (measure_mono hsub).trans ?_
  rw [Real.volume_Icc_pi]
  rw [Finset.prod_eq_single j]
  · simp
  · intro i _ hij; simp [Function.update_of_ne hij]
  · simp

theorem volume_nearBdry_apply_le {k : ℕ} {θ : ℝ} (hθ1 : θ ≤ 1) (a : Fin (k + 1)) :
    volume (FiniteElement.refSimplex k ∩ {x | refBary x a < θ}) ≤ ENNReal.ofReal θ := by
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨j, rfl⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : FiniteElement.refSimplex 0 ∩ {x | refBary x 0 < θ} = ∅ := by
        ext x; simp only [refBary_zero, Finset.univ_eq_empty, Finset.sum_empty, sub_zero,
          Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and,
          not_lt]
        exact fun _ => hθ1
      rw [this, measure_empty]; exact bot_le
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      set π : Equiv.Perm (Fin (k' + 2)) := Equiv.swap 0 1
      have hpre : permMap π ⁻¹' (FiniteElement.refSimplex (k' + 1) ∩ {x | x 0 < θ}) =
          FiniteElement.refSimplex (k' + 1) ∩ {x | refBary x 0 < θ} := by
        rw [Set.preimage_inter, permMap_preimage_refSimplex]
        congr 1
        ext x
        simp only [Set.mem_preimage, Set.mem_ofPred_eq]
        have := congrFun (refBary_permMap π x) 1
        have h1 : refBary (permMap π x) 1 = permMap π x 0 := by
          rw [← Fin.succ_zero_eq_one, refBary_succ]
        rw [← h1, this]
        simp [π, Equiv.swap_apply_right]
      rw [← hpre, (measurePreserving_permMap π).measure_preimage
        (((isClosed_refSimplex _).measurableSet.inter
          (measurableSet_lt (measurable_pi_apply 0) measurable_const))).nullMeasurableSet]
      exact volume_slab_le θ 0
  · simpa using volume_slab_le θ j

/-- **The boundary layer of the reference simplex is small**:
`|{x̂ ∈ T̂_k : some λ̂ₐ(x̂) < θ}| ≤ (k + 1) θ`. -/
theorem volume_real_nearBdry_le {k : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    volume.real (FiniteElement.refSimplex k ∩ nearBdry k θ) ≤ (k + 1) * θ := by
  have e : FiniteElement.refSimplex k ∩ nearBdry k θ =
      ⋃ a, FiniteElement.refSimplex k ∩ {x | refBary x a < θ} := by
    ext x; simp [nearBdry]
  have h : volume (FiniteElement.refSimplex k ∩ nearBdry k θ) ≤ ENNReal.ofReal ((k + 1) * θ) := by
    rw [e]
    refine (measure_iUnion_le _).trans ?_
    calc ∑' a, volume (FiniteElement.refSimplex k ∩ {x | refBary x a < θ})
        = ∑ a, volume (FiniteElement.refSimplex k ∩ {x | refBary x a < θ}) := tsum_fintype _
      _ ≤ ∑ _a : Fin (k + 1), ENNReal.ofReal θ :=
          Finset.sum_le_sum fun a _ => volume_nearBdry_apply_le hθ1 a
      _ = ENNReal.ofReal ((k + 1) * θ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_nsmul,
            nsmul_eq_mul]
          push_cast; rfl
  rw [Measure.real]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h

theorem volume_real_refSimplex_le_one (m : ℕ) :
    volume.real (FiniteElement.refSimplex m) ≤ 1 := by
  rw [volume_real_refSimplex, div_le_one (by positivity)]
  exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero m)

open Classical in
/-- **Integration of a face-integrand bound**: if `H |F(ξ)| ≤ c` near `∂Δ` (barycentric weight
`< θ`) and `≤ c ε` elsewhere, then `H |∫_Δ F| ≤ c (ε + (m + 1) θ)`. -/
theorem mul_abs_integral_refSimplex_le {m : ℕ} {F : (Fin m → ℝ) → ℝ} (hF : Continuous F)
    {H c ε θ : ℝ} (hH : 0 ≤ H) (hc : 0 ≤ c) (hε : 0 ≤ ε) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hpt : ∀ ξ ∈ FiniteElement.refSimplex m,
      H * |F ξ| ≤ c * (if ξ ∈ nearBdry m θ then 1 else ε)) :
    H * |∫ ξ in FiniteElement.refSimplex m, F ξ| ≤ c * (ε + (m + 1) * θ) := by
  have hS : MeasurableSet (FiniteElement.refSimplex m) := measurableSet_refSimplex m
  have hfin : volume (FiniteElement.refSimplex m) ≠ ⊤ := (volume_refSimplex_lt_top m).ne
  have hB := (isOpen_nearBdry m θ).measurableSet
  set β : (Fin m → ℝ) → ℝ := fun ξ => c * ε + c * (nearBdry m θ).indicator 1 ξ
  have hpt' : ∀ ξ ∈ FiniteElement.refSimplex m, H * |F ξ| ≤ β ξ := fun ξ hξ => by
    refine (hpt ξ hξ).trans ?_
    by_cases hb : ξ ∈ nearBdry m θ
    · simp only [hb, ite_true, β, Set.indicator_of_mem hb, Pi.one_apply]
      nlinarith [mul_nonneg hc hε]
    · simp [hb, β]
  have hind : IntegrableOn (fun ξ => (nearBdry m θ).indicator (1 : (Fin m → ℝ) → ℝ) ξ)
      (FiniteElement.refSimplex m) := (integrableOn_const hfin).indicator hB
  have hint : ∫ ξ in FiniteElement.refSimplex m, β ξ =
      c * ε * volume.real (FiniteElement.refSimplex m) +
        c * volume.real (FiniteElement.refSimplex m ∩ nearBdry m θ) := by
    rw [integral_add (integrableOn_const hfin) (hind.const_mul _), setIntegral_const, smul_eq_mul,
      integral_const_mul, integral_indicator_one hB, Measure.real, Measure.real,
      Measure.restrict_apply hB, Set.inter_comm]
    simp only [Measure.real]
    ring
  have hvol := volume_real_refSimplex_le_one m
  have hbad := volume_real_nearBdry_le (k := m) hθ0 hθ1
  calc H * |∫ ξ in FiniteElement.refSimplex m, F ξ|
      ≤ H * ∫ ξ in FiniteElement.refSimplex m, |F ξ| :=
        mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hH
    _ = ∫ ξ in FiniteElement.refSimplex m, H * |F ξ| := (integral_const_mul _ _).symm
    _ ≤ ∫ ξ in FiniteElement.refSimplex m, β ξ :=
        setIntegral_mono_on ((hF.abs.continuousOn.integrableOn_compact
          (isCompact_refSimplex m)).const_mul _)
          ((integrableOn_const hfin).add (hind.const_mul _)) hS hpt'
    _ ≤ c * (ε + (m + 1) * θ) := by
        rw [hint]
        have h1 := mul_le_mul_of_nonneg_left hvol (mul_nonneg hc hε)
        have h2 := mul_le_mul_of_nonneg_left hbad hc
        nlinarith


/-! ### Glued fields almost everywhere -/

/-- **A glued field almost everywhere** (any element family): a.e. point of `Ω` lies in the
interior of a simplex `T'`, where the field is the local field of `T'`. -/
theorem ae_glue_eq_local (E : LocalElement n) {M : SimplicialMesh n} {k : ℕ} (u : E.Piecewise M k)
    (hΩ : MeasurableSet M.domain) :
    ∀ᵐ t ∂volume, t ∈ M.domain → ∃ T' : M.simplices,
      t ∈ interior (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior ∧
        ∀ s : formIdx n k, M.domain.indicator
          ((E.glue M k u s : L2 ℝ M.domain) : (Fin n → ℝ) → ℝ) t =
          ((u T' : E.space T' k) : FormField n) t s.1 := by
  have h1 : ∀ᵐ t ∂volume.restrict M.domain, ∀ s : formIdx n k,
      ((E.glue M k u s : L2 ℝ M.domain) : (Fin n → ℝ) → ℝ) t =
        pieceFun M (fun T => formComp (k := (k : ℤ)) (E.extendPW M u T) s) t := by
    rw [ae_all_iff]
    intro s
    exact coeFn_pieceL2 M M.domain _ (fun T hT s => continuous_formComp
      (E.contDiff_extendPW M u hT).continuous s) s
  have h2 := ae_mem_interior M hΩ
  rw [← ae_restrict_iff' hΩ]
  filter_upwards [h1, h2, ae_restrict_mem hΩ] with t ht1 ht2 htΩ
  obtain ⟨T', hT', htT'⟩ := ht2
  refine ⟨⟨T', hT'⟩, htT', fun s => ?_⟩
  rw [Set.indicator_of_mem htΩ, ht1 s, pieceFun_of_mem_interior M _ hT' htT']
  change E.extendPW M u T' t s.1 = _
  rw [E.extendPW_of_mem M u hT']

/-- Sums over `Finset (Fin n)` of terms vanishing off degree `k`. -/
theorem sum_eq_sum_formIdx {k : ℕ} {f : Finset (Fin n) → ℝ} (hf : ∀ s, #s ≠ k → f s = 0) :
    ∑ s, f s = ∑ s : formIdx n k, f s.1 := by
  have h0 : ∑ s : {s : Finset (Fin n) // ¬ ((#s : ℤ) = (k : ℤ))}, f s = 0 :=
    Finset.sum_eq_zero fun s _ => hf s.1 (fun h => s.2 (by rw [h]))
  rw [← Fintype.sum_subtype_add_sum_subtype (fun s : Finset (Fin n) => (#s : ℤ) = (k : ℤ)) f, h0,
    add_zero]

/-- **The local fields are controlled by the glued field** on any set containing their simplex
(any element family and mesh with `interior T ⊆ Ω` for every simplex `T`). -/
theorem sum_integral_sq_le_of_subset (E : LocalElement n) {M : SimplicialMesh n}
    (hΩ : MeasurableSet M.domain) (hint : ∀ T ∈ M.simplices, interior T.closedInterior ⊆ M.domain)
    {k : ℕ} (u : E.Piecewise M k) (T' : M.simplices) {K : Set (Fin n → ℝ)}
    (hsub : (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior ⊆ K) :
    ∑ s, ∫ y in (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      (((u T' : E.space T' k) : FormField n) y s) ^ 2 ≤
      ∑ s : formIdx n k, ∫ t in K,
        (M.domain.indicator ((E.glue M k u s : L2 ℝ M.domain) : (Fin n → ℝ) → ℝ) t) ^ 2 := by
  set z : FormField n := ((u T' : E.space T' k) : FormField n)
  have hdeg : ∀ y, IsDeg k (z y) := E.isDeg_of_mem (u T').2
  rw [sum_eq_sum_formIdx (fun s hs => by
    have : ∀ y, (z y s) ^ 2 = 0 := fun y => by rw [hdeg y s hs]; ring
    simp_rw [this]; simp)]
  refine Finset.sum_le_sum fun s _ => ?_
  have hae := ae_glue_eq_local E u hΩ
  rw [integral_closedInterior_eq_interior]
  have heq : ∫ y in interior (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, (z y s.1) ^ 2 =
      ∫ y in interior (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
        (M.domain.indicator ((E.glue M k u s : L2 ℝ M.domain) : (Fin n → ℝ) → ℝ) y) ^ 2 := by
    refine setIntegral_congr_ae isOpen_interior.measurableSet ?_
    filter_upwards [hae] with y hy hyT
    obtain ⟨T'', hyT'', hval⟩ := hy (hint T' T'.2 hyT)
    have : T'' = T' := by
      by_contra hne
      exact Set.disjoint_left.1 (M.pairwise_disjoint_interior T''.2 T'.2
        (fun e => hne (Subtype.ext e))) hyT'' hyT
    subst this
    rw [hval s]
  rw [heq]
  exact setIntegral_mono_set ((memLp_indicator hΩ _).integrable_sq).integrableOn
    (Eventually.of_forall fun _ => sq_nonneg _)
    (Eventually.of_forall fun y hy => hsub (interior_subset hy))

/-- **The local mass controls the local fields** of the simplices inside the neighbourhood (any
element family). -/
theorem sum_integral_sq_le_locMass (E : LocalElement n) {N k : ℕ} (u : E.Piecewise (mesh n N) k)
    (T' : (mesh n N).simplices) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hsub : (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior ⊆
      Metric.cthickening (2 * hN N) T.closedInterior) :
    ∑ s, ∫ y in (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      (((u T' : E.space T' k) : FormField n) y s) ^ 2 ≤ locMass (E.glue (mesh n N) k u) T :=
  sum_integral_sq_le_of_subset E (isOpen_mesh_domain n N).measurableSet
    (fun _ hT => by rw [mesh_domain]; exact interior_closedInterior_subset_cubeDomain hT) u T' hsub

/-! ### Mollified differences -/

/-- `|∫ g G| ≤ β` for a probability density `g` and `|G| ≤ β` a.e. on `{g ≠ 0}`. -/
theorem abs_integral_mul_le_of_ae {g G : (Fin n → ℝ) → ℝ} (hg0 : ∀ t, 0 ≤ g t)
    (hgi : Integrable g) (hg1 : ∫ t, g t = 1) (hG : Integrable fun t => g t * G t) {β : ℝ}
    (hb : ∀ᵐ t ∂volume, g t ≠ 0 → |G t| ≤ β) : |∫ t, g t * G t| ≤ β := by
  calc |∫ t, g t * G t| ≤ ∫ t, |g t * G t| := abs_integral_le_integral_abs
    _ ≤ ∫ t, g t * β := by
        refine integral_mono_ae hG.abs (hgi.mul_const β) ?_
        filter_upwards [hb] with t ht
        rw [abs_mul, abs_of_nonneg (hg0 t)]
        by_cases h0 : g t = 0
        · rw [h0]; simp
        · exact mul_le_mul_of_nonneg_left (ht h0) (hg0 t)
    _ = β := by rw [integral_mul_const, hg1, one_mul]


/-- The zero extension of an `L²` `k`-form field, as a fibre form at each point. -/
def extField {Ω : Set (Fin n → ℝ)} {k : ℕ} (v : L2F ℝ Ω (formIdx n k)) (t : Fin n → ℝ) :
    Finset (Fin n) → ℝ :=
  formExt (fun s : formIdx n k => Ω.indicator ((v s : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) t)

theorem smoothForm_apply_eq_integral {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (p : SmoothingParam (Fin n → ℝ)) (k : ℕ) (v : L2F ℝ Ω (formIdx n k)) (x : Fin n → ℝ)
    (s : Finset (Fin n)) :
    (smoothForm p hΩ k v : FormField n) x s = p.factor ^ k *
      ∫ t, extField v t s * p.bump.normed volume (p.center + p.factor • (x - p.center) - t) := by
  by_cases hs : (#s : ℤ) = (k : ℤ)
  · have e := smoothForm_apply_eq hΩ p k v x ⟨s, hs⟩
    simp only at e
    rw [e]
    congr 2
    funext t
    rw [extField, formExt_of_card _ hs]
  · rw [isDeg_smoothForm p hΩ k v x s (fun h => hs (by rw [h]))]
    have : ∀ t, extField v t s = 0 := fun t => by simp [extField, formExt, hs]
    simp [this]

theorem integrable_extField_mul {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω) {k : ℕ}
    (v : L2F ℝ Ω (formIdx n k)) (φ : ContDiffBump (0 : Fin n → ℝ)) (y : Fin n → ℝ)
    (s : Finset (Fin n)) :
    Integrable fun t => extField v t s * φ.normed volume (y - t) := by
  by_cases hs : (#s : ℤ) = (k : ℤ)
  · have e : ∀ t, extField v t s = Ω.indicator ((v ⟨s, hs⟩ : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) t :=
      fun t => by rw [extField, formExt_of_card _ hs]
    simp_rw [e]
    exact integrable_mul_isTest ((memLp_indicator hΩ _).locallyIntegrable (by norm_num))
      (isTest_normed_comp_sub φ y)
  · have : ∀ t, extField v t s = 0 := fun t => by simp [extField, formExt, hs]
    simp [this]

/-- **The face integrand of `u - R v` as a mollified average**: for any fibre form `a` and
coefficients `m`, `Σₛ (aₛ - (R v)(x)ₛ) mₛ = ∫ ρ(x̂ - t) Σₛ (aₛ - cᵏ v̄(t)ₛ) mₛ dt`, `x̂` the dilated
point. -/
theorem sum_sub_smoothForm_mul_eq {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (p : SmoothingParam (Fin n → ℝ)) (k : ℕ) (v : L2F ℝ Ω (formIdx n k))
    (a m : Finset (Fin n) → ℝ) (x : Fin n → ℝ) :
    ∑ s, (a s - (smoothForm p hΩ k v : FormField n) x s) * m s =
      ∫ t, p.bump.normed volume (p.center + p.factor • (x - p.center) - t) *
        ∑ s, (a s - p.factor ^ k * extField v t s) * m s := by
  set ŷ := p.center + p.factor • (x - p.center)
  set g : (Fin n → ℝ) → ℝ := fun t => p.bump.normed volume (ŷ - t)
  have hg : Integrable g := (isTest_normed_comp_sub p.bump ŷ).continuous.integrable_of_hasCompactSupport
    (isTest_normed_comp_sub p.bump ŷ).hasCompactSupport
  have hg1 : ∫ t, g t = 1 := integral_normed_comp_sub p.bump ŷ
  have e : ∀ t, g t * ∑ s, (a s - p.factor ^ k * extField v t s) * m s =
      ∑ s, ((a s * m s) * g t - (p.factor ^ k * m s) * (extField v t s * g t)) := fun t => by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => by ring
  have hint : ∀ s ∈ (Finset.univ : Finset (Finset (Fin n))), Integrable fun t =>
      (a s * m s) * g t - (p.factor ^ k * m s) * (extField v t s * g t) := fun s _ =>
    (hg.const_mul _).sub ((integrable_extField_mul hΩ v p.bump ŷ s).const_mul _)
  rw [integral_congr_ae (Eventually.of_forall e), integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_sub (hg.const_mul _) ((integrable_extField_mul hΩ v p.bump ŷ s).const_mul _),
    integral_const_mul, integral_const_mul, hg1, smoothForm_apply_eq_integral hΩ p k v x s]
  ring


/-- **The zero extension of a glued field almost everywhere** (any element family): a.e. point
of `Ω` lies in the interior of a simplex `T'` whose local field is the zero extension there. -/
theorem ae_extField_glue_eq (E : LocalElement n) {M : SimplicialMesh n} {k : ℕ}
    (u : E.Piecewise M k) (hΩ : MeasurableSet M.domain) :
    ∀ᵐ t ∂volume, t ∈ M.domain → ∃ T' : M.simplices,
      t ∈ interior (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior ∧
        ∀ s, extField (E.glue M k u) t s = ((u T' : E.space T' k) : FormField n) t s := by
  filter_upwards [ae_glue_eq_local E u hΩ] with t ht htΩ
  obtain ⟨T', htT', hval⟩ := ht htΩ
  refine ⟨T', htT', fun s => ?_⟩
  by_cases hs' : (#s : ℤ) = (k : ℤ)
  · rw [extField, formExt_of_card _ hs']; exact hval ⟨s, hs'⟩
  · have : extField (E.glue M k u) t s = 0 := by simp [extField, formExt, hs']
    rw [this, E.isDeg_of_mem (u T').2 t s (fun h' => hs' (by rw [h']))]

/-- `H |Σₛ fₛ cₛ| ≤ K Σₛ |cₛ|` when `H |fₛ| ≤ K` for every `s`. -/
theorem mul_abs_sum_mul_le {H K : ℝ} (hH : 0 ≤ H) {f c : Finset (Fin n) → ℝ}
    (hf : ∀ s, H * |f s| ≤ K) : H * |∑ s, f s * c s| ≤ K * ∑ s, |c s| := by
  calc H * |∑ s, f s * c s| ≤ H * ∑ s, |f s| * |c s| :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (le_of_eq (Finset.sum_congr rfl fun s _ => abs_mul _ _))) hH
    _ = ∑ s, (H * |f s|) * |c s| := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
    _ ≤ ∑ s, K * |c s| := Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (hf s) (abs_nonneg _)
    _ = K * ∑ s, |c s| := by rw [Finset.mul_sum]

open Classical in
/-- **The pointwise estimate of a face integrand of `v - R v`**, for any element family and mesh:
at a point `x` with dilated point `x̂`, if the local field `a` at `x` and, a.e. near `x̂` inside `Ω`,
a local field `w` representing `v` obey the inverse estimates `H |·| ≤ A √L`, then
`H |Σₛ (aₛ - (R v)(x)ₛ) cₛ| ≤ (Σₛ |cₛ|) A √L 2^{k+1} · (1 or (k + 1) ε)`. The factor `(k + 1) ε`
holds when (`¬ b`) the traces agree (`Σₛ aₛ cₛ = Σₛ w(x)ₛ cₛ`), the displacement costs
`H |w(x)ₛ - w(t)ₛ| ≤ ε A √L`, the dilation defect is `|1 - cᵏ| ≤ k 2ᵏ ε`, and samples outside
`Ω` force `Σₛ aₛ cₛ = 0`. -/
theorem sqrt_mul_abs_sum_sub_smoothForm_le {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (p : SmoothingParam (Fin n → ℝ)) {k : ℕ} (v : L2F ℝ Ω (formIdx n k)) (x : Fin n → ℝ)
    (a c : Finset (Fin n) → ℝ) {H A L ε : ℝ} (b : Prop) (hH : 0 < H) (hA0 : 0 ≤ A)
    (hε : 0 ≤ ε) (hκ : p.factor ^ k ≤ 2 ^ k)
    (hdef : |1 - p.factor ^ k| ≤ k * 2 ^ k * ε) (ha : ∀ s, H * |a s| ≤ A * √L)
    (hloc : ∀ᵐ t ∂volume, dist t (p.center + p.factor • (x - p.center)) < p.bump.rOut →
      t ∈ Ω → ∃ w : FormField n, (∀ s, extField v t s = w t s) ∧ (∀ s, H * |w t s| ≤ A * √L) ∧
        (¬ b → ∑ s, a s * c s = ∑ s, w x s * c s ∧ (∀ s, H * |w x s| ≤ A * √L) ∧
          ∀ s, H * |w x s - w t s| ≤ ε * (A * √L)))
    (hout : ¬ b → ∀ t, dist t (p.center + p.factor • (x - p.center)) < p.bump.rOut → t ∉ Ω →
      ∑ s, a s * c s = 0) :
    H * |∑ s, (a s - (smoothForm p hΩ k v : FormField n) x s) * c s| ≤
      (∑ s, |c s|) * A * √L * 2 ^ (k + 1) * (if b then 1 else (k + 1) * ε) := by
  set ŷ := p.center + p.factor • (x - p.center)
  set κ := p.factor ^ k
  set R := (∑ s, |c s|) * A * √L * 2 ^ (k + 1) * (if b then 1 else (k + 1) * ε)
  have hκ0 : 0 ≤ κ := pow_nonneg p.factor_pos.le k
  have hAL : 0 ≤ A * √L := mul_nonneg hA0 (Real.sqrt_nonneg _)
  have h2k : (0 : ℝ) ≤ 2 ^ k := by positivity
  -- the four cases of the pointwise bound, as `H |fₛ| ≤ K` with `K Σₛ |cₛ| ≤ R`
  have hnear : b → ∀ f : Finset (Fin n) → ℝ, (∀ s, H * |f s| ≤ 2 ^ (k + 1) * (A * √L)) →
      H * |∑ s, f s * c s| ≤ R := fun hb f hf =>
    (mul_abs_sum_mul_le hH.le hf).trans (le_of_eq (by simp only [R, hb, ite_true]; ring))
  have hfar : ¬ b → ∀ f : Finset (Fin n) → ℝ,
      (∀ s, H * |f s| ≤ (k + 1) * 2 ^ k * ε * (A * √L)) → H * |∑ s, f s * c s| ≤ R :=
    fun hb f hf => (mul_abs_sum_mul_le hH.le hf).trans (by
      simp only [R, hb, ite_false, pow_succ]
      have : 0 ≤ (k + 1) * 2 ^ k * ε * (A * √L) * ∑ s, |c s| := by positivity
      nlinarith)
  have hmono : A * √L ≤ 2 ^ (k + 1) * (A * √L) :=
    le_mul_of_one_le_left hAL (one_le_pow₀ (by norm_num))
  rw [sum_sub_smoothForm_mul_eq hΩ p k v a c x]
  set G : (Fin n → ℝ) → ℝ := fun t => ∑ s, (a s - κ * extField v t s) * c s
  set ρ : (Fin n → ℝ) → ℝ := fun t => p.bump.normed volume (ŷ - t)
  have hρi : Integrable ρ :=
    (isTest_normed_comp_sub p.bump ŷ).continuous.integrable_of_hasCompactSupport
      (isTest_normed_comp_sub p.bump ŷ).hasCompactSupport
  have hρG : Integrable fun t => ρ t * G t := by
    have e : (fun t => ρ t * G t) = fun t => ∑ s, ((a s * c s) * ρ t -
        (κ * c s) * (extField v t s * ρ t)) := by
      funext t; simp only [G, Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => by ring
    rw [e]
    exact integrable_finsetSum _ fun s _ =>
      (hρi.const_mul _).sub ((integrable_extField_mul hΩ v p.bump ŷ s).const_mul _)
  have hb : ∀ᵐ t ∂volume, ρ t ≠ 0 → |G t| ≤ R / H := by
    filter_upwards [hloc] with t ht hρt
    have hdist : dist t ŷ < p.bump.rOut := by
      by_contra hcon; push Not at hcon
      exact hρt (normed_eq_zero_of_le p.bump hcon)
    rw [le_div_iff₀ hH, mul_comm]
    by_cases htΩ : t ∈ Ω
    · obtain ⟨w, hext, hwt, hfar'⟩ := ht hdist htΩ
      have hGt : G t = ∑ s, (a s - κ * w t s) * c s := by simp only [G, hext]
      rw [hGt]
      by_cases hbad : b
      · refine hnear hbad _ fun s => ?_
        calc H * |a s - κ * w t s| ≤ H * (|a s| + κ * |w t s|) :=
              mul_le_mul_of_nonneg_left ((abs_sub _ _).trans
                (by rw [abs_mul, abs_of_nonneg hκ0])) hH.le
          _ = H * |a s| + κ * (H * |w t s|) := by ring
          _ ≤ A * √L + 2 ^ k * (A * √L) :=
              add_le_add (ha s) (mul_le_mul hκ (hwt s) (by positivity) h2k)
          _ ≤ 2 ^ (k + 1) * (A * √L) := by
              rw [pow_succ]
              nlinarith [mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := k)) hAL]
      · obtain ⟨htr, hwx, hlip⟩ := hfar' hbad
        have e : ∑ s, (a s - κ * w t s) * c s =
            ∑ s, ((1 - κ) * w x s + κ * (w x s - w t s)) * c s := by
          have e1 : ∑ s, (a s - κ * w t s) * c s =
              ∑ s, a s * c s - ∑ s, κ * w t s * c s := by
            rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun s _ => by ring
          have e2 : ∑ s, ((1 - κ) * w x s + κ * (w x s - w t s)) * c s =
              ∑ s, w x s * c s - ∑ s, κ * w t s * c s := by
            rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun s _ => by ring
          rw [e1, e2, htr]
        rw [e]
        refine hfar hbad _ fun s => ?_
        calc H * |(1 - κ) * w x s + κ * (w x s - w t s)|
            ≤ |1 - κ| * (H * |w x s|) + κ * (H * |w x s - w t s|) := by
              refine (mul_le_mul_of_nonneg_left (abs_add_le _ _) hH.le).trans (le_of_eq ?_)
              rw [abs_mul, abs_mul, abs_of_nonneg hκ0]; ring
          _ ≤ (k * 2 ^ k * ε) * (A * √L) + 2 ^ k * (ε * (A * √L)) :=
              add_le_add (mul_le_mul hdef (hwx s) (by positivity) (by positivity))
                (mul_le_mul hκ (hlip s) (by positivity) h2k)
          _ = (k + 1) * 2 ^ k * ε * (A * √L) := by ring
    · have hext : ∀ s, extField v t s = 0 := fun s => by
        simp [extField, formExt, Set.indicator_of_notMem htΩ]
      have hGt : G t = ∑ s, a s * c s := by simp only [G, hext]; simp
      rw [hGt]
      by_cases hbad : b
      · exact hnear hbad a fun s => (ha s).trans hmono
      · rw [hout hbad t hdist htΩ, abs_zero, mul_zero]
        simp only [R, hbad, ite_false]
        positivity
  have hmain := abs_integral_mul_le_of_ae (fun t => p.bump.nonneg_normed _) hρi
    (integral_normed_comp_sub p.bump ŷ) hρG hb
  rw [le_div_iff₀ hH, mul_comm] at hmain
  exact hmain

/-- The local inverse estimates on all the Kuhn simplices, with one constant. -/
def InvBound (n k : ℕ) (A : ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {z : FormField n},
    z ∈ p1MinusForms n k →
      (∀ x ∈ (mapEquiv (boxMap t h hh.ne') (kuhnSimplex σ)).closedInterior, ∀ s,
        √h ^ n * |z x s| ≤ A * √(∑ s, ∫ x in (mapEquiv (boxMap t h hh.ne')
          (kuhnSimplex σ)).closedInterior, (z x s) ^ 2)) ∧
      (∀ x x' s, √h ^ n * h * |z x s - z x' s| ≤ A * ‖x - x'‖ *
        √(∑ s, ∫ x in (mapEquiv (boxMap t h hh.ne') (kuhnSimplex σ)).closedInterior,
          (z x s) ^ 2))

theorem exists_invBound (k : ℕ) : ∃ A, 0 ≤ A ∧ InvBound n k A := by
  choose A hA0 hA using fun σ : Equiv.Perm (Fin n) => exists_local_inverse_bound (kuhnSimplex σ) k
  have hle : ∀ σ, A σ ≤ ∑ σ, A σ := fun σ =>
    Finset.single_le_sum (fun σ _ => hA0 σ) (Finset.mem_univ σ)
  refine ⟨∑ σ, A σ, Finset.sum_nonneg fun σ _ => hA0 σ, fun σ h hh t z hz => ?_⟩
  obtain ⟨h1, h2⟩ := hA σ hh t hz
  exact ⟨fun x hx s => (h1 x hx s).trans (mul_le_mul_of_nonneg_right (hle σ)
      (Real.sqrt_nonneg _)),
    fun x x' s => (h2 x x' s).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hle σ) (norm_nonneg _)) (Real.sqrt_nonneg _))⟩

theorem InvBound.apply {k : ℕ} {A : ℝ} (hA : InvBound n k A) {N : ℕ}
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ (mesh n N).simplices) {z : FormField n}
    (hz : z ∈ p1MinusForms n k) :
    (∀ x ∈ T.closedInterior, ∀ s, √(hN N) ^ n * |z x s| ≤
      A * √(∑ s, ∫ x in T.closedInterior, (z x s) ^ 2)) ∧
    (∀ x x' s, √(hN N) ^ n * hN N * |z x s - z x' s| ≤
      A * ‖x - x'‖ * √(∑ s, ∫ x in T.closedInterior, (z x s) ^ 2)) := by
  obtain ⟨m, σ, rfl⟩ := mem_mesh_simplices.1 hT
  rw [cubeSimplex_eq]
  exact hA σ (hN_pos N) _ hz


theorem self_subset_cthickening (T : Affine.Simplex ℝ (Fin n → ℝ) n) {r : ℝ} (hr : 0 ≤ r) :
    T.closedInterior ⊆ Metric.cthickening r T.closedInterior :=
  Metric.self_subset_cthickening _ |>.trans (Metric.cthickening_mono hr _)

/-- The sampling condition at a face point: every sample of the smoother outside `Ω` forces the
face integral to vanish (vacuous for the maximal family; for the minimal family it is the
vanishing of the boundary DOFs). -/
def SampleOK {N k : ℕ} (γ : ℝ) (p : SmoothingParam (Fin n → ℝ))
    (u : (whitneyElement n).Piecewise (mesh n N) k) : Prop :=
  ∀ (T : (mesh n N).simplices) (g : Finset (Fin n → ℝ)),
    g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) → g.card = k + 1 →
    ∀ ξ ∈ FiniteElement.refSimplex k, ξ ∉ nearBdry k γ →
      ∀ t, dist t (p.center + p.factor • (simplexMap (faceEnum g (k + 1)) ξ - p.center)) <
        p.bump.rOut → t ∉ (mesh n N).domain →
        simplexIntegral (faceEnum g (k + 1)) ((u T : (whitneyElement n).space T k) : FormField n) = 0

/-- **Samples of the smoother near a point of the closed cube**: if `x ∈ T` and `t ∈ T'` lies in
the support of the bump at the dilated point of `x`, then `‖x - t‖ < γ h / 2` and `T'` lies in
the `2h`-neighbourhood of `T`. -/
theorem IsAdm.norm_sub_lt_and_subset {N : ℕ} {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm γ N p)
    (hγ1 : γ ≤ 1) {T T' : Affine.Simplex ℝ (Fin n → ℝ) n} (hT' : T' ∈ (mesh n N).simplices)
    {x t : Fin n → ℝ} (hxT : x ∈ T.closedInterior) (hxc : x ∈ closure (cubeDomain n))
    (htT' : t ∈ T'.closedInterior)
    (hdist : dist t (p.center + p.factor • (x - p.center)) < p.bump.rOut) :
    ‖x - t‖ < γ * hN N / 2 ∧ T'.closedInterior ⊆ Metric.cthickening (2 * hN N) T.closedInterior := by
  have hγh := hp.gamma_h_nonneg
  have hŷ := hp.norm_dil_sub_le hxc
  set ŷ := p.center + p.factor • (x - p.center)
  have hxt : ‖x - t‖ < γ * hN N / 2 := by
    have h1 : ‖ŷ - t‖ < γ * hN N / 32 := by
      rw [← dist_eq_norm, dist_comm, ← hp.rOut_eq]; exact hdist
    calc ‖x - t‖ = ‖(x - ŷ) + (ŷ - t)‖ := by congr 1; abel
      _ ≤ ‖x - ŷ‖ + ‖ŷ - t‖ := norm_add_le _ _
      _ < γ * hN N / 4 + γ * hN N / 32 := by
          rw [norm_sub_rev] at hŷ; exact add_lt_add_of_le_of_lt hŷ h1
      _ ≤ γ * hN N / 2 := by linarith
  refine ⟨hxt, fun y hy => ?_⟩
  obtain ⟨m', σ', rfl⟩ := mem_mesh_simplices.1 hT'
  have hdy : ‖y - t‖ ≤ hN N := norm_sub_le_of_mem_cubeSimplex hy htT'
  refine Metric.mem_cthickening_of_dist_le y x _ _ hxT ?_
  rw [dist_eq_norm]
  have hh := hN_pos N
  calc ‖y - x‖ = ‖(y - t) + (t - x)‖ := by congr 1; abel
    _ ≤ ‖y - t‖ + ‖t - x‖ := norm_add_le _ _
    _ ≤ hN N + γ * hN N / 2 := by rw [norm_sub_rev t x]; exact add_le_add hdy hxt.le
    _ ≤ 2 * hN N := by nlinarith

open Classical in
/-- **The pointwise estimate of the face integrand of `v - Q_N v`** (`v ∈ Vₕ`): at a point
`x = F_g(ξ)` of a `k`-face `g` of `T`,
`h^{n/2} |Σₛ (v_T - R v)(x)ₛ minorₛ| ≤ (Σₛ |minorₛ|) A m_T(v)^{1/2} 2^{k+1} · (1 or (k + 1) γ)`,
with the factor `(k + 1) γ` when all barycentric coordinates of `ξ` are `≥ γ`. In that case
every simplex sampled by the smoother inside `Ω` contains `g`, where the traces of the local
fields agree; the error is the dilation defect `1 - cᵏ` and the displacement `O(γ h)` against
the inverse estimates (samples outside `Ω` are controlled by `SampleOK`). Near `∂g` only the
inverse estimates are used. -/
theorem sqrt_mul_abs_integrand_le {N k : ℕ} {A : ℝ} (hA0 : 0 ≤ A) (hA : InvBound n k A)
    {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm γ N p)
    (hγ2 : γ ≤ 1 / 2) {u : (whitneyElement n).Piecewise (mesh n N) k}
    (hu : u ∈ (whitneyElement n).globalSpace (mesh n N) k) (hs : SampleOK γ p u)
    (T : (mesh n N).simplices)
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n))
    (hg : g.card = k + 1) {ξ : Fin k → ℝ} (hξ : ξ ∈ FiniteElement.refSimplex k) :
    √(hN N) ^ n * |∑ s, (((u T : (whitneyElement n).space T k) : FormField n)
        (simplexMap (faceEnum g (k + 1)) ξ) s -
      (smoothForm p (isOpen_mesh_domain n N).measurableSet k
        ((whitneyElement n).glue (mesh n N) k u) : FormField n)
        (simplexMap (faceEnum g (k + 1)) ξ) s) *
          wedgeProd (simplexMatrix (faceEnum g (k + 1))) s univ| ≤
      (∑ s, |wedgeProd (simplexMatrix (faceEnum g (k + 1))) s univ|) * A *
        √(locMass ((whitneyElement n).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)) *
        2 ^ (k + 1) * (if ξ ∈ nearBdry k γ then 1 else (k + 1) * γ) := by
  have hγ := hp.gamma_pos
  have hγ1 : γ ≤ 1 := by linarith
  set h := hN N
  have hh : 0 < h := hN_pos N
  have hh2 : h ≤ 1 / 2 := hN_le N
  set hΩ := (isOpen_mesh_domain n N).measurableSet
  set q := faceEnum g (k + 1)
  set x := simplexMap q ξ
  set uT : FormField n := ((u T : (whitneyElement n).space T k) : FormField n)
  set L := locMass ((whitneyElement n).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have hxT : x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior :=
    simplexMap_faceEnum_mem hgT hg hξ
  have hxc : x ∈ closure (cubeDomain n) := by
    rw [← mesh_domain n N]; exact (mesh n N).closedInterior_subset_closure T.2 hxT
  -- the local fields near `x` obey the inverse estimates against the local mass of `T`
  have hinv : ∀ T' : (mesh n N).simplices, (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior ⊆
      Metric.cthickening (2 * h) (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior →
      (∀ y ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ∀ s,
        √h ^ n * |((u T' : (whitneyElement n).space T' k) : FormField n) y s| ≤ A * √L) ∧
      ∀ y y' s, √h ^ n * h * |((u T' : (whitneyElement n).space T' k) : FormField n) y s -
        ((u T' : (whitneyElement n).space T' k) : FormField n) y' s| ≤ A * ‖y - y'‖ * √L := by
    intro T' hsub
    have hL' := Real.sqrt_le_sqrt (sum_integral_sq_le_locMass (whitneyElement n) u T' hsub)
    obtain ⟨h1, h2⟩ := hA.apply T'.2 (mem_p1MinusForms_of_space (u T'))
    exact ⟨fun y hy s => (h1 y hy s).trans (mul_le_mul_of_nonneg_left hL' hA0),
      fun y y' s => (h2 y y' s).trans (mul_le_mul_of_nonneg_left hL' (by positivity))⟩
  refine sqrt_mul_abs_sum_sub_smoothForm_le hΩ p _ x (uT x) _ (ξ ∈ nearBdry k γ)
    (pow_pos (Real.sqrt_pos.2 hh) n) hA0 hγ.le (hp.pow_factor_le hγ1 k)
    ((hp.abs_one_sub_pow_le hγ1 k).trans (mul_le_mul_of_nonneg_left (by nlinarith)
      (by positivity)))
    (fun s => (hinv T (self_subset_cthickening _ (by positivity))).1 x hxT s) ?_ ?_
  · filter_upwards [ae_extField_glue_eq (whitneyElement n) u hΩ] with t ht hdist htΩ
    obtain ⟨T', htT', hext⟩ := ht htΩ
    set u' : FormField n := ((u T' : (whitneyElement n).space T' k) : FormField n)
    have htT'c : t ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior := interior_subset htT'
    obtain ⟨hxt, hT'sub⟩ := hp.norm_sub_lt_and_subset hγ1 T'.2 hxT hxc htT'c hdist
    obtain ⟨hb1, hb2⟩ := hinv T' hT'sub
    refine ⟨u', hext, fun s => hb1 t htT'c s, fun hbad => ?_⟩
    have hμ : ∀ a, γ ≤ refBary ξ a := by
      intro a; by_contra hlt; push Not at hlt; exact hbad ⟨a, hlt⟩
    have hgT' : g ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n) :=
      subset_vertexSet_of_near T.2 T'.2 hgT hg hγ hγ2 hμ (sum_refBary ξ) htT'c
        (by rw [← simplexMap_eq_sum q ξ]; exact hxt)
    refine ⟨?_, fun s => hb1 x (simplexMap_faceEnum_mem hgT' hg hξ) s, fun s => ?_⟩
    · rw [sum_mul_minor_eq (mem_p1MinusForms_of_space (u T)) q ξ,
        sum_mul_minor_eq (mem_p1MinusForms_of_space (u T')) q ξ,
        simplexIntegral_eq_of_mem_globalSpace hu T T' hgT hgT' hg]
    · refine le_of_mul_le_mul_right ?_ hh
      calc √h ^ n * |u' x s - u' t s| * h = √h ^ n * h * |u' x s - u' t s| := by ring
        _ ≤ A * ‖x - t‖ * √L := hb2 x t s
        _ ≤ A * (γ * h) * √L := by gcongr; linarith [norm_nonneg (x - t)]
        _ = γ * (A * √L) * h := by ring
  · intro hbad t hdist htΩ
    rw [sum_mul_minor_eq (mem_p1MinusForms_of_space (u T)) q ξ]
    change ↑k.factorial * simplexIntegral q uT = 0
    rw [hs T g hgT hg ξ hξ hbad t hdist htΩ, mul_zero]

/-- **The DOF error of `Q_N` on `Vₕ`**: for `v ∈ Vₕ` and a `k`-face `g` of `T`,
`h^{n/2} |∫_g (v_T - R v)| ≤ 3 (k + 1) 2ⁿ k! 2^{k+1} A γ hᵏ m_T(v)^{1/2}`. -/
theorem sqrt_mul_abs_dof_err_le {N k : ℕ} {A : ℝ} (hA0 : 0 ≤ A) (hA : InvBound n k A)
    {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm γ N p)
    (hγ2 : γ ≤ 1 / 2) {u : (whitneyElement n).Piecewise (mesh n N) k}
    (hu : u ∈ (whitneyElement n).globalSpace (mesh n N) k) (hs : SampleOK γ p u)
    (T : (mesh n N).simplices)
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n))
    (hg : g.card = k + 1) :
    √(hN N) ^ n * |simplexIntegral (faceEnum g (k + 1))
        ((u T : (whitneyElement n).space T k) : FormField n) -
      simplexIntegral (faceEnum g (k + 1))
        (smoothForm p (isOpen_mesh_domain n N).measurableSet k
          ((whitneyElement n).glue (mesh n N) k u) : FormField n)| ≤
      3 * (k + 1) * 2 ^ n * k.factorial * 2 ^ (k + 1) * A * γ * hN N ^ k *
        √(locMass ((whitneyElement n).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)) := by
  have hγ := hp.gamma_pos
  set q := faceEnum g (k + 1)
  set uT : FormField n := ((u T : (whitneyElement n).space T k) : FormField n)
  set w : FormField n := (smoothForm p (isOpen_mesh_domain n N).measurableSet k
    ((whitneyElement n).glue (mesh n N) k u) : FormField n)
  set L := locMass ((whitneyElement n).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have hMm : ∑ s, |wedgeProd (simplexMatrix q) s univ| ≤ 2 ^ n * (k.factorial * hN N ^ k) :=
    sum_abs_minor_face_le T.2 hgT hg
  have huc : Continuous uT :=
    (isAffineField_of_mem_p1MinusForms (mem_p1MinusForms_of_space _)).continuous
  have hwc : Continuous w := (mem_c1Forms.1 (smoothForm p
    (isOpen_mesh_domain n N).measurableSet k ((whitneyElement n).glue (mesh n N) k u)).2).continuous
  rw [← simplexIntegral_sub huc.continuousOn hwc.continuousOn, simplexIntegral_def]
  set c := 2 ^ n * (k.factorial * hN N ^ k) * A * √L * 2 ^ (k + 1)
  have hh := hN_pos N
  have hc0 : 0 ≤ c := by positivity
  have hc : 0 ≤ c * ((k + 1) * γ) := by positivity
  refine (mul_abs_integral_refSimplex_le (continuous_finsetSum _ fun s _ =>
    ((((continuous_apply s).comp (huc.comp (continuous_simplexMap q))).sub
      ((continuous_apply s).comp (hwc.comp (continuous_simplexMap q)))).mul continuous_const))
    (pow_nonneg (Real.sqrt_nonneg _) n) hc0 (by positivity) hγ.le
    (by linarith) fun ξ hξ => (sqrt_mul_abs_integrand_le hA0 hA hp hγ2 hu hs T hgT hg hξ).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hMm hA0) (Real.sqrt_nonneg _)) (by positivity))
        (by split_ifs <;> positivity))).trans ?_
  calc c * ((k + 1) * γ + (k + 1) * γ) ≤ 3 * (c * ((k + 1) * γ)) := by linarith
    _ = _ := by simp only [c]; ring

/-- **The local `L²` error of `Q_N` on `Vₕ`**: `‖v - Q_N v‖²_{L²(T)} ≲ γ² m_T(v)`. -/
theorem sum_integral_sq_sub_interp_le {N k : ℕ} {A B : ℝ} (hA0 : 0 ≤ A) (hA : InvBound n k A)
    (hB : DofBound n k B) {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm γ N p)
    (hγ2 : γ ≤ 1 / 2) {u : (whitneyElement n).Piecewise (mesh n N) k}
    (hu : u ∈ (whitneyElement n).globalSpace (mesh n N) k) (hs : SampleOK γ p u)
    (T : (mesh n N).simplices) :
    ∑ s : formIdx n k, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      ((((u T : (whitneyElement n).space T k) : FormField n) -
        ((((whitneyElement n).globalInterp (mesh n N) k
          (Submodule.inclusion c1Forms_le_contForms
            (smoothForm p (isOpen_mesh_domain n N).measurableSet k
              ((whitneyElement n).glue (mesh n N) k u))) :
            (whitneyElement n).Piecewise (mesh n N) k) T : (whitneyElement n).space T k) :
              FormField n)) y s.1) ^ 2 ≤
      2 ^ n * (B * (3 * (k + 1) * 2 ^ n * k.factorial * 2 ^ (k + 1) * A) * γ) ^ 2 *
        locMass ((whitneyElement n).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n) := by
  set h := hN N
  have hh : 0 < h := hN_pos N
  set w := smoothForm p (isOpen_mesh_domain n N).measurableSet k
    ((whitneyElement n).glue (mesh n N) k u)
  set z : FormField n := ((u T : (whitneyElement n).space T k) : FormField n) -
    ((((whitneyElement n).globalInterp (mesh n N) k (Submodule.inclusion c1Forms_le_contForms w) :
      (whitneyElement n).Piecewise (mesh n N) k) T : (whitneyElement n).space T k) : FormField n)
  have hz : z ∈ p1MinusForms n k := Submodule.sub_mem _ (mem_p1MinusForms_of_space _)
    (mem_p1MinusForms_of_space _)
  set L := locMass ((whitneyElement n).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have hL0 : 0 ≤ L := locMass_nonneg _ _
  have hγ := hp.gamma_pos
  set C₁ := 3 * (k + 1) * 2 ^ n * k.factorial * 2 ^ (k + 1) * A
  have hC₁ : 0 ≤ C₁ := by positivity
  have hsq : 0 < √h ^ n := pow_pos (Real.sqrt_pos.2 hh) n
  set D := C₁ * γ * h ^ k * √L / √h ^ n
  have hD0 : 0 ≤ D := by positivity
  have hdof : ∀ g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n), g.card = k + 1 →
      |simplexIntegral (faceEnum g (k + 1)) z| ≤ D := by
    intro g hgT hg
    have hc1 : Continuous ((u T : (whitneyElement n).space T k) : FormField n) :=
      (isAffineField_of_mem_p1MinusForms (mem_p1MinusForms_of_space _)).continuous
    have hc2 : Continuous ((((whitneyElement n).globalInterp (mesh n N) k
        (Submodule.inclusion c1Forms_le_contForms w) : (whitneyElement n).Piecewise (mesh n N) k) T :
          (whitneyElement n).space T k) : FormField n) :=
      (isAffineField_of_mem_p1MinusForms (mem_p1MinusForms_of_space _)).continuous
    rw [simplexIntegral_sub hc1.continuousOn hc2.continuousOn,
      simplexIntegral_globalInterp k _ T hgT hg, le_div_iff₀ hsq, mul_comm]
    exact sqrt_mul_abs_dof_err_le hA0 hA hp hγ2 hu hs T hgT hg
  have hzb : ∀ y ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ∀ s,
      |z y s| ≤ B * (C₁ * γ * √L / √h ^ n) := by
    intro y hy s
    have h1 := hB.apply T.2 hz hD0 hdof hy s
    have hhk : 0 < h ^ k := pow_pos hh k
    refine le_of_mul_le_mul_left (h1.trans (le_of_eq ?_)) hhk
    simp only [D]; field_simp; simp only [h]; ring
  have hhn : h ^ n = (√h ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hh.le]
  calc ∑ s : formIdx n k, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, (z y s.1) ^ 2
      ≤ 2 ^ n * (h ^ n * (B * (C₁ * γ * √L / √h ^ n)) ^ 2) :=
        sum_integral_sq_le_of_abs_le T.2 (isAffineField_of_mem_p1MinusForms hz).continuous hzb
    _ = 2 ^ n * (B * C₁ * γ) ^ 2 * (√L) ^ 2 := by
        rw [hhn]; field_simp
    _ = 2 ^ n * (B * C₁ * γ) ^ 2 * L := by rw [Real.sq_sqrt hL0]


/-- **`Q_N` is close to the identity on `Vₕ`**:
`‖v - Q_N v‖² ≤ 2ⁿ (B C₁ γ)² 6ⁿ n! ‖v‖²`, `C₁ = 3 (k + 1) 2ⁿ k! 2^{k+1} A`. -/
theorem norm_sq_sub_smoothedInterp_le {N k : ℕ} {A B : ℝ} (hA0 : 0 ≤ A) (hA : InvBound n k A)
    (hB : DofBound n k B) {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm γ N p)
    (hγ2 : γ ≤ 1 / 2) {u : (whitneyElement n).Piecewise (mesh n N) k}
    (hu : u ∈ (whitneyElement n).globalSpace (mesh n N) k) (hs : SampleOK γ p u) :
    ‖(whitneyElement n).glue (mesh n N) k u - (whitneyElement n).smoothedInterp (mesh n N)
        p (isOpen_mesh_domain n N).measurableSet k
        ((whitneyElement n).glue (mesh n N) k u)‖ ^ 2 ≤
      2 ^ n * (B * (3 * (k + 1) * 2 ^ n * k.factorial * 2 ^ (k + 1) * A) * γ) ^ 2 *
        ((6 ^ n * n.factorial : ℕ) * ‖(whitneyElement n).glue (mesh n N) k u‖ ^ 2) := by
  set v := (whitneyElement n).glue (mesh n N) k u
  have hQ := (whitneyElement n).smoothedInterp_natCast (mesh n N) p
    (isOpen_mesh_domain n N).measurableSet k v
  set Pw := (whitneyElement n).globalInterp (mesh n N) k (Submodule.inclusion c1Forms_le_contForms
    (smoothForm p (isOpen_mesh_domain n N).measurableSet k v))
  set d : (whitneyElement n).Piecewise (mesh n N) k := u - (Pw : (whitneyElement n).Piecewise (mesh n N) k)
  have hsub : v - (whitneyElement n).smoothedInterp (mesh n N) p
      (isOpen_mesh_domain n N).measurableSet k v = (whitneyElement n).glue (mesh n N) k d := by
    rw [hQ, map_sub]
  rw [hsub]
  exact norm_sq_glue_le_locMass _ v d (by positivity)
    fun T hT => sum_integral_sq_sub_interp_le hA0 hA hB hp hγ2 hu hs ⟨T, hT⟩


/-! ### Assembly: the smoothing estimates -/

/-- Estimates of a commuting map transport along an equality of domains. -/
theorem commutingMapOfEq_estimates {Ω Ω' : Set (Fin n → ℝ)} (h : Ω = Ω') (hΩ : IsOpen Ω)
    (hΩ' : IsOpen Ω') {S : ((deRham ℝ n).maximalComplex hΩ).Subcomplex} (Q : S.CommutingMap)
    {C θ : ℝ} (hb : ∀ i x, ‖Q.Q i x‖ ≤ C * ‖x‖)
    (hc : ∀ i, ∀ v ∈ S.V i, ‖v - Q.Q i v‖ ≤ θ * ‖v‖) :
    (∀ i x, ‖((deRham ℝ n).commutingMapOfEq h hΩ hΩ' Q).Q i x‖ ≤ C * ‖x‖) ∧
    (∀ i, ∀ v ∈ ((deRham ℝ n).maximalSubcomplexOfEq h hΩ hΩ' S).V i,
      ‖v - ((deRham ℝ n).commutingMapOfEq h hΩ hΩ' Q).Q i v‖ ≤ θ * ‖v‖) := by
  subst h; exact ⟨hb, hc⟩

theorem one_le_cov : (1 : ℝ) ≤ 2 ^ n * ((6 ^ n * n.factorial : ℕ) : ℝ) := by
  have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ ((6 ^ n * n.factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
  nlinarith

/-- **Choice of the smoothing scale** `γ`: small against the constants of the local
estimates. -/
theorem sq_le_quarter {S K x : ℝ} (hS : 0 ≤ S) (hK : 1 ≤ K) (hx0 : 0 ≤ x) (hx : x ≤ S) :
    K * (x * (1 / (2 * (1 + S * K)))) ^ 2 ≤ 1 / 4 := by
  have hpos : 0 < 1 + S * K := by nlinarith
  rw [mul_pow, div_pow, one_pow, mul_pow]
  rw [show K * (x ^ 2 * (1 / (2 ^ 2 * (1 + S * K) ^ 2))) = K * x ^ 2 / (4 * (1 + S * K) ^ 2) by
    field_simp; ring]
  rw [div_le_iff₀ (by positivity)]
  have h1 : K * x ^ 2 ≤ K * S ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx 2)
    (by linarith)
  have h2 : K * S ^ 2 ≤ (S * K) ^ 2 := by nlinarith
  nlinarith

theorem norm_sub_smoothedInterp_le_half {N k : ℕ} {A B S K : ℝ} (hA0 : 0 ≤ A)
    (hA : InvBound n k A) (hB0 : 0 ≤ B) (hB : DofBound n k B) (hS : 0 ≤ S)
    (hxS : B * (3 * (k + 1) * 2 ^ n * k.factorial * 2 ^ (k + 1) * A) ≤ S)
    (hK : K = 2 ^ n * ((6 ^ n * n.factorial : ℕ) : ℝ)) (hγe : γ = 1 / (2 * (1 + S * K)))
    {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm γ N p)
    (hγ2 : γ ≤ 1 / 2) {u : (whitneyElement n).Piecewise (mesh n N) k}
    (hu : u ∈ (whitneyElement n).globalSpace (mesh n N) k) (hs : SampleOK γ p u) :
    ‖(whitneyElement n).glue (mesh n N) k u - (whitneyElement n).smoothedInterp (mesh n N)
        p (isOpen_mesh_domain n N).measurableSet k
        ((whitneyElement n).glue (mesh n N) k u)‖ ≤
      1 / 2 * ‖(whitneyElement n).glue (mesh n N) k u‖ := by
  have h := norm_sq_sub_smoothedInterp_le hA0 hA hB hp hγ2 hu hs
  have hK1 : 1 ≤ K := hK ▸ one_le_cov
  have hx0 : 0 ≤ B * (3 * (k + 1) * 2 ^ n * k.factorial * 2 ^ (k + 1) * A) := by positivity
  have hq := sq_le_quarter hS hK1 hx0 hxS
  rw [← hγe] at hq
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) (h.trans ?_)
  calc 2 ^ n * (B * (3 * (k + 1) * 2 ^ n * k.factorial * 2 ^ (k + 1) * A) * γ) ^ 2 *
        (((6 ^ n * n.factorial : ℕ) : ℝ) * ‖(whitneyElement n).glue (mesh n N) k u‖ ^ 2)
      = K * (B * (3 * (k + 1) * 2 ^ n * k.factorial * 2 ^ (k + 1) * A) * γ) ^ 2 *
          ‖(whitneyElement n).glue (mesh n N) k u‖ ^ 2 := by rw [hK]; ring
    _ ≤ 1 / 4 * ‖(whitneyElement n).glue (mesh n N) k u‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hq (sq_nonneg _)
    _ = (1 / 2 * ‖(whitneyElement n).glue (mesh n N) k u‖) ^ 2 := by ring

variable (n) in
/-- **The smoothing scale** `γ`, depending only on `n`: for every admissible parameter at
scale `γ` (either family) and every global Whitney field satisfying the sampling condition,
`‖v - Q_N v‖ ≤ ½ ‖v‖`. -/
theorem exists_gamma :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 / 2 ∧ ∀ (N k : ℕ) (p : SmoothingParam (Fin n → ℝ)), IsAdm γ N p →
      ∀ u ∈ (whitneyElement n).globalSpace (mesh n N) k, SampleOK γ p u →
        ‖(whitneyElement n).glue (mesh n N) k u - (whitneyElement n).smoothedInterp (mesh n N) p
          (isOpen_mesh_domain n N).measurableSet k ((whitneyElement n).glue (mesh n N) k u)‖ ≤
          1 / 2 * ‖(whitneyElement n).glue (mesh n N) k u‖ := by
  classical
  choose A hA0 hA using fun k : ℕ => exists_invBound (n := n) k
  choose B hB0 hB using fun k : ℕ => exists_dofBound (n := n) k
  set x : ℕ → ℝ := fun k => B k * (3 * (k + 1) * 2 ^ n * k.factorial * 2 ^ (k + 1) * A k)
  have hx0 : ∀ k, 0 ≤ x k := fun k => mul_nonneg (hB0 k) (by have := hA0 k; positivity)
  set S := ∑ k ∈ Finset.range (n + 1), x k
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => hx0 k
  set K : ℝ := 2 ^ n * ((6 ^ n * n.factorial : ℕ) : ℝ)
  have hK : 1 ≤ K := one_le_cov
  set γ := 1 / (2 * (1 + S * K)) with hγe
  have hpos : 0 < 1 + S * K := by nlinarith
  have hγ : 0 < γ := by positivity
  have hγ2 : γ ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  refine ⟨γ, hγ, hγ2, fun N k p hp u hu hs => ?_⟩
  by_cases hk : n < k
  · have := subsingleton_L2F_of_lt (Ω := (mesh n N).domain) hk
    rw [Subsingleton.elim ((whitneyElement n).glue (mesh n N) k u) 0]; simp
  push Not at hk
  have hxk : x k ≤ S := Finset.single_le_sum (fun k _ => hx0 k) (Finset.mem_range.2 (by omega))
  exact norm_sub_smoothedInterp_le_half (hA0 k) (hA k) (hB0 k) (hB k) hS hxk rfl hγe hp hγ2 hu hs

/-- **The maximal family samples only inside `Ω`**, so the sampling condition holds for every
field. -/
theorem sampleOK_pMax {N k : ℕ} (u : (whitneyElement n).Piecewise (mesh n N) k) :
    SampleOK γ (pMax (n := n) γ hγ hγ1 N) u := by
  intro T g hgT hg ξ hξ _ t ht htΩ
  exfalso
  have hxT := simplexMap_faceEnum_mem hgT hg hξ
  have hxc : simplexMap (faceEnum g (k + 1)) ξ ∈ closure (mesh n N).domain :=
    (mesh n N).closedInterior_subset_closure T.2 hxT
  have hp := pMax_isMaximal (n := n) (γ := γ) (hγ := hγ) (hγ1 := hγ1) N
  have := closedBall_dil_subset_of_starBall (starBall_mesh n N)
    (pMax (n := n) γ hγ hγ1 N).half_le_factor hp.factor_lt_one hp.rOut_lt hxc
  rw [← hp.center_eq] at this
  exact htΩ (this (Metric.mem_closedBall.2 ht.le))

/-! ### The minimal family: boundary faces -/

/-- The coordinate hyperplane `{y | yᵢ = c}` as an affine subspace. -/
def coordHyperplane (i : Fin n) (c : ℝ) : AffineSubspace ℝ (Fin n → ℝ) where
  carrier := {y | y i = c}
  smul_vsub_vadd_mem' a p₁ p₂ p₃ h₁ h₂ h₃ := by
    simp only [Set.mem_ofPred_eq] at h₁ h₂ h₃ ⊢
    simp [h₁, h₂, h₃]

/-- A simplex of `ℝⁿ` does not lie in a coordinate hyperplane. -/
theorem not_closedInterior_subset_coordHyperplane (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    (i : Fin n) (c : ℝ) : ¬ T.closedInterior ⊆ {y | y i = c} := by
  intro hsub
  obtain ⟨z, hz⟩ := interior_closedInterior_nonempty T
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isOpen_interior z hz
  have hmem : z + (δ / 2) • (Pi.single i 1 : Fin n → ℝ) ∈ interior T.closedInterior := by
    refine hball ?_
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg (by positivity)]
    have : ‖(Pi.single i 1 : Fin n → ℝ)‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
      by_cases hij : j = i
      · subst hij; simp
      · simp [hij]
    nlinarith
  have h1 := hsub (interior_subset hz)
  have h2 := hsub (interior_subset hmem)
  simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
    mul_one] at h1 h2
  linarith

/-- **A facet in a coordinate hyperplane bounding all the vertices is not an interior facet**:
the apexes of the two cofaces would lie strictly on opposite sides. -/
theorem not_isInteriorFacet_of_coord {M : SimplicialMesh n} {F : Finset (Fin n → ℝ)}
    (i : Fin n) (c ε : ℝ) (hε : ε ≠ 0)
    (hV : ∀ T ∈ M.simplices, ∀ v ∈ vertexSet T, 0 ≤ ε * (v i - c))
    (hF0 : ∀ v ∈ F, v i = c) : ¬ M.IsInteriorFacet F := by
  classical
  rintro ⟨hF, hcard, horient⟩
  obtain ⟨T₁, T₂, hne, he⟩ := Finset.card_eq_two.1 hcard
  have h₁ : T₁ ∈ M.cofaces F := by rw [he]; simp
  have h₂ : T₂ ∈ M.cofaces F := by rw [he]; simp
  have hFc : F.card = n := hF.1
  -- the apex of a coface lies strictly on the positive side
  have hapex : ∀ T ∈ M.cofaces F, ∃ a ∈ vertexSet T, a ∉ F ∧ 0 < ε * (a i - c) := by
    intro T hT
    obtain ⟨hTM, hFT⟩ := M.mem_cofaces.1 hT
    obtain ⟨j, hj, hjF⟩ := exists_apex hFT hFc
    refine ⟨T.points j, points_mem_vertexSet T j, hj, ?_⟩
    rcases (hV T hTM _ (points_mem_vertexSet T j)).lt_or_eq with h | h
    · exact h
    · exfalso
      have hji : T.points j i = c := by
        rcases mul_eq_zero.1 h.symm with h' | h'
        · exact absurd h' hε
        · linarith
      refine not_closedInterior_subset_coordHyperplane T i c ?_
      rw [← Affine.Simplex.convexHull_eq_closedInterior]
      refine convexHull_min ?_ ?_
      · rintro _ ⟨l, rfl⟩
        by_cases hl : l = j
        · subst hl; exact hji
        · exact hF0 _ (hjF l hl)
      · intro y hy z hz a b ha hb hab
        simp only [Set.mem_ofPred_eq] at hy hz ⊢
        simp [hy, hz, ← add_mul, hab]
  obtain ⟨a, ha, haF, ha0⟩ := hapex T₁ h₁
  obtain ⟨a', ha', ha'F, ha'0⟩ := hapex T₂ h₂
  have hs := horient T₁ h₁ T₂ h₂ hne a ha haF a' ha' ha'F
  obtain ⟨⟨p₁, hp₁, p₂, hp₂, hray⟩, -, -⟩ := hs
  have hspan : affineSpan ℝ (F : Set (Fin n → ℝ)) ≤ coordHyperplane i c :=
    affineSpan_le.2 fun v hv => hF0 v hv
  have hp₁i : p₁ i = c := hspan hp₁
  have hp₂i : p₂ i = c := hspan hp₂
  have hx : a -ᵥ p₁ ≠ 0 := fun h0 => by
    have := congrFun h0 i
    simp only [vsub_eq_sub, Pi.sub_apply, Pi.zero_apply, hp₁i] at this
    rw [show a i = c by linarith] at ha0; simp at ha0
  have hy : p₂ -ᵥ a' ≠ 0 := fun h0 => by
    have := congrFun h0 i
    simp only [vsub_eq_sub, Pi.sub_apply, Pi.zero_apply, hp₂i] at this
    rw [show a' i = c by linarith] at ha'0; simp at ha'0
  obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := hray.exists_pos hx hy
  have := congrFun hr i
  simp only [vsub_eq_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hp₁i, hp₂i] at this
  have e1 : 0 < r₁ * (ε * (a i - c)) := mul_pos hr₁ ha0
  have e2 : 0 < r₂ * (ε * (a' i - c)) := mul_pos hr₂ ha'0
  have : r₁ * (ε * (a i - c)) = -(r₂ * (ε * (a' i - c))) := by
    have h3 : ε * (r₁ * (a i - c)) = ε * (r₂ * (c - a' i)) := by rw [this]
    linarith [h3]
  linarith

theorem kuhnVertex_mul_swap {σ : Equiv.Perm (Fin n)} {a b : Fin n} {j : Fin (n + 1)}
    (h : ∀ c : Fin n, ((Equiv.swap a b c : ℕ) < j ↔ (c : ℕ) < j)) :
    kuhnVertex (σ * Equiv.swap a b) j = kuhnVertex σ j := by
  funext l
  simp only [kuhnVertex, Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap]
  have := h (σ.symm l)
  by_cases h1 : ((Equiv.swap a b (σ.symm l) : Fin n) : ℕ) < j
  · simp only [h1, this.1 h1, ite_true]
  · simp only [h1, mt this.2 h1, ite_false]

theorem apply_mem_Icc_of_mem_vertexSet {N : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) {v : Fin n → ℝ} (hv : v ∈ vertexSet T) (i : Fin n) :
    0 ≤ v i ∧ v i ≤ 1 / 2 := by
  have h := (mesh n N).closedInterior_subset_closure hT (vertexSet_subset_closedInterior T hv)
  rw [mesh_domain, closure_cubeDomain] at h
  exact h i (Set.mem_univ i)

theorem isBoundaryFacet_of_coord {N : ℕ} {F : Finset (Fin n → ℝ)}
    (hF : F ∈ (mesh n N).facets) (i : Fin n) (c ε : ℝ) (hε : ε ≠ 0)
    (hV : ∀ T ∈ (mesh n N).simplices, ∀ v ∈ vertexSet T, 0 ≤ ε * (v i - c))
    (hF0 : ∀ v ∈ F, v i = c) : (mesh n N).IsBoundaryFacet F :=
  ((mesh n N).isInteriorFacet_or_isBoundaryFacet hF).resolve_left
    (not_isInteriorFacet_of_coord i c ε hε hV hF0)

theorem cubeSimplex_points_apply (N : ℕ) (m : Fin n → Fin (N + 1)) (σ : Equiv.Perm (Fin n))
    (j : Fin (n + 1)) (i : Fin n) :
    (cubeSimplex N m σ).points j i = hN N * ((m i : ℕ) + kuhnVertex σ j i) := by
  rw [cubeSimplex_points]; simp [finLattice]

/-- **A face in the lower face `{yᵢ = 0}` of the cube lies in a boundary facet**. -/
theorem exists_boundaryFacet_of_lower {N : ℕ} (m : Fin n → Fin (N + 1)) (σ : Equiv.Perm (Fin n))
    (i : Fin n) {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet (cubeSimplex N m σ))
    (hg0 : ∀ v ∈ g, v i = 0) (hgne : g.Nonempty) :
    ∃ T'' ∈ (mesh n N).simplices, ∃ F, (mesh n N).IsBoundaryFacet F ∧
      F ⊆ vertexSet T'' ∧ g ⊆ F := by
  classical
  have hh := hN_pos N
  set p := σ.symm i
  set l : Fin n := ⟨n - 1, by have := i.2; omega⟩
  have hpl : (p : ℕ) ≤ l := by simp only [l]; have := p.2; omega
  -- the vertices of `g` have `j ≤ σ⁻¹ i` and `mᵢ = 0`
  have hvert : ∀ v ∈ g, ∃ j : Fin (n + 1), (cubeSimplex N m σ).points j = v ∧
      (j : ℕ) ≤ p ∧ (m i : ℕ) = 0 := by
    intro v hv
    obtain ⟨j, rfl⟩ := mem_vertexSet.1 (hgT hv)
    have h0 := hg0 _ hv
    rw [cubeSimplex_points_apply] at h0
    have h1 : ((m i : ℕ) : ℝ) + kuhnVertex σ j i = 0 := by
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h hh.ne'
      · exact h
    have hk : 0 ≤ kuhnVertex σ j i := by unfold kuhnVertex; split_ifs <;> norm_num
    have hm0 : ((m i : ℕ) : ℝ) = 0 := by linarith [(Nat.cast_nonneg (m i : ℕ) : (0 : ℝ) ≤ _)]
    have hk0 : kuhnVertex σ j i = 0 := by linarith
    refine ⟨j, rfl, ?_, by exact_mod_cast hm0⟩
    unfold kuhnVertex at hk0
    split_ifs at hk0 with hlt
    · norm_num at hk0
    · push Not at hlt; exact hlt
  obtain ⟨v₀, hv₀⟩ := hgne
  obtain ⟨-, -, -, hmi⟩ := hvert v₀ hv₀
  set σ'' := σ * Equiv.swap p l
  set T'' := cubeSimplex N m σ''
  have hsame : ∀ j : Fin (n + 1), (j : ℕ) ≤ p → T''.points j = (cubeSimplex N m σ).points j := by
    intro j hj
    rw [cubeSimplex_points, cubeSimplex_points, kuhnVertex_mul_swap]
    intro c
    by_cases hc : c = p
    · subst hc; rw [Equiv.swap_apply_left]; constructor <;> intro h <;> omega
    · by_cases hc' : c = l
      · subst hc'; rw [Equiv.swap_apply_right]; constructor <;> intro h <;> omega
      · rw [Equiv.swap_apply_of_ne_of_ne hc hc']
  set F := (vertexSet T'').erase (T''.points (Fin.last n))
  have hFT : F ⊆ vertexSet T'' := Finset.erase_subset _ _
  have hFc : F.card = n := by
    rw [Finset.card_erase_of_mem (points_mem_vertexSet _ _), card_vertexSet]; rfl
  have hσi : (σ''.symm i : ℕ) = n - 1 := by
    simp only [σ'', Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap, p]
    rw [Equiv.swap_apply_left]
  have hF0 : ∀ v ∈ F, v i = 0 := by
    intro v hv
    obtain ⟨hvne, hvT⟩ := Finset.mem_erase.1 hv
    obtain ⟨j, rfl⟩ := mem_vertexSet.1 hvT
    have hj : j ≠ Fin.last n := fun h => hvne (by rw [h])
    have hjn : (j : ℕ) < n := by
      have := j.2; have : (j : ℕ) ≠ n := fun h => hj (Fin.ext h); omega
    rw [cubeSimplex_points_apply]
    simp only [kuhnVertex, hσi, hmi]
    simp [show ¬ (n - 1 < (j : ℕ)) by omega]
  refine ⟨T'', cubeSimplex_mem N m σ'', F, ?_, hFT, ?_⟩
  · refine isBoundaryFacet_of_coord ⟨hFc, T'', cubeSimplex_mem N m σ'', hFT⟩ i 0 1 one_ne_zero
      (fun T hT v hv => ?_) hF0
    have := (apply_mem_Icc_of_mem_vertexSet hT hv i).1; linarith
  · intro v hv
    obtain ⟨j, rfl, hjp, -⟩ := hvert v hv
    refine Finset.mem_erase.2 ⟨fun he => ?_, ?_⟩
    · rw [← hsame j hjp] at he
      have := congrArg (fun x : Fin (n + 1) => (x : ℕ)) (T''.independent.injective he)
      simp only [Fin.val_last] at this
      have : (p : ℕ) < n := p.2
      omega
    · rw [← hsame j hjp]; exact points_mem_vertexSet _ _

/-- **A face in the upper face `{yᵢ = ½}` of the cube lies in a boundary facet**. -/
theorem exists_boundaryFacet_of_upper {N : ℕ} (m : Fin n → Fin (N + 1)) (σ : Equiv.Perm (Fin n))
    (i : Fin n) {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet (cubeSimplex N m σ))
    (hg0 : ∀ v ∈ g, v i = 1 / 2) (hgne : g.Nonempty) :
    ∃ T'' ∈ (mesh n N).simplices, ∃ F, (mesh n N).IsBoundaryFacet F ∧
      F ⊆ vertexSet T'' ∧ g ⊆ F := by
  classical
  have hh := hN_pos N
  have hhN : hN N * ((N : ℝ) + 1) = 1 / 2 := by
    unfold hN; push_cast; field_simp
  set p := σ.symm i
  set o : Fin n := ⟨0, by have := i.2; omega⟩
  have hvert : ∀ v ∈ g, ∃ j : Fin (n + 1), (cubeSimplex N m σ).points j = v ∧
      (p : ℕ) < j ∧ (m i : ℕ) = N := by
    intro v hv
    obtain ⟨j, rfl⟩ := mem_vertexSet.1 (hgT hv)
    have h0 := hg0 _ hv
    rw [cubeSimplex_points_apply, ← hhN] at h0
    have h1 : ((m i : ℕ) : ℝ) + kuhnVertex σ j i = N + 1 :=
      mul_left_cancel₀ hh.ne' h0
    have hk : kuhnVertex σ j i ≤ 1 := by unfold kuhnVertex; split_ifs <;> norm_num
    have hmN : ((m i : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 (m i).2
    have hmi : ((m i : ℕ) : ℝ) = N := by linarith
    have hk1 : kuhnVertex σ j i = 1 := by linarith
    refine ⟨j, rfl, ?_, by exact_mod_cast hmi⟩
    unfold kuhnVertex at hk1
    split_ifs at hk1 with hlt
    · exact hlt
    · norm_num at hk1
  obtain ⟨v₀, hv₀⟩ := hgne
  obtain ⟨-, -, -, hmi⟩ := hvert v₀ hv₀
  set σ'' := σ * Equiv.swap o p
  set T'' := cubeSimplex N m σ''
  have hsame : ∀ j : Fin (n + 1), (p : ℕ) < j → T''.points j = (cubeSimplex N m σ).points j := by
    intro j hj
    rw [cubeSimplex_points, cubeSimplex_points, kuhnVertex_mul_swap]
    intro c
    by_cases hc : c = o
    · subst hc; rw [Equiv.swap_apply_left]; simp only [o]; constructor <;> intro h <;> omega
    · by_cases hc' : c = p
      · subst hc'; rw [Equiv.swap_apply_right]; simp only [o]; constructor <;> intro h <;> omega
      · rw [Equiv.swap_apply_of_ne_of_ne hc hc']
  set F := (vertexSet T'').erase (T''.points 0)
  have hFT : F ⊆ vertexSet T'' := Finset.erase_subset _ _
  have hFc : F.card = n := by
    rw [Finset.card_erase_of_mem (points_mem_vertexSet _ _), card_vertexSet]; rfl
  have hσi : (σ''.symm i : ℕ) = 0 := by
    simp only [σ'', Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap, p]
    rw [Equiv.swap_apply_right]
  have hF0 : ∀ v ∈ F, v i = 1 / 2 := by
    intro v hv
    obtain ⟨hvne, hvT⟩ := Finset.mem_erase.1 hv
    obtain ⟨j, rfl⟩ := mem_vertexSet.1 hvT
    have hj : j ≠ 0 := fun h => hvne (by rw [h])
    have hj0 : 0 < (j : ℕ) := by
      rcases Nat.eq_zero_or_pos (j : ℕ) with h | h
      · exact absurd (Fin.ext h) hj
      · exact h
    rw [cubeSimplex_points_apply]
    simp only [kuhnVertex, hσi, hmi]
    simp only [hj0, ite_true, ← hhN]
  refine ⟨T'', cubeSimplex_mem N m σ'', F, ?_, hFT, ?_⟩
  · refine isBoundaryFacet_of_coord ⟨hFc, T'', cubeSimplex_mem N m σ'', hFT⟩ i (1 / 2) (-1)
      (by norm_num) (fun T hT v hv => ?_) hF0
    have := (apply_mem_Icc_of_mem_vertexSet hT hv i).2; linarith
  · intro v hv
    obtain ⟨j, rfl, hjp, -⟩ := hvert v hv
    refine Finset.mem_erase.2 ⟨fun he => ?_, ?_⟩
    · rw [← hsame j hjp] at he
      have := congrArg (fun x : Fin (n + 1) => (x : ℕ)) (T''.independent.injective he)
      simp only [Fin.val_zero] at this
      omega
    · rw [← hsame j hjp]; exact points_mem_vertexSet _ _

/-- Points of a face of a mesh simplex with weights `≥ θ` are `θ`-separated in lattice
coordinates. -/
theorem isSep_inv_smul_of_face {N : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) {k : ℕ} {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet T)
    (hg : g.card = k + 1) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) {μ : Fin (k + 1) → ℝ}
    (hμ : ∀ a, θ ≤ μ a) (hμ1 : ∑ a, μ a = 1) :
    IsSep θ ((hN N)⁻¹ • ∑ a, μ a • faceEnum g (k + 1) a) := by
  classical
  set q := faceEnum g (k + 1)
  have hqT : ∀ a, q a ∈ vertexSet T := fun a => hgT (by
    have : q a ∈ Set.range q := ⟨a, rfl⟩
    rwa [range_faceEnum hg] at this)
  obtain ⟨m, σ, rfl⟩ := mem_mesh_simplices.1 hT
  have hj : ∀ a, ∃ j, q a = hN N • (latticePoint (finLattice m) + kuhnVertex σ j) := fun a => by
    obtain ⟨j, hj⟩ := mem_vertexSet.1 (hqT a)
    exact ⟨j, by rw [← hj, cubeSimplex_points]⟩
  choose j hj using hj
  have hxs : (hN N)⁻¹ • ∑ a, μ a • q a =
      latticePoint (finLattice m) + ∑ a, μ a • kuhnVertex σ (j a) := by
    have hh := hN_ne_zero N
    simp only [hj, Finset.smul_sum, smul_smul, smul_add, Finset.sum_add_distrib,
      ← Finset.sum_smul]
    have e1 : (hN N)⁻¹ * ∑ i, μ i * hN N = 1 := by
      rw [← Finset.sum_mul, hμ1]; field_simp
    have e2 : ∀ a, (hN N)⁻¹ * (μ a * hN N) = μ a := fun a => by field_simp
    simp only [e1, e2, one_smul]
  rw [hxs]
  exact isSep_latticePoint_add_sum hθ0.le hθ (finLattice m) σ j hμ hμ1

theorem eq_of_sum_smul_apply_eq {k : ℕ} {μ : Fin (k + 1) → ℝ} (hμ : ∀ a, 0 < μ a)
    (hμ1 : ∑ a, μ a = 1) {q : Fin (k + 1) → Fin n → ℝ} {i : Fin n} {c : ℝ}
    (hq : ∀ a, 0 ≤ (q a i - c)) (hx : (∑ a, μ a • q a) i = c) (a : Fin (k + 1)) :
    q a i = c := by
  have h : ∑ b, μ b * (q b i - c) = 0 := by
    have : (∑ a, μ a • q a) i = ∑ b, μ b * q b i := by simp [Finset.sum_apply]
    rw [this] at hx
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hμ1, one_mul, hx, sub_self]
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun b _ => mul_nonneg (hμ b).le (hq b)).1 h a
    (Finset.mem_univ a)
  rcases mul_eq_zero.1 h0 with h' | h'
  · exact absurd h' (hμ a).ne'
  · linarith

/-- **The minimal family satisfies the sampling condition on `V̊ₕ`**: a sample outside `Ω` near a
point of a face with weights `≥ γ` forces the face to lie in a boundary facet, where the DOFs of
fields with vanishing boundary DOFs vanish. -/
theorem sampleOK_pMin (hγ2 : γ ≤ 1 / 2) {N k : ℕ} {u : (whitneyElement n).Piecewise (mesh n N) k}
    (hu : u ∈ (whitneyElement n).globalSpace₀ (mesh n N) k) :
    SampleOK γ (pMin (n := n) γ hγ N) u := by
  classical
  intro T g hgT hg ξ hξ hgood t ht htΩ
  have hp := pMin_isAdm (n := n) (γ := γ) (hγ := hγ) N
  have hh := hN_pos N
  set h := hN N
  set q := faceEnum g (k + 1)
  set x := simplexMap q ξ
  have hμ : ∀ a, γ ≤ refBary ξ a := by
    intro a; by_contra hlt; push Not at hlt; exact hgood ⟨a, hlt⟩
  have hx : x = ∑ a, refBary ξ a • q a := simplexMap_eq_sum q ξ
  have hxT : x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior :=
    simplexMap_faceEnum_mem hgT hg hξ
  have hxc : x ∈ closure (cubeDomain n) := by
    rw [← mesh_domain n N]; exact (mesh n N).closedInterior_subset_closure T.2 hxT
  have hxt : ‖x - t‖ < γ * h / 2 := by
    have hŷ := hp.norm_dil_sub_le hxc
    have h1 : ‖(pMin (n := n) γ hγ N).center + (pMin (n := n) γ hγ N).factor •
        (x - (pMin (n := n) γ hγ N).center) - t‖ < γ * h / 32 := by
      rw [← dist_eq_norm, dist_comm, ← hp.rOut_eq]; exact ht
    calc ‖x - t‖ = ‖(x - ((pMin (n := n) γ hγ N).center + (pMin (n := n) γ hγ N).factor •
          (x - (pMin (n := n) γ hγ N).center))) + (((pMin (n := n) γ hγ N).center +
            (pMin (n := n) γ hγ N).factor • (x - (pMin (n := n) γ hγ N).center)) - t)‖ := by
          congr 1; abel
      _ ≤ _ := norm_add_le _ _
      _ < γ * h / 4 + γ * h / 32 := by
          rw [norm_sub_rev] at hŷ; exact add_lt_add_of_le_of_lt hŷ h1
      _ ≤ γ * h / 2 := by nlinarith
  have hsep := isSep_inv_smul_of_face T.2 hgT hg hγ hγ2 hμ (sum_refBary ξ)
  rw [← hx] at hsep
  have hqT : ∀ a, q a ∈ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n) := fun a => hgT (by
    have : q a ∈ Set.range q := ⟨a, rfl⟩
    rwa [range_faceEnum hg] at this)
  have hgq : ∀ v ∈ g, ∃ a, q a = v := fun v hv => by
    have : v ∈ Set.range q := by rw [range_faceEnum hg]; exact hv
    exact this
  have hμp : ∀ a, 0 < refBary ξ a := fun a => hγ.trans_le (hμ a)
  -- `t ∉ Ω`: some coordinate leaves `(0, ½)`
  obtain ⟨i, hi⟩ : ∃ i, ¬ (0 < t i ∧ t i < 1 / 2) := by
    by_contra hcon; push Not at hcon
    exact htΩ (by rw [mesh_domain]; exact fun i _ => hcon i)
  have hxi : |x i - t i| < γ * h / 2 := by
    have := norm_le_pi_norm (x - t) i
    rw [Real.norm_eq_abs, Pi.sub_apply] at this
    exact this.trans_lt hxt
  rw [abs_lt] at hxi
  have hxbox := hxc
  rw [closure_cubeDomain] at hxbox
  have hx01 := hxbox i (Set.mem_univ i)
  have hXi : ((hN N)⁻¹ • x) i = x i / h := by
    simp [div_eq_inv_mul, h]
  obtain ⟨m, σ, hmσ⟩ := mem_mesh_simplices.1 T.2
  have hgT' : g ⊆ vertexSet (cubeSimplex N m σ) := by rw [hmσ]; exact hgT
  have hgne : g.Nonempty := Finset.card_pos.1 (by rw [hg]; omega)
  obtain ⟨T'', hT'', F, hF, hFT'', hgF⟩ : ∃ T'' ∈ (mesh n N).simplices, ∃ F,
      (mesh n N).IsBoundaryFacet F ∧ F ⊆ vertexSet T'' ∧ g ⊆ F := by
    by_cases hlow : t i ≤ 0
    · -- the lower face
      have hx0 : x i = 0 := by
        rcases hsep.1 i 0 with e | e
        · rw [hXi] at e; push_cast at e
          rcases (div_eq_zero_iff.1 e) with e' | e'
          · exact e'
          · exact absurd e' hh.ne'
        · exfalso
          rw [hXi] at e; push_cast at e
          rw [sub_zero, abs_of_nonneg (div_nonneg hx01.1 hh.le), le_div_iff₀ hh] at e
          nlinarith
      refine exists_boundaryFacet_of_lower m σ i hgT' (fun v hv => ?_) hgne
      obtain ⟨a, rfl⟩ := hgq v hv
      refine eq_of_sum_smul_apply_eq hμp (sum_refBary ξ) (fun b => ?_) (by rw [← hx]; exact hx0) a
      have := (apply_mem_Icc_of_mem_vertexSet T.2 (hqT b) i).1; linarith
    · -- the upper face
      have hup : 1 / 2 ≤ t i := by
        by_contra h'; push Not at h'; exact hi ⟨by push Not at hlow; exact hlow, h'⟩
      have hhN : h * ((N : ℝ) + 1) = 1 / 2 := by
        simp only [h]; unfold hN; push_cast; field_simp
      have hx1 : x i = 1 / 2 := by
        rcases hsep.1 i (N + 1) with e | e
        · rw [hXi] at e; push_cast at e
          rw [div_eq_iff hh.ne'] at e; rw [e, mul_comm]; exact hhN
        · exfalso
          rw [hXi] at e; push_cast at e
          have hx2 := hx01.2
          have hle : x i / h ≤ N + 1 := by
            rw [div_le_iff₀ hh]; linarith [hhN, mul_comm h ((N : ℝ) + 1)]
          have hgt : (N : ℝ) + 1 - γ / 2 < x i / h := by
            rw [lt_div_iff₀ hh]
            have : (N : ℝ) + 1 - γ / 2 = ((N : ℝ) + 1) - γ / 2 := rfl
            nlinarith [hhN, mul_comm h ((N : ℝ) + 1)]
          rw [abs_of_nonpos (by linarith)] at e
          linarith
      refine exists_boundaryFacet_of_upper m σ i hgT' (fun v hv => ?_) hgne
      obtain ⟨a, rfl⟩ := hgq v hv
      have h1 := eq_of_sum_smul_apply_eq (q := fun a => -q a) (i := i) (c := -(1 / 2)) hμp
        (sum_refBary ξ)
        (fun b => by have := (apply_mem_Icc_of_mem_vertexSet T.2 (hqT b) i).2; simp; linarith)
        (by
          have : (∑ a, refBary ξ a • -q a) = -(∑ a, refBary ξ a • q a) := by
            simp [Finset.sum_neg_distrib]
          rw [this, ← hx, Pi.neg_apply, hx1]) a
      simp only [Pi.neg_apply, neg_inj] at h1
      exact h1
  -- the boundary DOFs vanish
  have h0 := hu.2 ⟨T'', hT''⟩ F hF hFT'' g hgF (⟨(), hg⟩ : WhitneyDofIdx g k)
  rw [simplexIntegral_localDof ⟨T'', hT''⟩ hg] at h0
  rw [simplexIntegral_eq_of_mem_globalSpace hu.1 T ⟨T'', hT''⟩ hgT (hgF.trans hFT'') hg]
  exact h0

theorem smoothedCommutingMapMin_Q {M : SimplicialMesh n} [NeZero n] (p : SmoothingParam (Fin n → ℝ))
    (hΩo : IsOpen M.domain) (hb : Bornology.IsBounded M.domain) {x₀ : Fin n → ℝ} {s₀ : ℝ}
    (hstar : ∀ y ∈ M.domain, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ M.domain)
    (hp : p.IsMinimal x₀ s₀) (y₀ : Fin n → ℝ)
    (hstar' : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → y₀ + t • (x - y₀) ∈ M.domain)
    (i : ℤ) :
    ((whitneyElement n).smoothedCommutingMapMin M p hΩo hb hstar hp y₀ hstar').Q i =
      (whitneyElement n).smoothedInterp M p hΩo.measurableSet i := rfl

/-- Estimates of a commuting map into a subcomplex of the minimal complex transport along an
equality of domains. -/
theorem commutingMapOfEqMin_estimates {Ω Ω' : Set (Fin n → ℝ)} (h : Ω = Ω') (hΩ : IsOpen Ω)
    (hΩ' : IsOpen Ω') {S : ((deRham ℝ n).minimalComplex hΩ).Subcomplex} (Q : S.CommutingMap)
    {C θ : ℝ} (hb : ∀ i x, ‖Q.Q i x‖ ≤ C * ‖x‖)
    (hc : ∀ i, ∀ v ∈ S.V i, ‖v - Q.Q i v‖ ≤ θ * ‖v‖) :
    (∀ i x, ‖((deRham ℝ n).commutingMapOfEqMin h hΩ hΩ' Q).Q i x‖ ≤ C * ‖x‖) ∧
    (∀ i, ∀ v ∈ ((deRham ℝ n).minimalSubcomplexOfEq h hΩ hΩ' S).V i,
      ‖v - ((deRham ℝ n).commutingMapOfEqMin h hΩ hΩ' Q).Q i v‖ ≤ θ * ‖v‖) := by
  subst h; exact ⟨hb, hc⟩

variable [NeZero n]

/-- **The smoothed-projection estimates hold on the Freudenthal meshes of the cube**
([AFW2010], §5.4; [ChristiansenWinther2008]): for the parameters `pMax γ` (dilation factor
`1 - γ h_N` about the centre, bump radii `γ h_N / 64 < γ h_N / 32`) with `γ` small depending only on
`n`, the smoothed interpolants `Q_N = Π_h R_N` are bounded in `L²` uniformly in `N`, and
`‖v - Q_N v‖ ≤ ½ ‖v‖` on the Whitney spaces. -/
theorem smoothingEstimates_pMax :
    ∃ (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (C : ℝ), SmoothingEstimates n (pMax γ hγ hγ1) C := by
  obtain ⟨γ, hγ, hγ2, hclose⟩ := exists_gamma n
  have hγ1 : γ ≤ 1 := by linarith
  obtain ⟨C, hC0, hbound⟩ := exists_norm_smoothedInterp_le (n := n) hγ hγ1
  refine ⟨γ, hγ, hγ1, max C (1 / 2), ?_⟩
  have hest : ∀ N, (∀ i x, ‖(smoothed n N (pMax γ hγ hγ1 N) (pMax_isMaximal N)).Q i x‖ ≤
      max C (1 / 2) * ‖x‖) ∧ (∀ i, ∀ v ∈ (whitney n N).V i,
        ‖v - (smoothed n N (pMax γ hγ hγ1 N) (pMax_isMaximal N)).Q i v‖ ≤ 1 / 2 * ‖v‖) := by
    intro N
    refine commutingMapOfEq_estimates (mesh_domain n N) (isOpen_mesh_domain n N)
      (isOpen_cubeDomain n) _ (fun i x => ?_) (fun i v hv => ?_)
    · rw [LocalElement.smoothedCommutingMap_Q]
      rcases i with k | k
      · exact (hbound N k _ (pMax_isAdm N) x).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      · have h0 : ∀ y : L2F ℝ (mesh n N).domain (formIdx n (Int.negSucc k)), ‖y‖ = 0 := fun y => by
          have := LocalElement.subsingleton_L2F_negSucc (mesh n N).domain (n := n) k
          rw [Subsingleton.elim y 0, norm_zero]
        exact (h0 _).le.trans (by positivity)
    · rw [LocalElement.smoothedCommutingMap_Q]
      rcases i with k | k
      · obtain ⟨u, rfl⟩ := hv
        exact hclose N k _ (pMax_isAdm N) u.1 u.2 (sampleOK_pMax _)
      · have h0 : ∀ y : L2F ℝ (mesh n N).domain (formIdx n (Int.negSucc k)), ‖y‖ = 0 := fun y => by
          have := LocalElement.subsingleton_L2F_negSucc (mesh n N).domain (n := n) k
          rw [Subsingleton.elim y 0, norm_zero]
        exact (h0 _).le.trans (by positivity)
  exact ⟨fun N => pMax_isMaximal N, le_max_right _ _, fun N => (hest N).1,
    fun N => (hest N).2⟩

/-- **The smoothed-projection estimates hold on the Freudenthal meshes of the cube**, as an
existence statement over the parameters (`smoothingEstimates_pMax` with the parameters `pMax γ`
made explicit). -/
theorem smoothingEstimates_exists :
    ∃ (p : ℕ → SmoothingParam (Fin n → ℝ)) (C : ℝ), SmoothingEstimates n p C := by
  obtain ⟨γ, hγ, hγ1, C, h⟩ := smoothingEstimates_pMax (n := n)
  exact ⟨_, C, h⟩


/-- **The smoothed-projection estimates with vanishing boundary DOFs hold on the Freudenthal
meshes of the cube** ([AFW2010], §5.4; [ChristiansenWinther2008]): for the parameters `pMin γ`
(dilation factor `1 + γ h_N` towards the centre, bump radii `γ h_N / 64 < γ h_N / 32`) with `γ`
small depending only on `n`, the smoothed interpolants `Q̊_N = Π_h R_N` of the Whitney complexes
with vanishing boundary DOFs are bounded in `L²` uniformly in `N`, and `‖v - Q̊_N v‖ ≤ ½ ‖v‖`
on `V̊ₕ`. The samples of the smoother outside `Q` only meet faces lying in boundary facets, where
the DOFs of `V̊ₕ` vanish (`sampleOK_pMin`). -/
theorem smoothingEstimatesMin_pMin :
    ∃ (γ : ℝ) (hγ : 0 < γ) (C : ℝ), SmoothingEstimatesMin n (pMin γ hγ) C := by
  obtain ⟨γ, hγ, hγ2, hclose⟩ := exists_gamma n
  have hγ1 : γ ≤ 1 := by linarith
  obtain ⟨C, hC0, hbound⟩ := exists_norm_smoothedInterp_le (n := n) hγ hγ1
  refine ⟨γ, hγ, max C (1 / 2), ?_⟩
  have hest : ∀ N, (∀ i x, ‖(smoothedMin n N (pMin γ hγ N) (pMin_isMinimal N)).Q i x‖ ≤
      max C (1 / 2) * ‖x‖) ∧ (∀ i, ∀ v ∈ (whitneyMin n N).V i,
        ‖v - (smoothedMin n N (pMin γ hγ N) (pMin_isMinimal N)).Q i v‖ ≤ 1 / 2 * ‖v‖) := by
    intro N
    refine commutingMapOfEqMin_estimates (mesh_domain n N) (isOpen_mesh_domain n N)
      (isOpen_cubeDomain n) _ (fun i x => ?_) (fun i v hv => ?_)
    · rw [smoothedCommutingMapMin_Q]
      rcases i with k | k
      · exact (hbound N k _ (pMin_isAdm N) x).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      · have h0 : ∀ y : L2F ℝ (mesh n N).domain (formIdx n (Int.negSucc k)), ‖y‖ = 0 := fun y => by
          have := LocalElement.subsingleton_L2F_negSucc (mesh n N).domain (n := n) k
          rw [Subsingleton.elim y 0, norm_zero]
        exact (h0 _).le.trans (by positivity)
    · rw [smoothedCommutingMapMin_Q]
      rcases i with k | k
      · obtain ⟨u, rfl⟩ := hv
        exact hclose N k _ (pMin_isAdm N) u.1
          ((whitneyElement n).globalSpace₀_le (mesh n N) k u.2) (sampleOK_pMin hγ2 u.2)
      · have h0 : ∀ y : L2F ℝ (mesh n N).domain (formIdx n (Int.negSucc k)), ‖y‖ = 0 := fun y => by
          have := LocalElement.subsingleton_L2F_negSucc (mesh n N).domain (n := n) k
          rw [Subsingleton.elim y 0, norm_zero]
        exact (h0 _).le.trans (by positivity)
  exact ⟨fun N => pMin_isMinimal N, le_max_right _ _, fun N => (hest N).1,
    fun N => (hest N).2⟩

/-- **The smoothed-projection estimates with vanishing boundary DOFs hold on the Freudenthal
meshes of the cube**, as an existence statement over the parameters
(`smoothingEstimatesMin_pMin` with the parameters `pMin γ` made explicit). -/
theorem smoothingEstimatesMin_exists :
    ∃ (p : ℕ → SmoothingParam (Fin n → ℝ)) (C : ℝ), SmoothingEstimatesMin n p C := by
  obtain ⟨γ, hγ, C, h⟩ := smoothingEstimatesMin_pMin (n := n)
  exact ⟨_, C, h⟩


/-- **Uniformly bounded cochain projections onto the Whitney complexes of the cube**
(unconditionally): there is `C` such that for every `N` the Whitney complex of the
level-`(N + 1)` Freudenthal mesh carries a cochain projection bounded by `C` in `L²` and in the
graph norms ([AFW2010], §5.4). -/
theorem exists_uniform_cochainProjection :
    ∃ C : ℝ, ∀ N, ∃ π : (whitney n N).CochainProjection,
      (∀ i x, ‖π.π i x‖ ≤ C * ‖x‖) ∧ ∀ i j, π.IsGraphBounded i j C := by
  obtain ⟨p, C, hE⟩ := smoothingEstimates_exists (n := n)
  exact ⟨2 * C, fun N => ⟨hE.proj N, hE.norm_proj_le N, hE.isGraphBounded_proj N⟩⟩

/-- **Uniformly bounded cochain projections onto the Whitney complexes with vanishing boundary
DOFs** (unconditionally), in `L²` and in the graph norms of `H̊Λ(Q)`. -/
theorem exists_uniform_cochainProjectionMin :
    ∃ C : ℝ, ∀ N, ∃ π : (whitneyMin n N).CochainProjection,
      (∀ i x, ‖π.π i x‖ ≤ C * ‖x‖) ∧ ∀ i j, π.IsGraphBounded i j C := by
  obtain ⟨p, C, hE⟩ := smoothingEstimatesMin_exists (n := n)
  exact ⟨2 * C, fun N => ⟨hE.proj N, hE.norm_proj_le N, hE.isGraphBounded_proj N⟩⟩

end Feec.Models.Cube.FEM
