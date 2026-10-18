module

public import Feec.FiniteElement.InverseEstimate
public import Feec.Models.Cube.FiniteElementMethod

/-!
# The smoothed-projection estimates on the Freudenthal meshes of the cube

**The estimates `FEM.SmoothingEstimates` hold** (`FEM.smoothingEstimates_exists`): for the
maximal-family parameters `pMax γ` (dilation factor `1 - γ h_N` about the centre of
`Q = (0, ½)ⁿ`, bump radii `γ h_N / 64 < γ h_N / 32`, `h_N = 1 / (2 (N + 1))`) with `γ` small
depending only on `n`, the smoothed canonical interpolants `Q_N = Π_h R_N` of the Whitney complexes
of the level-`(N + 1)` Freudenthal meshes are bounded in `L²` uniformly in `N` and satisfy
`‖v - Q_N v‖ ≤ ½ ‖v‖` on the Whitney spaces ([AFW2010], §5.4; [ChristiansenWinther2008]). All the
consequences proved under these estimates in `Feec.Models.Cube.FiniteElementMethod` (uniformly
bounded cochain projections, discrete Poincaré inequality, quasi-optimality, `O(h)` rates) hold
unconditionally for these parameters.

The proof uses that every simplex of the mesh is `h_N (m + K_σ)`, a homothetic copy of one of the
`n!` Kuhn simplices ([Freudenthal1942], [Kuhn1960]), so the inverse estimates of
`Feec.FiniteElement.InverseEstimate` hold with one constant (`DofBound`, `InvBound`).

* **Uniform bound** (`exists_norm_smoothedInterp_le`). On a simplex `T`, the local DOF estimate
  bounds `Q_N x` by the face integrals of the smoothed field, `O(h_Nᵏ sup_T |R x|)`
  (`abs_simplexIntegral_face_le`), and by Jensen's inequality for the mollifier
  `|R x (y)|² ≤ |B(0, rIn)|⁻¹ ∫_{B̄(ŷ, rOut)} |x̄|²` (`abs_smoothForm_le`), so
  `‖Q_N x‖²_{L²(T)} ≲ (32/γ)ⁿ m_T(x)` with the local mass `m_T(x)` of `x` on the
  `2 h_N`-neighbourhood of `T` (`sum_integral_sq_interp_le`). A point lies in at most `6ⁿ n!`
  such neighbourhoods (`card_filter_mem_cthickening_le`, `sum_locMass_le`).
* **Closeness on `Vₕ`** (`exists_gamma`). For `v ∈ Vₕ` and a `k`-face `g` of `T`, the face
  integrand of `v_T - R v` is a mollified average of `Σₛ (v_T(x) - cᵏ v̄(t))ₛ minorₛ`
  (`sum_sub_smoothForm_mul_eq`). At points of `g` whose barycentric coordinates are `≥ γ`, every
  simplex `T'` met by the smoother contains `g` (`subset_vertexSet_of_near`, through the
  separation of the lattice points `isSep_latticePoint_add_sum`,
  `mem_freudenthalSet_of_isSep`, and the face-to-face property); there the traces of `v_T` and
  `v_{T'}` agree (`sum_mul_minor_eq`, `simplexIntegral_eq_of_mem_globalSpace`), and the error is
  `O(γ)` by the inverse estimates. The remaining boundary layer of `g` has measure `O(γ)`
  (`volume_real_nearBdry_le`). Hence `h^{n/2} |∫_g (v_T - R v)| ≲ γ hᵏ m_T(v)^{1/2}`
  (`sqrt_mul_abs_dof_err_le`) and `‖v - Q_N v‖² ≲ γ² ‖v‖²` (`norm_sq_sub_smoothedInterp_le`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.4 (smoothed projections: the estimates for `ε ≈ h`)
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]
* [H. W. Kuhn, *Some combinatorial lemmas in topology*][Kuhn1960]
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

theorem pMax_factor (N : ℕ) : (pMax (n := n) γ hγ hγ1 N).factor = 1 - γ * hN N := rfl

theorem pMax_rOut (N : ℕ) : (pMax (n := n) γ hγ hγ1 N).bump.rOut = γ * hN N / 32 := rfl

theorem pMax_rIn (N : ℕ) : (pMax (n := n) γ hγ hγ1 N).bump.rIn = γ * hN N / 64 := rfl

theorem pMax_center (N : ℕ) : (pMax (n := n) γ hγ hγ1 N).center = center n := rfl

/-- The dilated point is within `γ h_N / 4` of the original point on `cl Q`. -/
theorem norm_dil_sub_le (N : ℕ) {x : Fin n → ℝ} (hx : x ∈ closure (cubeDomain n)) :
    ‖((pMax (n := n) γ hγ hγ1 N).center + (pMax (n := n) γ hγ hγ1 N).factor •
      (x - (pMax (n := n) γ hγ hγ1 N).center)) - x‖ ≤ γ * hN N / 4 := by
  rw [pMax_center, pMax_factor]
  have e : center n + (1 - γ * hN N) • (x - center n) - x = -(γ * hN N) • (x - center n) := by
    rw [sub_smul, one_smul, neg_smul]; abel
  rw [e, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (mul_pos hγ (hN_pos N))]
  have := norm_sub_center_le hx
  have h0 : 0 < γ * hN N := mul_pos hγ (hN_pos N)
  nlinarith

/-! ### The smoothed form at a point -/

theorem smoothForm_apply_eq {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (p : SmoothingParam (Fin n → ℝ)) (k : ℕ) (x : L2F ℝ Ω (formIdx n k)) (y : Fin n → ℝ)
    (s : formIdx n k) :
    (smoothForm p hΩ k x : FormField n) y s.1 = p.factor ^ k *
      ∫ t, Ω.indicator ((x s : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) t *
        p.bump.normed volume (p.center + p.factor • (y - p.center) - t) := by
  rw [smoothForm_apply, formExt_val, smoothCoeff, smoothExt, dil, molli_apply, zpow_natCast]

theorem smoothForm_apply_of_card_ne {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (p : SmoothingParam (Fin n → ℝ)) (k : ℕ) (x : L2F ℝ Ω (formIdx n k)) (y : Fin n → ℝ)
    {s : Finset (Fin n)} (hs : #s ≠ k) : (smoothForm p hΩ k x : FormField n) y s = 0 :=
  isDeg_smoothForm p hΩ k x y s hs

/-- **Pointwise bound of the smoothed form** (`c ≤ 1`):
`|R x (y)ₛ|² ≤ |B(0, rIn)|⁻¹ Σ_{s'} ∫_{B̄(ŷ, rOut)} |x̄_{s'}|²`, `ŷ` the dilated point. -/
theorem abs_smoothForm_le {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (p : SmoothingParam (Fin n → ℝ)) (hc1 : p.factor ≤ 1) (k : ℕ) (x : L2F ℝ Ω (formIdx n k))
    (y : Fin n → ℝ) (s : Finset (Fin n)) :
    |(smoothForm p hΩ k x : FormField n) y s| ≤
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
    have hc : |p.factor ^ k| ≤ 1 := by
      rw [abs_of_pos (pow_pos p.factor_pos k)]; exact pow_le_one₀ p.factor_pos.le hc1
    rw [abs_mul]
    refine (mul_le_of_le_one_left (abs_nonneg _) hc).trans ?_
    rw [← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    refine (sq_integral_mul_normed_le p.bump hf hf2.locallyIntegrable ŷ).trans
      ((integral_sq_mul_normed_le p.bump hf2 ŷ).trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ hMρ
    exact Finset.single_le_sum (f := fun s' : formIdx n k => ∫ t in Metric.closedBall ŷ p.bump.rOut,
      (Ω.indicator ((x s' : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) t) ^ 2) (fun s' _ => hterm s')
      (Finset.mem_univ _)
  · rw [smoothForm_apply_of_card_ne hΩ p k x y hs, abs_zero]
    exact Real.sqrt_nonneg _


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
  rwa [whitneySpace_simplex_eq_p1MinusForms] at this

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

variable (γ hγ hγ1) in
/-- **The local `L²` bound of `Q_N = Π_h R`** on a simplex: `‖Q_N x‖²_{L²(T)} ≲ m_T(x)`. -/
theorem sum_integral_sq_interp_le {N k : ℕ} {B : ℝ} (hB : DofBound n k B)
    (x : L2F ℝ (mesh n N).domain (formIdx n k)) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) :
    ∑ s : formIdx n k, ∫ y in T.closedInterior,
      (((((whitneyElement n).globalInterp (mesh n N) k
        (Submodule.inclusion c1Forms_le_contForms
          (smoothForm (pMax γ hγ hγ1 N) (isOpen_mesh_domain n N).measurableSet k x)) :
          (whitneyElement n).Piecewise (mesh n N) k) ⟨T, hT⟩ : (whitneyElement n).space T k) :
          FormField n) y s.1) ^ 2 ≤
      2 ^ n * (B * 2 ^ n) ^ 2 * (32 / γ) ^ n * locMass x T := by
  set h := hN N
  have hh : 0 < h := hN_pos N
  have hh' : h ≠ 0 := hh.ne'
  set p := pMax (n := n) γ hγ hγ1 N
  set hΩ := (isOpen_mesh_domain n N).measurableSet
  set w := smoothForm p hΩ k x
  set z : FormField n := ((((whitneyElement n).globalInterp (mesh n N) k
    (Submodule.inclusion c1Forms_le_contForms w) :
      (whitneyElement n).Piecewise (mesh n N) k) ⟨T, hT⟩ : (whitneyElement n).space T k) :
        FormField n)
  have hz : z ∈ p1MinusForms n k := mem_p1MinusForms_of_space _
  set L := locMass x T
  have hL := locMass_nonneg x T
  set Mρ := 1 / volume.real (Metric.closedBall (0 : Fin n → ℝ) p.bump.rIn)
  have hMρ : Mρ = (32 / (γ * h)) ^ n := by
    change 1 / volume.real (Metric.closedBall (0 : Fin n → ℝ) (γ * h / 64)) = _
    rw [volume_real_closedBall_zero (by positivity)]
    rw [one_div, ← inv_pow]
    congr 1
    field_simp
    ring
  set A := √(Mρ * L)
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  -- the smoothed field is bounded by `A` on `T`
  have hw : ∀ y ∈ T.closedInterior, ∀ s, |(w : FormField n) y s| ≤ A := by
    intro y hy s
    refine (abs_smoothForm_le hΩ p (by rw [pMax_factor]; nlinarith) k x y s).trans ?_
    refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s' _ => ?_)
      (by positivity))
    refine setIntegral_mono_set (integrable_sq_indicator _).integrableOn
      (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall fun t ht => ?_)
    have hyc : y ∈ closure (cubeDomain n) := by
      rw [← mesh_domain n N]; exact (mesh n N).closedInterior_subset_closure hT hy
    have h1 := norm_dil_sub_le (hγ := hγ) (hγ1 := hγ1) N hyc
    have h2 : dist t (p.center + p.factor • (y - p.center)) ≤ γ * h / 32 := ht
    refine Metric.mem_cthickening_of_dist_le t y _ _ hy ?_
    calc dist t y ≤ dist t (p.center + p.factor • (y - p.center)) +
          dist (p.center + p.factor • (y - p.center)) y := dist_triangle _ _ _
      _ ≤ γ * h / 32 + γ * h / 4 := add_le_add h2 (by rw [dist_eq_norm]; exact h1)
      _ ≤ 2 * h := by nlinarith
  -- its face integrals are `O(hᵏ A)`
  have hdof : ∀ g ⊆ vertexSet T, g.card = k + 1 →
      |simplexIntegral (faceEnum g (k + 1)) z| ≤ 2 ^ n * h ^ k * A := by
    intro g hgT hg
    rw [simplexIntegral_globalInterp k _ ⟨T, hT⟩ hgT hg]
    exact abs_simplexIntegral_face_le hT hgT hg hA0 hw
  -- hence `|z| ≤ B 2ⁿ A` on `T`
  have hzb : ∀ y ∈ T.closedInterior, ∀ s, |z y s| ≤ B * 2 ^ n * A := by
    intro y hy s
    have h1 := hB.apply hT hz (by positivity) hdof hy s
    have hhk : 0 < h ^ k := pow_pos hh k
    have : h ^ k * |z y s| ≤ h ^ k * (B * 2 ^ n * A) := by
      calc h ^ k * |z y s| ≤ B * (2 ^ n * h ^ k * A) := h1
        _ = h ^ k * (B * 2 ^ n * A) := by ring
    exact le_of_mul_le_mul_left this hhk
  have hzc : Continuous z := (isAffineField_of_mem_p1MinusForms hz).continuous
  obtain ⟨m, σ, hmσ⟩ := mem_mesh_simplices.1 hT
  have hloc : ∀ s : formIdx n k, ∫ y in T.closedInterior, (z y s.1) ^ 2 ≤
      h ^ n * (B * 2 ^ n * A) ^ 2 := by
    intro s
    rw [← hmσ]
    refine integral_cubeSimplex_le m σ (f := fun y => (z y s.1) ^ 2)
      (((continuous_apply s.1).comp hzc).pow 2) (fun y hy => ?_) (fun y => sq_nonneg _)
    rw [hmσ] at hy
    have := hzb y hy s.1
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  calc ∑ s : formIdx n k, ∫ y in T.closedInterior, (z y s.1) ^ 2
      ≤ ∑ _s : formIdx n k, h ^ n * (B * 2 ^ n * A) ^ 2 := Finset.sum_le_sum fun s _ => hloc s
    _ = Fintype.card (formIdx n k) * (h ^ n * (B * 2 ^ n * A) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 2 ^ n * (h ^ n * (B * 2 ^ n * A) ^ 2) :=
        mul_le_mul_of_nonneg_right (card_formIdx_le _) (by positivity)
    _ = 2 ^ n * (B * 2 ^ n) ^ 2 * (h ^ n * Mρ) * L := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
    _ = 2 ^ n * (B * 2 ^ n) ^ 2 * (32 / γ) ^ n * L := by
        rw [hMρ, ← mul_pow, show h * (32 / (γ * h)) = 32 / γ by field_simp]


theorem subsingleton_L2F_of_lt {Ω : Set (Fin n → ℝ)} {k : ℕ} (hk : n < k) :
    Subsingleton (L2F ℝ Ω (formIdx n k)) := by
  constructor
  intro x y
  refine PiLp.ext fun s => ?_
  exfalso
  have h1 := s.2
  have h2 : #s.1 ≤ n := by simpa using Finset.card_le_univ s.1
  omega

variable (γ hγ hγ1) in
/-- **The uniform `L²` bound of the smoothed interpolants** `Q_N = Π_h R_N` (maximal family,
parameters `pMax γ`): `‖Q_N x‖ ≤ C ‖x‖` for all `N`, all degrees and all `x`. -/
theorem exists_norm_smoothedInterp_le :
    ∃ C, 0 ≤ C ∧ ∀ (N k : ℕ) (x : L2F ℝ (mesh n N).domain (formIdx n k)),
      ‖(whitneyElement n).smoothedInterp (mesh n N) (pMax γ hγ hγ1 N)
        (isOpen_mesh_domain n N).measurableSet k x‖ ≤ C * ‖x‖ := by
  classical
  choose B hB0 hB using fun k : ℕ => exists_dofBound (n := n) k
  set Cov : ℝ := ((6 ^ n * n.factorial : ℕ) : ℝ)
  set K : ℕ → ℝ := fun k => 2 ^ n * (B k * 2 ^ n) ^ 2 * (32 / γ) ^ n * Cov
  have hK : ∀ k, 0 ≤ K k := fun k => by positivity
  refine ⟨√(∑ k ∈ Finset.range (n + 1), K k), Real.sqrt_nonneg _, fun N k x => ?_⟩
  by_cases hk : n < k
  · have := subsingleton_L2F_of_lt (Ω := (mesh n N).domain) hk
    rw [Subsingleton.elim x 0]
    simp
  push Not at hk
  have hQ := (whitneyElement n).smoothedInterp_natCast (mesh n N) (pMax γ hγ hγ1 N)
    (isOpen_mesh_domain n N).measurableSet k x
  set u := (whitneyElement n).globalInterp (mesh n N) k (Submodule.inclusion c1Forms_le_contForms
    (smoothForm (pMax (n := n) γ hγ hγ1 N) (isOpen_mesh_domain n N).measurableSet k x))
  have h1 := norm_sq_pieceL2_le (mesh n N) (mesh n N).domain (fun T => formComp (k := (k : ℤ))
    ((whitneyElement n).extendPW (mesh n N) (u : (whitneyElement n).Piecewise (mesh n N) k) T))
    (fun T hT s => continuous_formComp ((whitneyElement n).contDiff_extendPW (mesh n N) _
      hT).continuous s)
  have h2 : ∑ T ∈ (mesh n N).simplices, ∑ s : formIdx n k, ∫ y in T.closedInterior,
      (formComp (k := (k : ℤ)) ((whitneyElement n).extendPW (mesh n N)
        (u : (whitneyElement n).Piecewise (mesh n N) k) T) s y) ^ 2 ≤
      ∑ T ∈ (mesh n N).simplices, 2 ^ n * (B k * 2 ^ n) ^ 2 * (32 / γ) ^ n * locMass x T := by
    refine Finset.sum_le_sum fun T hT => ?_
    have e : ∀ s : formIdx n k, ∀ y, formComp (k := (k : ℤ))
        ((whitneyElement n).extendPW (mesh n N) (u : (whitneyElement n).Piecewise (mesh n N) k) T)
          s y = (((u : (whitneyElement n).Piecewise (mesh n N) k) ⟨T, hT⟩ :
            (whitneyElement n).space T k) : FormField n) y s.1 := fun s y => by
      change (whitneyElement n).extendPW (mesh n N) _ T y s.1 = _
      rw [(whitneyElement n).extendPW_of_mem (mesh n N) _ hT]
    simp_rw [e]
    exact sum_integral_sq_interp_le γ hγ hγ1 (hB k) x hT
  have h3 := sum_locMass_le N x
  have hsq : ‖(whitneyElement n).smoothedInterp (mesh n N) (pMax γ hγ hγ1 N)
      (isOpen_mesh_domain n N).measurableSet k x‖ ^ 2 ≤
      (√(∑ k ∈ Finset.range (n + 1), K k) * ‖x‖) ^ 2 := by
    rw [hQ, mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun k _ => hK k)]
    refine h1.trans (h2.trans ?_)
    rw [← Finset.mul_sum]
    calc 2 ^ n * (B k * 2 ^ n) ^ 2 * (32 / γ) ^ n * ∑ T ∈ (mesh n N).simplices, locMass x T
        ≤ 2 ^ n * (B k * 2 ^ n) ^ 2 * (32 / γ) ^ n * (Cov * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = K k * ‖x‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun k _ => hK k)
          (Finset.mem_range.2 (by omega))) (sq_nonneg _)
  exact le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) hsq


/-! ### Ingredients of the closeness estimate -/

/-- The pulled-back integrand of a face integral. -/
theorem simplexIntegral_eq_integral_sum {k : ℕ} (q : Fin (k + 1) → Fin n → ℝ) (ω : FormField n) :
    simplexIntegral q ω = ∫ x in FiniteElement.refSimplex k,
      ∑ s, ω (simplexMap q x) s * wedgeProd (simplexMatrix q) s univ :=
  simplexIntegral_def q ω

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


/-! ### Glued fields almost everywhere -/

/-- **A glued field almost everywhere**: a.e. point of `Ω` lies in the interior of a simplex
`T'`, where the field is the local field of `T'`. -/
theorem ae_glue_eq_local {M : SimplicialMesh n} {k : ℕ} (u : (whitneyElement n).Piecewise M k)
    (hΩ : MeasurableSet M.domain) :
    ∀ᵐ t ∂volume, t ∈ M.domain → ∃ T' : M.simplices,
      t ∈ interior (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior ∧
        ∀ s : formIdx n k, M.domain.indicator
          (((whitneyElement n).glue M k u s : L2 ℝ M.domain) : (Fin n → ℝ) → ℝ) t =
          ((u T' : (whitneyElement n).space T' k) : FormField n) t s.1 := by
  have h1 : ∀ᵐ t ∂volume.restrict M.domain, ∀ s : formIdx n k,
      (((whitneyElement n).glue M k u s : L2 ℝ M.domain) : (Fin n → ℝ) → ℝ) t =
        pieceFun M (fun T => formComp (k := (k : ℤ))
          ((whitneyElement n).extendPW M u T) s) t := by
    rw [ae_all_iff]
    intro s
    exact coeFn_pieceL2 M M.domain _ (fun T hT s => continuous_formComp
      ((whitneyElement n).contDiff_extendPW M u hT).continuous s) s
  have h2 := ae_mem_interior M hΩ
  rw [← ae_restrict_iff' hΩ]
  filter_upwards [h1, h2, ae_restrict_mem hΩ] with t ht1 ht2 htΩ
  obtain ⟨T', hT', htT'⟩ := ht2
  refine ⟨⟨T', hT'⟩, htT', fun s => ?_⟩
  rw [Set.indicator_of_mem htΩ, ht1 s, pieceFun_of_mem_interior M _ hT' htT']
  change (whitneyElement n).extendPW M u T' t s.1 = _
  rw [(whitneyElement n).extendPW_of_mem M u hT']

/-- Sums over `Finset (Fin n)` of terms vanishing off degree `k`. -/
theorem sum_eq_sum_formIdx {k : ℕ} {f : Finset (Fin n) → ℝ} (hf : ∀ s, #s ≠ k → f s = 0) :
    ∑ s, f s = ∑ s : formIdx n k, f s.1 := by
  have h0 : ∑ s : {s : Finset (Fin n) // ¬ ((#s : ℤ) = (k : ℤ))}, f s = 0 :=
    Finset.sum_eq_zero fun s _ => hf s.1 (fun h => s.2 (by rw [h]))
  rw [← Fintype.sum_subtype_add_sum_subtype (fun s : Finset (Fin n) => (#s : ℤ) = (k : ℤ)) f, h0,
    add_zero]

/-- **The local mass controls the local fields** of the simplices inside the neighbourhood. -/
theorem sum_integral_sq_le_locMass {N k : ℕ} (u : (whitneyElement n).Piecewise (mesh n N) k)
    (T' : (mesh n N).simplices) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hsub : (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior ⊆
      Metric.cthickening (2 * hN N) T.closedInterior) :
    ∑ s, ∫ y in (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      (((u T' : (whitneyElement n).space T' k) : FormField n) y s) ^ 2 ≤
      locMass ((whitneyElement n).glue (mesh n N) k u) T := by
  set z : FormField n := ((u T' : (whitneyElement n).space T' k) : FormField n)
  have hz : z ∈ p1MinusForms n k := mem_p1MinusForms_of_space _
  have hdeg := isDeg_of_mem_p1MinusForms hz
  rw [sum_eq_sum_formIdx (fun s hs => by
    have : ∀ y, (z y s) ^ 2 = 0 := fun y => by rw [hdeg y s hs]; ring
    simp_rw [this]; simp)]
  refine Finset.sum_le_sum fun s _ => ?_
  have hΩ := (isOpen_mesh_domain n N).measurableSet
  have hae := ae_glue_eq_local u hΩ
  have hint : interior (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior ⊆ (mesh n N).domain := by
    rw [mesh_domain]; exact interior_closedInterior_subset_cubeDomain T'.2
  rw [integral_closedInterior_eq_interior]
  have heq : ∫ y in interior (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, (z y s.1) ^ 2 =
      ∫ y in interior (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
        ((mesh n N).domain.indicator (((whitneyElement n).glue (mesh n N) k u s :
          L2 ℝ (mesh n N).domain) : (Fin n → ℝ) → ℝ) y) ^ 2 := by
    refine setIntegral_congr_ae isOpen_interior.measurableSet ?_
    filter_upwards [hae] with y hy hyT
    obtain ⟨T'', hyT'', hval⟩ := hy (hint hyT)
    have : T'' = T' := by
      by_contra hne
      exact Set.disjoint_left.1 ((mesh n N).pairwise_disjoint_interior T''.2 T'.2
        (fun e => hne (Subtype.ext e))) hyT'' hyT
    subst this
    rw [hval s]
  rw [heq]
  refine setIntegral_mono_set (integrable_sq_indicator _).integrableOn
    (Eventually.of_forall fun _ => sq_nonneg _)
    (Eventually.of_forall fun y hy => hsub (interior_subset hy))

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
  · rw [smoothForm_apply_of_card_ne hΩ p k v x (fun h => hs (by rw [h]))]
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


theorem one_sub_pow_le {a : ℝ} (ha1 : a ≤ 1) (k : ℕ) : 1 - (1 - a) ^ k ≤ k * a := by
  have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -a by linarith) k
  rw [← sub_eq_add_neg, mul_neg, ← sub_eq_add_neg] at this
  linarith

theorem self_subset_cthickening (T : Affine.Simplex ℝ (Fin n → ℝ) n) {r : ℝ} (hr : 0 ≤ r) :
    T.closedInterior ⊆ Metric.cthickening r T.closedInterior :=
  Metric.self_subset_cthickening _ |>.trans (Metric.cthickening_mono hr _)

variable (γ hγ hγ1) in
open Classical in
/-- **The pointwise estimate of the face integrand of `v - Q_N v`** (`v ∈ Vₕ`): at a point
`x = F_g(x̂)` of a `k`-face `g` of `T`,
`h^{n/2} |Σₛ (v_T - R v)(x)ₛ minorₛ| ≤ (Σₛ |minorₛ|) A m_T(v)^{1/2} · (2 or (k + 1) γ)`,
with the factor `(k + 1) γ` when all barycentric coordinates of `x̂` are `≥ γ`. In that case
every simplex sampled by the smoother contains `g`, where the traces of the local fields agree;
the error is the dilation defect `1 - cᵏ` and the displacement `O(γ h)` against the inverse
estimates. Near `∂g` only the inverse estimates are used. -/
theorem sqrt_mul_abs_integrand_le {N k : ℕ} {A : ℝ} (hA0 : 0 ≤ A) (hA : InvBound n k A)
    (hγ2 : γ ≤ 1 / 2) {u : (whitneyElement n).Piecewise (mesh n N) k}
    (hu : u ∈ (whitneyElement n).globalSpace (mesh n N) k) (T : (mesh n N).simplices)
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n))
    (hg : g.card = k + 1) {ξ : Fin k → ℝ} (hξ : ξ ∈ FiniteElement.refSimplex k) :
    √(hN N) ^ n * |∑ s, (((u T : (whitneyElement n).space T k) : FormField n)
        (simplexMap (faceEnum g (k + 1)) ξ) s -
      (smoothForm (pMax γ hγ hγ1 N) (isOpen_mesh_domain n N).measurableSet k
        ((whitneyElement n).glue (mesh n N) k u) : FormField n)
        (simplexMap (faceEnum g (k + 1)) ξ) s) *
          wedgeProd (simplexMatrix (faceEnum g (k + 1))) s univ| ≤
      (∑ s, |wedgeProd (simplexMatrix (faceEnum g (k + 1))) s univ|) * A *
        √(locMass ((whitneyElement n).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)) *
        (if ξ ∈ nearBdry k γ then 2 else (k + 1) * γ) := by
  classical
  set h := hN N
  have hh : 0 < h := hN_pos N
  have hh2 : h ≤ 1 / 2 := hN_le N
  set p := pMax (n := n) γ hγ hγ1 N
  set hΩ := (isOpen_mesh_domain n N).measurableSet
  set v := (whitneyElement n).glue (mesh n N) k u
  set q := faceEnum g (k + 1)
  set x := simplexMap q ξ
  set m : Finset (Fin n) → ℝ := fun s => wedgeProd (simplexMatrix q) s univ
  set uT : FormField n := ((u T : (whitneyElement n).space T k) : FormField n)
  set L := locMass v (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have hL0 : 0 ≤ L := locMass_nonneg _ _
  set R := (∑ s, |m s|) * A * √L * (if ξ ∈ nearBdry k γ then 2 else (k + 1) * γ)
  have hsq : 0 < √h ^ n := pow_pos (Real.sqrt_pos.2 hh) n
  have hxT : x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior :=
    simplexMap_faceEnum_mem hgT hg hξ
  have hxc : x ∈ closure (cubeDomain n) := by
    rw [← mesh_domain n N]; exact (mesh n N).closedInterior_subset_closure T.2 hxT
  set ŷ := p.center + p.factor • (x - p.center)
  have hŷ : ‖ŷ - x‖ ≤ γ * h / 4 := norm_dil_sub_le (hγ := hγ) (hγ1 := hγ1) N hxc
  have hball : Metric.closedBall ŷ p.bump.rOut ⊆ (mesh n N).domain := by
    have hp := pMax_isMaximal (n := n) (γ := γ) (hγ := hγ) (hγ1 := hγ1) N
    have := closedBall_dil_subset_of_starBall (starBall_mesh n N) p.half_le_factor
      hp.factor_lt_one hp.rOut_lt (by rw [mesh_domain]; exact hxc)
    rwa [← hp.center_eq] at this
  have hc0 : 0 < p.factor := p.factor_pos
  have hc1 : p.factor ≤ 1 := by rw [pMax_factor]; nlinarith
  have hck : p.factor ^ k ≤ 1 := pow_le_one₀ hc0.le hc1
  have hck0 : 0 ≤ p.factor ^ k := pow_nonneg hc0.le k
  have hdef : 1 - p.factor ^ k ≤ k * γ := by
    have := one_sub_pow_le (a := γ * h) (by nlinarith) k
    rw [pMax_factor]
    calc 1 - (1 - γ * h) ^ k ≤ k * (γ * h) := this
      _ ≤ k * γ := by
          have : γ * h ≤ γ := by nlinarith
          exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg k)
  have hTinv := hA.apply T.2 (mem_p1MinusForms_of_space (u T))
  have hLT : ∑ s, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, (uT y s) ^ 2 ≤ L :=
    sum_integral_sq_le_locMass u T (self_subset_cthickening _ (by positivity))
  -- the integrand as a mollified average
  rw [sum_sub_smoothForm_mul_eq hΩ p k v (uT x) m x]
  set G : (Fin n → ℝ) → ℝ := fun t => ∑ s, (uT x s - p.factor ^ k * extField v t s) * m s
  set ρ : (Fin n → ℝ) → ℝ := fun t => p.bump.normed volume (ŷ - t)
  have hρ0 : ∀ t, 0 ≤ ρ t := fun t => p.bump.nonneg_normed _
  have hρi : Integrable ρ := (isTest_normed_comp_sub p.bump ŷ).continuous.integrable_of_hasCompactSupport
    (isTest_normed_comp_sub p.bump ŷ).hasCompactSupport
  have hρ1 : ∫ t, ρ t = 1 := integral_normed_comp_sub p.bump ŷ
  have hρG : Integrable fun t => ρ t * G t := by
    have e : (fun t => ρ t * G t) = fun t => ∑ s, ((uT x s * m s) * ρ t -
        (p.factor ^ k * m s) * (extField v t s * ρ t)) := by
      funext t; simp only [G, Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => by ring
    rw [e]
    exact integrable_finsetSum _ fun s _ =>
      (hρi.const_mul _).sub ((integrable_extField_mul hΩ v p.bump ŷ s).const_mul _)
  -- the pointwise bound on the support of the mollifier
  have hae := ae_glue_eq_local u hΩ
  have hb : ∀ᵐ t ∂volume, ρ t ≠ 0 → |G t| ≤ R / √h ^ n := by
    filter_upwards [hae] with t ht hρt
    have hdist : dist t ŷ < p.bump.rOut := by
      by_contra hcon; push Not at hcon
      exact hρt (normed_eq_zero_of_le p.bump hcon)
    have htΩ : t ∈ (mesh n N).domain := hball (Metric.mem_closedBall.2 hdist.le)
    obtain ⟨T', htT', hval⟩ := ht htΩ
    set u' : FormField n := ((u T' : (whitneyElement n).space T' k) : FormField n)
    have hu' : u' ∈ p1MinusForms n k := mem_p1MinusForms_of_space _
    have hext : ∀ s, extField v t s = u' t s := by
      intro s
      by_cases hs : (#s : ℤ) = (k : ℤ)
      · rw [extField, formExt_of_card _ hs]; exact hval ⟨s, hs⟩
      · have : extField v t s = 0 := by simp [extField, formExt, hs]
        rw [this, isDeg_of_mem_p1MinusForms hu' t s (fun h' => hs (by rw [h']))]
    have hGt : G t = ∑ s, (uT x s - p.factor ^ k * u' t s) * m s := by
      simp only [G, hext]
    have htT'c : t ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior := interior_subset htT'
    have hxt : ‖x - t‖ < γ * h / 2 := by
      have h1 : ‖ŷ - t‖ < γ * h / 32 := by rw [← dist_eq_norm]; rw [dist_comm]; exact hdist
      calc ‖x - t‖ = ‖(x - ŷ) + (ŷ - t)‖ := by congr 1; abel
        _ ≤ ‖x - ŷ‖ + ‖ŷ - t‖ := norm_add_le _ _
        _ < γ * h / 4 + γ * h / 32 := by
            rw [norm_sub_rev] at hŷ
            exact add_lt_add_of_le_of_lt hŷ h1
        _ ≤ γ * h / 2 := by nlinarith
    have hT'sub : (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior ⊆
        Metric.cthickening (2 * h) (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior := by
      intro y hy
      obtain ⟨m', σ', hmσ'⟩ := mem_mesh_simplices.1 T'.2
      have hdy : ‖y - t‖ ≤ h := by
        rw [← hmσ'] at hy htT'c; exact norm_sub_le_of_mem_cubeSimplex hy htT'c
      refine Metric.mem_cthickening_of_dist_le y x _ _ hxT ?_
      rw [dist_eq_norm]
      calc ‖y - x‖ = ‖(y - t) + (t - x)‖ := by congr 1; abel
        _ ≤ ‖y - t‖ + ‖t - x‖ := norm_add_le _ _
        _ ≤ h + γ * h / 2 := by rw [norm_sub_rev t x]; exact add_le_add hdy hxt.le
        _ ≤ 2 * h := by nlinarith
    have hL' : ∑ s, ∫ y in (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, (u' y s) ^ 2 ≤ L :=
      sum_integral_sq_le_locMass u T' hT'sub
    have hT'inv := hA.apply T'.2 hu'
    have hsqL' : √(∑ s, ∫ y in (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
        (u' y s) ^ 2) ≤ √L := Real.sqrt_le_sqrt hL'
    have hsqLT : √(∑ s, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
        (uT y s) ^ 2) ≤ √L := Real.sqrt_le_sqrt hLT
    rw [le_div_iff₀ hsq, hGt, mul_comm]
    by_cases hbad : ξ ∈ nearBdry k γ
    · -- near the boundary of the face: inverse estimates only
      have hR : R = (∑ s, |m s|) * A * √L * 2 := by simp only [R, hbad, ite_true]
      rw [hR]
      calc √h ^ n * |∑ s, (uT x s - p.factor ^ k * u' t s) * m s|
          ≤ √h ^ n * ∑ s, (|uT x s| + |u' t s|) * |m s| := by
            refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun s _ => ?_)) hsq.le
            rw [abs_mul]
            refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            calc |uT x s - p.factor ^ k * u' t s| ≤ |uT x s| + |p.factor ^ k * u' t s| :=
                  abs_sub _ _
              _ ≤ |uT x s| + |u' t s| := by
                  rw [abs_mul, abs_of_nonneg hck0]
                  exact add_le_add le_rfl (mul_le_of_le_one_left (abs_nonneg _) hck)
        _ = ∑ s, (√h ^ n * |uT x s| + √h ^ n * |u' t s|) * |m s| := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => by ring
        _ ≤ ∑ s, (A * √L + A * √L) * |m s| := by
            refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            exact add_le_add ((hTinv.1 x hxT s).trans (mul_le_mul_of_nonneg_left hsqLT hA0))
              ((hT'inv.1 t htT'c s).trans (mul_le_mul_of_nonneg_left hsqL' hA0))
        _ = (∑ s, |m s|) * A * √L * 2 := by
            rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
            refine Finset.sum_congr rfl fun s _ => by ring
    · -- away from the boundary of the face: the sampled simplex contains the face
      have hR : R = (∑ s, |m s|) * A * √L * ((k + 1) * γ) := by simp only [R, hbad, ite_false]
      rw [hR]
      have hμ : ∀ a, γ ≤ refBary ξ a := by
        intro a; by_contra hlt; push Not at hlt; exact hbad ⟨a, hlt⟩
      have hx : x = ∑ a, refBary ξ a • q a := simplexMap_eq_sum q ξ
      have hgT' : g ⊆ vertexSet (T' : Affine.Simplex ℝ (Fin n → ℝ) n) :=
        subset_vertexSet_of_near T.2 T'.2 hgT hg hγ (hγ2) hμ (sum_refBary ξ) htT'c
          (by rw [← hx]; exact hxt)
      have htr : ∑ s, uT x s * m s = ∑ s, u' x s * m s := by
        rw [sum_mul_minor_eq (mem_p1MinusForms_of_space (u T)) q ξ,
          sum_mul_minor_eq hu' q ξ, simplexIntegral_eq_of_mem_globalSpace hu T T' hgT hgT' hg]
      have e : ∑ s, (uT x s - p.factor ^ k * u' t s) * m s =
          ∑ s, ((1 - p.factor ^ k) * u' x s + p.factor ^ k * (u' x s - u' t s)) * m s := by
        have e1 : ∑ s, (uT x s - p.factor ^ k * u' t s) * m s =
            ∑ s, uT x s * m s - ∑ s, p.factor ^ k * u' t s * m s := by
          rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun s _ => by ring
        have e2 : ∑ s, ((1 - p.factor ^ k) * u' x s + p.factor ^ k * (u' x s - u' t s)) * m s =
            ∑ s, u' x s * m s - ∑ s, p.factor ^ k * u' t s * m s := by
          rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun s _ => by ring
        rw [e1, e2, htr]
      rw [e]
      have hxT' : x ∈ (T' : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior :=
        simplexMap_faceEnum_mem hgT' hg hξ
      calc √h ^ n * |∑ s, ((1 - p.factor ^ k) * u' x s + p.factor ^ k * (u' x s - u' t s)) * m s|
          ≤ √h ^ n * ∑ s, ((1 - p.factor ^ k) * |u' x s| + |u' x s - u' t s|) * |m s| := by
            refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun s _ => ?_)) hsq.le
            rw [abs_mul]
            refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
            · rw [abs_mul, abs_of_nonneg (by linarith)]
            · rw [abs_mul, abs_of_nonneg hck0]
              exact mul_le_of_le_one_left (abs_nonneg _) hck
        _ = ∑ s, ((1 - p.factor ^ k) * (√h ^ n * |u' x s|) +
              (√h ^ n * h * |u' x s - u' t s|) / h) * |m s| := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => by field_simp
        _ ≤ ∑ s, ((k * γ) * (A * √L) + (A * (γ * h / 2) * √L) / h) * |m s| := by
            refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right
              (add_le_add ?_ (div_le_div_of_nonneg_right ?_ hh.le)) (abs_nonneg _)
            · refine mul_le_mul hdef ((hT'inv.1 x hxT' s).trans
                (mul_le_mul_of_nonneg_left hsqL' hA0)) (by positivity) (by positivity)
            · refine (hT'inv.2 x t s).trans ?_
              refine mul_le_mul (mul_le_mul_of_nonneg_left hxt.le hA0) hsqL'
                (Real.sqrt_nonneg _) (by positivity)
        _ = ∑ s, ((k + 1 / 2) * γ * (A * √L)) * |m s| := by
            refine Finset.sum_congr rfl fun s _ => by field_simp
        _ ≤ ∑ s, ((k + 1) * γ * (A * √L)) * |m s| := by
            refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            have : 0 ≤ γ * (A * √L) := by positivity
            nlinarith
        _ = (∑ s, |m s|) * A * √L * ((k + 1) * γ) := by
            rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
            refine Finset.sum_congr rfl fun s _ => by ring
  have hmain := abs_integral_mul_le_of_ae hρ0 hρi hρ1 hρG hb
  rw [le_div_iff₀ hsq, mul_comm] at hmain
  exact hmain


variable (γ hγ hγ1) in
/-- **The DOF error of `Q_N` on `Vₕ`**: for `v ∈ Vₕ` and a `k`-face `g` of `T`,
`h^{n/2} |∫_g (v_T - R v)| ≤ 3 (k + 1) 2ⁿ k! A γ hᵏ m_T(v)^{1/2}`. -/
theorem sqrt_mul_abs_dof_err_le {N k : ℕ} {A : ℝ} (hA0 : 0 ≤ A) (hA : InvBound n k A)
    (hγ2 : γ ≤ 1 / 2) {u : (whitneyElement n).Piecewise (mesh n N) k}
    (hu : u ∈ (whitneyElement n).globalSpace (mesh n N) k) (T : (mesh n N).simplices)
    {g : Finset (Fin n → ℝ)} (hgT : g ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n))
    (hg : g.card = k + 1) :
    √(hN N) ^ n * |simplexIntegral (faceEnum g (k + 1))
        ((u T : (whitneyElement n).space T k) : FormField n) -
      simplexIntegral (faceEnum g (k + 1))
        (smoothForm (pMax γ hγ hγ1 N) (isOpen_mesh_domain n N).measurableSet k
          ((whitneyElement n).glue (mesh n N) k u) : FormField n)| ≤
      3 * (k + 1) * 2 ^ n * k.factorial * A * γ * hN N ^ k *
        √(locMass ((whitneyElement n).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)) := by
  classical
  set q := faceEnum g (k + 1)
  set uT : FormField n := ((u T : (whitneyElement n).space T k) : FormField n)
  set w : FormField n := (smoothForm (pMax γ hγ hγ1 N) (isOpen_mesh_domain n N).measurableSet k
    ((whitneyElement n).glue (mesh n N) k u) : FormField n)
  set m : Finset (Fin n) → ℝ := fun s => wedgeProd (simplexMatrix q) s univ
  set L := locMass ((whitneyElement n).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  set Mm := ∑ s, |m s|
  have hMm : Mm ≤ 2 ^ n * (k.factorial * hN N ^ k) := sum_abs_minor_face_le T.2 hgT hg
  have huc : Continuous uT := (isAffineField_of_mem_p1MinusForms (mem_p1MinusForms_of_space _)).continuous
  have hwc : Continuous w := (mem_c1Forms.1 (smoothForm (pMax γ hγ hγ1 N)
    (isOpen_mesh_domain n N).measurableSet k ((whitneyElement n).glue (mesh n N) k u)).2).continuous
  set F : (Fin k → ℝ) → ℝ := fun ξ => ∑ s, (uT (simplexMap q ξ) s - w (simplexMap q ξ) s) * m s
  have hFc : Continuous F := continuous_finsetSum _ fun s _ =>
    ((((continuous_apply s).comp (huc.comp (continuous_simplexMap q))).sub
      ((continuous_apply s).comp (hwc.comp (continuous_simplexMap q)))).mul continuous_const)
  have herr : simplexIntegral q uT - simplexIntegral q w = ∫ ξ in FiniteElement.refSimplex k, F ξ := by
    rw [← simplexIntegral_sub huc.continuousOn hwc.continuousOn, simplexIntegral_def]
    rfl
  have hsq : 0 ≤ √(hN N) ^ n := pow_nonneg (Real.sqrt_nonneg _) n
  set β : (Fin k → ℝ) → ℝ := fun ξ =>
    Mm * A * √L * ((k + 1) * γ + 2 * (nearBdry k γ).indicator 1 ξ)
  have hpt : ∀ ξ ∈ FiniteElement.refSimplex k, √(hN N) ^ n * |F ξ| ≤ β ξ := by
    intro ξ hξ
    refine (sqrt_mul_abs_integrand_le γ hγ hγ1 hA0 hA hγ2 hu T hgT hg hξ).trans ?_
    have h0 : 0 ≤ Mm * A * √L := by positivity
    refine mul_le_mul_of_nonneg_left ?_ h0
    by_cases hb : ξ ∈ nearBdry k γ
    · rw [Set.indicator_of_mem hb, Pi.one_apply]; simp only [hb, ↓reduceIte]; nlinarith
    · rw [Set.indicator_of_notMem hb]; simp [hb]
  have hS : MeasurableSet (FiniteElement.refSimplex k) := measurableSet_refSimplex k
  have hfin : volume (FiniteElement.refSimplex k) ≠ ⊤ := (volume_refSimplex_lt_top k).ne
  set c := Mm * A * √L
  have hβ' : ∀ ξ, β ξ = c * ((k + 1) * γ) + (c * 2) * (nearBdry k γ).indicator 1 ξ := fun ξ => by
    simp only [β, c]; ring
  have hind : IntegrableOn (fun ξ => (nearBdry k γ).indicator (1 : (Fin k → ℝ) → ℝ) ξ)
      (FiniteElement.refSimplex k) :=
    (integrableOn_const hfin).indicator (isOpen_nearBdry k γ).measurableSet
  have hβi : IntegrableOn β (FiniteElement.refSimplex k) := by
    have : IntegrableOn (fun ξ => c * ((k + 1) * γ) + (c * 2) * (nearBdry k γ).indicator 1 ξ)
        (FiniteElement.refSimplex k) := (integrableOn_const hfin).add (hind.const_mul _)
    exact this.congr_fun (fun ξ _ => (hβ' ξ).symm) hS
  have hint : ∫ ξ in FiniteElement.refSimplex k, β ξ =
      c * ((k + 1) * γ * volume.real (FiniteElement.refSimplex k) +
        2 * volume.real (FiniteElement.refSimplex k ∩ nearBdry k γ)) := by
    simp_rw [hβ']
    rw [integral_add (integrableOn_const hfin) (hind.const_mul _), setIntegral_const, smul_eq_mul,
      integral_const_mul (c * 2), integral_indicator_one (isOpen_nearBdry k γ).measurableSet,
      Measure.real, Measure.real, Measure.restrict_apply (isOpen_nearBdry k γ).measurableSet,
      Set.inter_comm]
    simp only [Measure.real]
    ring
  have hvol : volume.real (FiniteElement.refSimplex k) ≤ 1 := by
    rw [volume_real_refSimplex]
    rw [div_le_one (by positivity)]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero k)
  have hbad := volume_real_nearBdry_le (k := k) hγ.le (by linarith : γ ≤ 1)
  rw [herr]
  calc √(hN N) ^ n * |∫ ξ in FiniteElement.refSimplex k, F ξ|
      ≤ √(hN N) ^ n * ∫ ξ in FiniteElement.refSimplex k, |F ξ| :=
        mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs) hsq
    _ = ∫ ξ in FiniteElement.refSimplex k, √(hN N) ^ n * |F ξ| := (integral_const_mul _ _).symm
    _ ≤ ∫ ξ in FiniteElement.refSimplex k, β ξ :=
        setIntegral_mono_on ((hFc.abs.continuousOn.integrableOn_compact
          (isCompact_refSimplex k)).const_mul _) hβi hS hpt
    _ = Mm * A * √L * ((k + 1) * γ * volume.real (FiniteElement.refSimplex k) +
        2 * volume.real (FiniteElement.refSimplex k ∩ nearBdry k γ)) := hint
    _ ≤ (2 ^ n * (k.factorial * hN N ^ k)) * A * √L * ((k + 1) * γ * 1 + 2 * ((k + 1) * γ)) := by
        have h1 : 0 ≤ A * √L := by positivity
        have h2 : 0 ≤ (k + 1) * γ * volume.real (FiniteElement.refSimplex k) +
            2 * volume.real (FiniteElement.refSimplex k ∩ nearBdry k γ) := by positivity
        calc Mm * A * √L * ((k + 1) * γ * volume.real (FiniteElement.refSimplex k) +
              2 * volume.real (FiniteElement.refSimplex k ∩ nearBdry k γ))
            ≤ (2 ^ n * (k.factorial * hN N ^ k)) * A * √L *
              ((k + 1) * γ * volume.real (FiniteElement.refSimplex k) +
                2 * volume.real (FiniteElement.refSimplex k ∩ nearBdry k γ)) := by
              rw [mul_assoc Mm, mul_assoc (2 ^ n * _)]
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMm h1) h2
          _ ≤ _ := by
              have hh := hN_pos N
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have : 0 ≤ (k + 1 : ℝ) * γ := by positivity
              nlinarith
    _ = 3 * (k + 1) * 2 ^ n * k.factorial * A * γ * hN N ^ k * √L := by ring


variable (γ hγ hγ1) in
/-- **The local `L²` error of `Q_N` on `Vₕ`**: `‖v - Q_N v‖²_{L²(T)} ≲ γ² m_T(v)`. -/
theorem sum_integral_sq_sub_interp_le {N k : ℕ} {A B : ℝ} (hA0 : 0 ≤ A) (hA : InvBound n k A)
    (hB : DofBound n k B) (hγ2 : γ ≤ 1 / 2) {u : (whitneyElement n).Piecewise (mesh n N) k}
    (hu : u ∈ (whitneyElement n).globalSpace (mesh n N) k) (T : (mesh n N).simplices) :
    ∑ s : formIdx n k, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      ((((u T : (whitneyElement n).space T k) : FormField n) -
        ((((whitneyElement n).globalInterp (mesh n N) k
          (Submodule.inclusion c1Forms_le_contForms
            (smoothForm (pMax γ hγ hγ1 N) (isOpen_mesh_domain n N).measurableSet k
              ((whitneyElement n).glue (mesh n N) k u))) :
            (whitneyElement n).Piecewise (mesh n N) k) T : (whitneyElement n).space T k) :
              FormField n)) y s.1) ^ 2 ≤
      2 ^ n * (B * (3 * (k + 1) * 2 ^ n * k.factorial * A) * γ) ^ 2 *
        locMass ((whitneyElement n).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n) := by
  set h := hN N
  have hh : 0 < h := hN_pos N
  set w := smoothForm (pMax γ hγ hγ1 N) (isOpen_mesh_domain n N).measurableSet k
    ((whitneyElement n).glue (mesh n N) k u)
  set z : FormField n := ((u T : (whitneyElement n).space T k) : FormField n) -
    ((((whitneyElement n).globalInterp (mesh n N) k (Submodule.inclusion c1Forms_le_contForms w) :
      (whitneyElement n).Piecewise (mesh n N) k) T : (whitneyElement n).space T k) : FormField n)
  have hz : z ∈ p1MinusForms n k := Submodule.sub_mem _ (mem_p1MinusForms_of_space _)
    (mem_p1MinusForms_of_space _)
  set L := locMass ((whitneyElement n).glue (mesh n N) k u) (T : Affine.Simplex ℝ (Fin n → ℝ) n)
  have hL0 : 0 ≤ L := locMass_nonneg _ _
  set C₁ := 3 * (k + 1) * 2 ^ n * k.factorial * A
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
    exact sqrt_mul_abs_dof_err_le γ hγ hγ1 hA0 hA hγ2 hu T hgT hg
  have hzb : ∀ y ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, ∀ s,
      |z y s| ≤ B * (C₁ * γ * √L / √h ^ n) := by
    intro y hy s
    have h1 := hB.apply T.2 hz hD0 hdof hy s
    have hhk : 0 < h ^ k := pow_pos hh k
    refine le_of_mul_le_mul_left (h1.trans (le_of_eq ?_)) hhk
    simp only [D]; field_simp; simp only [h]; ring
  have hzc : Continuous z := (isAffineField_of_mem_p1MinusForms hz).continuous
  obtain ⟨m, σ, hmσ⟩ := mem_mesh_simplices.1 T.2
  have hloc : ∀ s : formIdx n k, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior,
      (z y s.1) ^ 2 ≤ h ^ n * (B * (C₁ * γ * √L / √h ^ n)) ^ 2 := by
    intro s
    rw [← hmσ]
    refine integral_cubeSimplex_le m σ (f := fun y => (z y s.1) ^ 2)
      (((continuous_apply s.1).comp hzc).pow 2) (fun y hy => ?_) (fun y => sq_nonneg _)
    rw [hmσ] at hy
    have := hzb y hy s.1
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hhn : h ^ n = (√h ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hh.le]
  calc ∑ s : formIdx n k, ∫ y in (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior, (z y s.1) ^ 2
      ≤ ∑ _s : formIdx n k, h ^ n * (B * (C₁ * γ * √L / √h ^ n)) ^ 2 :=
        Finset.sum_le_sum fun s _ => hloc s
    _ = Fintype.card (formIdx n k) * (h ^ n * (B * (C₁ * γ * √L / √h ^ n)) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 2 ^ n * (h ^ n * (B * (C₁ * γ * √L / √h ^ n)) ^ 2) :=
        mul_le_mul_of_nonneg_right (card_formIdx_le _) (by positivity)
    _ = 2 ^ n * (B * C₁ * γ) ^ 2 * (√L) ^ 2 := by
        rw [hhn]; field_simp
    _ = 2 ^ n * (B * C₁ * γ) ^ 2 * L := by rw [Real.sq_sqrt hL0]


variable (γ hγ hγ1) in
/-- **`Q_N` is close to the identity on `Vₕ`**:
`‖v - Q_N v‖² ≤ 2ⁿ (B C₁ γ)² 6ⁿ n! ‖v‖²`, `C₁ = 3 (k + 1) 2ⁿ k! A`. -/
theorem norm_sq_sub_smoothedInterp_le {N k : ℕ} {A B : ℝ} (hA0 : 0 ≤ A) (hA : InvBound n k A)
    (hB : DofBound n k B) (hγ2 : γ ≤ 1 / 2) {u : (whitneyElement n).Piecewise (mesh n N) k}
    (hu : u ∈ (whitneyElement n).globalSpace (mesh n N) k) :
    ‖(whitneyElement n).glue (mesh n N) k u - (whitneyElement n).smoothedInterp (mesh n N)
        (pMax γ hγ hγ1 N) (isOpen_mesh_domain n N).measurableSet k
        ((whitneyElement n).glue (mesh n N) k u)‖ ^ 2 ≤
      2 ^ n * (B * (3 * (k + 1) * 2 ^ n * k.factorial * A) * γ) ^ 2 *
        ((6 ^ n * n.factorial : ℕ) * ‖(whitneyElement n).glue (mesh n N) k u‖ ^ 2) := by
  set v := (whitneyElement n).glue (mesh n N) k u
  have hQ := (whitneyElement n).smoothedInterp_natCast (mesh n N) (pMax γ hγ hγ1 N)
    (isOpen_mesh_domain n N).measurableSet k v
  set Pw := (whitneyElement n).globalInterp (mesh n N) k (Submodule.inclusion c1Forms_le_contForms
    (smoothForm (pMax (n := n) γ hγ hγ1 N) (isOpen_mesh_domain n N).measurableSet k v))
  set d : (whitneyElement n).Piecewise (mesh n N) k := u - (Pw : (whitneyElement n).Piecewise (mesh n N) k)
  have hsub : v - (whitneyElement n).smoothedInterp (mesh n N) (pMax γ hγ hγ1 N)
      (isOpen_mesh_domain n N).measurableSet k v = (whitneyElement n).glue (mesh n N) k d := by
    rw [hQ, map_sub]
  have hglue : (whitneyElement n).glue (mesh n N) k d = pieceL2 (mesh n N) (mesh n N).domain
      (fun T => formComp (k := (k : ℤ)) ((whitneyElement n).extendPW (mesh n N) d T))
      (fun T hT s => continuous_formComp ((whitneyElement n).contDiff_extendPW (mesh n N) _
        hT).continuous s) := rfl
  have h1 := norm_sq_pieceL2_le (mesh n N) (mesh n N).domain (fun T => formComp (k := (k : ℤ))
    ((whitneyElement n).extendPW (mesh n N) d T))
    (fun T hT s => continuous_formComp ((whitneyElement n).contDiff_extendPW (mesh n N) _
      hT).continuous s)
  set C := 2 ^ n * (B * (3 * (k + 1) * 2 ^ n * k.factorial * A) * γ) ^ 2
  have h2 : ∑ T ∈ (mesh n N).simplices, ∑ s : formIdx n k, ∫ y in T.closedInterior,
      (formComp (k := (k : ℤ)) ((whitneyElement n).extendPW (mesh n N) d T) s y) ^ 2 ≤
      ∑ T ∈ (mesh n N).simplices, C * locMass v T := by
    refine Finset.sum_le_sum fun T hT => ?_
    have e : ∀ s : formIdx n k, ∀ y, formComp (k := (k : ℤ))
        ((whitneyElement n).extendPW (mesh n N) d T) s y =
        ((((u ⟨T, hT⟩ : (whitneyElement n).space T k) : FormField n) -
          (((Pw : (whitneyElement n).Piecewise (mesh n N) k) ⟨T, hT⟩ :
            (whitneyElement n).space T k) : FormField n)) y s.1) := fun s y => by
      change (whitneyElement n).extendPW (mesh n N) d T y s.1 = _
      rw [(whitneyElement n).extendPW_of_mem (mesh n N) _ hT]
      rfl
    simp_rw [e]
    exact sum_integral_sq_sub_interp_le γ hγ hγ1 hA0 hA hB hγ2 hu ⟨T, hT⟩
  have h3 := sum_locMass_le N v
  rw [hsub, hglue]
  refine h1.trans (h2.trans ?_)
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left h3 (by positivity)


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
    (hxS : B * (3 * (k + 1) * 2 ^ n * k.factorial * A) ≤ S)
    (hK : K = 2 ^ n * ((6 ^ n * n.factorial : ℕ) : ℝ)) (hγe : γ = 1 / (2 * (1 + S * K)))
    (hγ2 : γ ≤ 1 / 2) {u : (whitneyElement n).Piecewise (mesh n N) k}
    (hu : u ∈ (whitneyElement n).globalSpace (mesh n N) k) :
    ‖(whitneyElement n).glue (mesh n N) k u - (whitneyElement n).smoothedInterp (mesh n N)
        (pMax γ hγ hγ1 N) (isOpen_mesh_domain n N).measurableSet k
        ((whitneyElement n).glue (mesh n N) k u)‖ ≤
      1 / 2 * ‖(whitneyElement n).glue (mesh n N) k u‖ := by
  have h := norm_sq_sub_smoothedInterp_le γ hγ hγ1 hA0 hA hB hγ2 hu
  have hK1 : 1 ≤ K := hK ▸ one_le_cov
  have hx0 : 0 ≤ B * (3 * (k + 1) * 2 ^ n * k.factorial * A) := by positivity
  have hq := sq_le_quarter hS hK1 hx0 hxS
  rw [← hγe] at hq
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) (h.trans ?_)
  calc 2 ^ n * (B * (3 * (k + 1) * 2 ^ n * k.factorial * A) * γ) ^ 2 *
        (((6 ^ n * n.factorial : ℕ) : ℝ) * ‖(whitneyElement n).glue (mesh n N) k u‖ ^ 2)
      = K * (B * (3 * (k + 1) * 2 ^ n * k.factorial * A) * γ) ^ 2 *
          ‖(whitneyElement n).glue (mesh n N) k u‖ ^ 2 := by rw [hK]; ring
    _ ≤ 1 / 4 * ‖(whitneyElement n).glue (mesh n N) k u‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hq (sq_nonneg _)
    _ = (1 / 2 * ‖(whitneyElement n).glue (mesh n N) k u‖) ^ 2 := by ring

variable (n) in
/-- **The smoothing scale** `γ` of the parameters `pMax`, depending only on `n`. -/
theorem exists_gamma :
    ∃ γ : ℝ, ∃ hγ : 0 < γ, ∃ hγ1 : γ ≤ 1, γ ≤ 1 / 2 ∧ ∀ (N k : ℕ),
      ∀ v ∈ (whitneyElement n).V (mesh n N) k,
        ‖v - (whitneyElement n).smoothedInterp (mesh n N) (pMax γ hγ hγ1 N)
          (isOpen_mesh_domain n N).measurableSet k v‖ ≤ 1 / 2 * ‖v‖ := by
  classical
  choose A hA0 hA using fun k : ℕ => exists_invBound (n := n) k
  choose B hB0 hB using fun k : ℕ => exists_dofBound (n := n) k
  set x : ℕ → ℝ := fun k => B k * (3 * (k + 1) * 2 ^ n * k.factorial * A k)
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
  have hγ1 : γ ≤ 1 := by linarith
  refine ⟨γ, hγ, hγ1, hγ2, fun N k v hv => ?_⟩
  by_cases hk : n < k
  · have := subsingleton_L2F_of_lt (Ω := (mesh n N).domain) hk
    rw [Subsingleton.elim v 0]; simp
  push Not at hk
  obtain ⟨u, hu⟩ := hv
  rw [← hu]
  have hxk : x k ≤ S := Finset.single_le_sum (fun k _ => hx0 k) (Finset.mem_range.2 (by omega))
  exact norm_sub_smoothedInterp_le_half (hγ := hγ) (hγ1 := hγ1) (hA0 k) (hA k) (hB0 k) (hB k) hS
    hxk rfl hγe hγ2 u.2

variable [NeZero n]

/-- **The smoothed-projection estimates hold on the Freudenthal meshes of the cube**
([AFW2010], §5.4; [ChristiansenWinther2008]): for the parameters `pMax γ` (dilation factor
`1 - γ h_N` about the centre, bump radii `γ h_N / 64 < γ h_N / 32`) with `γ` small depending only on
`n`, the smoothed interpolants `Q_N = Π_h R_N` are bounded in `L²` uniformly in `N`, and
`‖v - Q_N v‖ ≤ ½ ‖v‖` on the Whitney spaces. -/
theorem smoothingEstimates_exists :
    ∃ (p : ℕ → SmoothingParam (Fin n → ℝ)) (C : ℝ), SmoothingEstimates n p C := by
  obtain ⟨γ, hγ, hγ1, -, hclose⟩ := exists_gamma n
  obtain ⟨C, hC0, hbound⟩ := exists_norm_smoothedInterp_le (n := n) γ hγ hγ1
  refine ⟨pMax γ hγ hγ1, max C (1 / 2), ?_⟩
  have hest : ∀ N, (∀ i x, ‖(smoothed n N (pMax γ hγ hγ1 N) (pMax_isMaximal N)).Q i x‖ ≤
      max C (1 / 2) * ‖x‖) ∧ (∀ i, ∀ v ∈ (whitney n N).V i,
        ‖v - (smoothed n N (pMax γ hγ hγ1 N) (pMax_isMaximal N)).Q i v‖ ≤ 1 / 2 * ‖v‖) := by
    intro N
    refine commutingMapOfEq_estimates (mesh_domain n N) (isOpen_mesh_domain n N)
      (isOpen_cubeDomain n) _ (fun i x => ?_) (fun i v hv => ?_)
    · rw [LocalElement.smoothedCommutingMap_Q]
      rcases i with k | k
      · exact (hbound N k x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      · have h0 : ∀ y : L2F ℝ (mesh n N).domain (formIdx n (Int.negSucc k)), ‖y‖ = 0 := fun y => by
          have := LocalElement.subsingleton_L2F_negSucc (mesh n N).domain (n := n) k
          rw [Subsingleton.elim y 0, norm_zero]
        exact (h0 _).le.trans (by positivity)
    · rw [LocalElement.smoothedCommutingMap_Q]
      rcases i with k | k
      · exact hclose N k v hv
      · have h0 : ∀ y : L2F ℝ (mesh n N).domain (formIdx n (Int.negSucc k)), ‖y‖ = 0 := fun y => by
          have := LocalElement.subsingleton_L2F_negSucc (mesh n N).domain (n := n) k
          rw [Subsingleton.elim y 0, norm_zero]
        exact (h0 _).le.trans (by positivity)
  exact ⟨fun N => pMax_isMaximal N, le_max_right _ _, fun N => (hest N).1,
    fun N => (hest N).2⟩

end Feec.Models.Cube.FEM
