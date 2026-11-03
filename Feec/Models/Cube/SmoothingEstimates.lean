module

public import Feec.Models.StarShaped.Smoothing
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
([AFW2010], §5.5; [ChristiansenWinther2008]). All the consequences proved under these estimates in
`Feec.Models.Cube.FiniteElementMethod` therefore hold unconditionally for these parameters, for
instance uniformly bounded cochain projections (`exists_uniform_cochainProjection`,
`exists_uniform_cochainProjectionMin`).

**The proof is the star-shaped one** (`Feec.Models.StarShaped.Smoothing`): `Q` is star-shaped
with respect to the ball `B((¼, …, ¼), ¼)` and contained in the closed ball of radius `R = ¼`
about its centre, and the Freudenthal meshes are uniformly shape regular and quasi-uniform
(`meshData`: every simplex is `h_N (m + K_σ)`, a homothetic copy of one of the `n!` Kuhn simplices,
[Freudenthal1942], [Kuhn1960]). An admissible parameter at scale `γ` (`IsAdm`: centre of the cube,
`|c - 1| = γ h_N`, the bump radii above) is admissible at scale `γ h_N / 4` with bump ratio
`σ = 1 / 8 = s₀ / (8 R)` in the star-shaped theory (`IsAdm.starShaped`), which gives the uniform
bound and the closeness for every `γ ≤ γ₀` (`exists_gamma₀`, `smoothingEstimates_pMax_forall`,
`smoothingEstimatesMin_pMin_forall`).

The file also keeps the geometry of the Freudenthal meshes used by the other cube families: the
Kuhn simplices `cubeSimplex`, the separation of lattice points (`isSep_latticePoint_add_sum`,
`isSep_inv_smul_sum`), bounded overlap with the constant `6ⁿ n!`
(`card_filter_mem_cthickening_le`, `sum_locMass_le`), and the boundary facets of the cube meshes
(`exists_boundaryFacet_of_lower`, `exists_boundaryFacet_of_upper`, `coord_eq_zero_of_near`,
`coord_eq_half_of_near`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.5 (smoothed projections: the estimates for `ε ≈ h`)
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

/-- The simplices of the level-`(N + 1)` mesh have diameter `h_N` (`n ≠ 0`). -/
theorem diam_eq_hN [NeZero n] {N : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) : diam T = hN N := by
  obtain ⟨m, σ, rfl⟩ := mem_freudenthalMesh_simplices.1 hT
  exact diam_freudenthalMesh_simplex (0 : Fin n → ℝ) (hN_pos N) (finLattice m) σ

/-! ### Bounded overlap -/

open Classical in
/-- **Bounded overlap**: a point lies in the `2 h_N`-neighbourhoods of at most `6ⁿ n!` simplices
of the level-`(N + 1)` mesh (`Feec.FiniteElement.card_filter_mem_cthickening_le` with the shape
constants `max n 2, 1` and `q = 1`). -/
theorem card_filter_mem_cthickening_le (N : ℕ) (t : Fin n → ℝ) :
    ((mesh n N).simplices.filter fun T : Affine.Simplex ℝ (Fin n → ℝ) n =>
      t ∈ Metric.cthickening (2 * hN N) T.closedInterior).card ≤ 6 ^ n * n.factorial := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine (Finset.card_filter_le _ _).trans ((Finset.card_le_card (t := Finset.univ.image
      fun p : (Fin 0 → Fin (N + 1)) × Equiv.Perm (Fin 0) => cubeSimplex N p.1 p.2)
      fun T hT => ?_).trans Finset.card_image_le |>.trans (by simp))
    obtain ⟨m, σ, rfl⟩ := mem_mesh_simplices.1 hT
    exact Finset.mem_image.2 ⟨(m, σ), Finset.mem_univ _, rfl⟩
  have : NeZero n := ⟨hn.ne'⟩
  have hm : (mesh n N).meshSize = hN N :=
    (mesh n N).meshSize_eq ⟨_, cubeSimplex_mem N 0 1⟩ fun T hT => diam_eq_hN hT
  have h := Feec.FiniteElement.card_filter_mem_cthickening_le (mesh n N)
    (C := ((max n 2 : ℕ) : ℝ)) (fun T hT => by
      exact_mod_cast isShapeRegular_freudenthalMesh (0 : Fin n → ℝ) (1 / 2) (by norm_num) T
        ⟨N, hT⟩) one_pos one_pos (fun T hT => by rw [one_mul, hm, diam_eq_hN hT])
    (hm ▸ hN_pos N) (r := 2 * hN N) (by have := hN_pos N; positivity) t
  rw [hm] at h
  have e : (2 * (2 * hN N + hN N)) ^ n * n.factorial / (1 * (1 * hN N) ^ n) =
      6 ^ n * n.factorial := by
    have := hN_ne_zero N; field_simp; ring
  exact_mod_cast h.trans_eq e

open Classical in
/-- **Bounded overlap of the neighbourhoods**, integrated. -/
theorem sum_integral_cthickening_le (N : ℕ) {f : (Fin n → ℝ) → ℝ} (hf : Integrable f)
    (hf0 : ∀ x, 0 ≤ f x) :
    ∑ T ∈ (mesh n N).simplices, ∫ x in Metric.cthickening (2 * hN N) T.closedInterior, f x ≤
      (6 ^ n * n.factorial : ℕ) * ∫ x, f x :=
  sum_integral_le_of_card_le _ _ (fun _ => Metric.isClosed_cthickening.measurableSet)
    (fun x => by exact_mod_cast card_filter_mem_cthickening_le N x) hf hf0

/-! ### Face integrals on the mesh simplices -/

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

/-- **The smoothed field near a simplex is bounded by the local mass**:
`|R x (y)ₛ| ≤ 2ᵏ ((32 / (γ h_N))ⁿ m_T(x))^{1/2}` at every point `y ∈ cl Q` within `h_N` of `T`. -/
theorem IsAdm.abs_smoothForm_le_locMass_of_near {N k : ℕ} {p : SmoothingParam (Fin n → ℝ)}
    (hp : IsAdm γ N p) (hγ1 : γ ≤ 1) (x : L2F ℝ (mesh n N).domain (formIdx n k))
    (T : Affine.Simplex ℝ (Fin n → ℝ) n) {y z : Fin n → ℝ} (hyc : y ∈ closure (cubeDomain n))
    (hz : z ∈ T.closedInterior) (hyz : dist y z ≤ hN N) (s : Finset (Fin n)) :
    |(smoothForm p (isOpen_mesh_domain n N).measurableSet k x : FormField n) y s| ≤
      2 ^ k * √((32 / (γ * hN N)) ^ n * locMass x T) := by
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
  have h1 := hp.norm_dil_sub_le hyc
  have h2 : dist t (p.center + p.factor • (y - p.center)) ≤ γ * hN N / 32 := by
    have := Metric.mem_closedBall.1 ht; rwa [hp.rOut_eq] at this
  refine Metric.mem_cthickening_of_dist_le t z _ _ hz ?_
  calc dist t z ≤ dist t (p.center + p.factor • (y - p.center)) +
        dist (p.center + p.factor • (y - p.center)) y + dist y z := dist_triangle4 _ _ _ _
    _ ≤ γ * hN N / 32 + γ * hN N / 4 + hN N :=
        add_le_add (add_le_add h2 (by rw [dist_eq_norm]; exact h1)) hyz
    _ ≤ 2 * hN N := by nlinarith

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

theorem interior_closedInterior_subset_cubeDomain {N : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) : interior T.closedInterior ⊆ cubeDomain n := by
  have h := interior_mono ((mesh n N).closedInterior_subset_closure hT)
  rw [mesh_domain, closure_cubeDomain, interior_pi_set Set.finite_univ] at h
  simp only [interior_Icc] at h
  exact h

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

/-- **Samples of the smoother near a point of the closed cube**: a point `t` in the support of the
bump at the dilated point of `x ∈ cl Q` has `‖x - t‖ < γ h / 2`. -/
theorem IsAdm.norm_sub_lt {N : ℕ} {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm γ N p)
    {x t : Fin n → ℝ} (hxc : x ∈ closure (cubeDomain n))
    (hdist : dist t (p.center + p.factor • (x - p.center)) < p.bump.rOut) :
    ‖x - t‖ < γ * hN N / 2 := by
  have hγh := hp.gamma_h_nonneg
  have hŷ := hp.norm_dil_sub_le hxc
  set ŷ := p.center + p.factor • (x - p.center)
  have h1 : ‖ŷ - t‖ < γ * hN N / 32 := by
    rw [← dist_eq_norm, dist_comm, ← hp.rOut_eq]; exact hdist
  calc ‖x - t‖ = ‖(x - ŷ) + (ŷ - t)‖ := by congr 1; abel
    _ ≤ ‖x - ŷ‖ + ‖ŷ - t‖ := norm_add_le _ _
    _ < γ * hN N / 4 + γ * hN N / 32 := by
        rw [norm_sub_rev] at hŷ; exact add_lt_add_of_le_of_lt hŷ h1
    _ ≤ γ * hN N / 2 := by linarith

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

/-- **The maximal family samples only inside `Ω`**: every sample `t` of the smoother at a point
`x` of `Ω̄` lies in `Ω`. -/
theorem pMax_samples_mem (N : ℕ) :
    ∀ x ∈ closure (mesh n N).domain, ∀ t, dist t ((pMax (n := n) γ hγ hγ1 N).center +
      (pMax (n := n) γ hγ hγ1 N).factor • (x - (pMax (n := n) γ hγ hγ1 N).center)) <
        (pMax (n := n) γ hγ hγ1 N).bump.rOut → t ∈ (mesh n N).domain := fun x hx t ht => by
  have hp := pMax_isMaximal (n := n) (γ := γ) (hγ := hγ) (hγ1 := hγ1) N
  have := closedBall_dil_subset_of_starBall (starBall_mesh n N)
    (pMax (n := n) γ hγ hγ1 N).half_le_factor hp.factor_lt_one hp.rOut_lt hx
  rw [← hp.center_eq] at this
  exact this (Metric.mem_closedBall.2 ht.le)

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

/-- **Separation of convex combinations of the vertices of a mesh simplex**: if all weights are
`≥ θ`, the rescaled point `h_N⁻¹ Σₐ μₐ qₐ` is `θ`-separated (`IsSep`). -/
theorem isSep_inv_smul_sum {N : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) {m : ℕ} {q : Fin (m + 1) → Fin n → ℝ}
    (hqT : ∀ a, q a ∈ vertexSet T) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2)
    {μ : Fin (m + 1) → ℝ} (hμ : ∀ a, θ ≤ μ a) (hμ1 : ∑ a, μ a = 1) :
    IsSep θ ((hN N)⁻¹ • ∑ a, μ a • q a) := by
  obtain ⟨m₀, σ, rfl⟩ := mem_mesh_simplices.1 hT
  have hj : ∀ a, ∃ j, q a = hN N • (latticePoint (finLattice m₀) + kuhnVertex σ j) := fun a => by
    obtain ⟨j, hj⟩ := mem_vertexSet.1 (hqT a)
    exact ⟨j, by rw [← hj, cubeSimplex_points]⟩
  choose j hj using hj
  have hxs : (hN N)⁻¹ • ∑ a, μ a • q a =
      latticePoint (finLattice m₀) + ∑ a, μ a • kuhnVertex σ (j a) := by
    have hh := hN_ne_zero N
    simp only [hj, Finset.smul_sum, smul_smul, smul_add, Finset.sum_add_distrib,
      ← Finset.sum_smul]
    have e1 : (hN N)⁻¹ * ∑ i, μ i * hN N = 1 := by
      rw [← Finset.sum_mul, hμ1]; field_simp
    have e2 : ∀ a, (hN N)⁻¹ * (μ a * hN N) = μ a := fun a => by field_simp
    simp only [e1, e2, one_smul]
  rw [hxs]
  exact isSep_latticePoint_add_sum hθ0.le hθ (finLattice m₀) σ j hμ hμ1

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

/-- **A good point near `{y_i = 0}`**: a convex combination of vertices of a mesh simplex with
weights `≥ θ` and `i`-th coordinate `< θ h_N / 2` has all its vertices in `{y_i = 0}`. -/
theorem coord_eq_zero_of_near {N : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) {m : ℕ} {q : Fin (m + 1) → Fin n → ℝ}
    (hqT : ∀ a, q a ∈ vertexSet T) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2)
    {μ : Fin (m + 1) → ℝ} (hμ : ∀ a, θ ≤ μ a) (hμ1 : ∑ a, μ a = 1) {i : Fin n}
    (hx : (∑ a, μ a • q a) i < θ * hN N / 2) (a : Fin (m + 1)) : q a i = 0 := by
  have hh := hN_pos N
  have hsep := isSep_inv_smul_sum hT hqT hθ0 hθ hμ hμ1
  have hμp : ∀ a, 0 < μ a := fun a => hθ0.trans_le (hμ a)
  have hx0' : 0 ≤ (∑ a, μ a • q a) i := by
    rw [Finset.sum_apply]
    exact Finset.sum_nonneg fun a _ => by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (hμp a).le (apply_mem_Icc_of_mem_vertexSet hT (hqT a) i).1
  have hXi : ((hN N)⁻¹ • ∑ a, μ a • q a) i = (∑ a, μ a • q a) i / hN N := by
    simp [div_eq_inv_mul]
  have hx0 : (∑ a, μ a • q a) i = 0 := by
    rcases hsep.1 i 0 with e | e
    · rw [hXi] at e; push_cast at e
      rcases div_eq_zero_iff.1 e with e' | e'
      · exact e'
      · exact absurd e' hh.ne'
    · exfalso
      rw [hXi] at e; push_cast at e
      rw [sub_zero, abs_of_nonneg (div_nonneg hx0' hh.le), le_div_iff₀ hh] at e
      nlinarith
  refine eq_of_sum_smul_apply_eq hμp hμ1 (fun b => ?_) hx0 a
  have := (apply_mem_Icc_of_mem_vertexSet hT (hqT b) i).1; linarith

/-- **A good point near `{y_i = ½}`**: the upper analogue of `coord_eq_zero_of_near`. -/
theorem coord_eq_half_of_near {N : ℕ} {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ (mesh n N).simplices) {m : ℕ} {q : Fin (m + 1) → Fin n → ℝ}
    (hqT : ∀ a, q a ∈ vertexSet T) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2)
    {μ : Fin (m + 1) → ℝ} (hμ : ∀ a, θ ≤ μ a) (hμ1 : ∑ a, μ a = 1) {i : Fin n}
    (hx : 1 / 2 - θ * hN N / 2 < (∑ a, μ a • q a) i) (a : Fin (m + 1)) : q a i = 1 / 2 := by
  have hh := hN_pos N
  have hsep := isSep_inv_smul_sum hT hqT hθ0 hθ hμ hμ1
  have hμp : ∀ a, 0 < μ a := fun a => hθ0.trans_le (hμ a)
  have hx2 : (∑ a, μ a • q a) i ≤ 1 / 2 := by
    have e : (∑ a, μ a • q a) i = ∑ a, μ a * q a i := by simp [Finset.sum_apply]
    have : ∑ a, μ a * q a i ≤ ∑ a, μ a * (1 / 2) :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
        (apply_mem_Icc_of_mem_vertexSet hT (hqT a) i).2 (hμp a).le
    rw [← Finset.sum_mul, hμ1, one_mul] at this
    linarith
  have hXi : ((hN N)⁻¹ • ∑ a, μ a • q a) i = (∑ a, μ a • q a) i / hN N := by
    simp [div_eq_inv_mul]
  have hhN : hN N * ((N : ℝ) + 1) = 1 / 2 := by unfold hN; push_cast; field_simp
  have hx1 : (∑ a, μ a • q a) i = 1 / 2 := by
    rcases hsep.1 i (N + 1) with e | e
    · rw [hXi] at e; push_cast at e
      rw [div_eq_iff hh.ne'] at e; rw [e, mul_comm]; exact hhN
    · exfalso
      rw [hXi] at e; push_cast at e
      have hle : (∑ a, μ a • q a) i / hN N ≤ N + 1 := by
        rw [div_le_iff₀ hh]; linarith [hhN, mul_comm (hN N) ((N : ℝ) + 1)]
      have hgt : (N : ℝ) + 1 - θ / 2 < (∑ a, μ a • q a) i / hN N := by
        rw [lt_div_iff₀ hh]
        nlinarith [hhN, mul_comm (hN N) ((N : ℝ) + 1)]
      rw [abs_of_nonpos (by linarith)] at e
      linarith
  have h1 := eq_of_sum_smul_apply_eq (q := fun a => -q a) (i := i) (c := -(1 / 2)) hμp hμ1
    (fun b => by have := (apply_mem_Icc_of_mem_vertexSet hT (hqT b) i).2; simp; linarith)
    (by
      have : (∑ a, μ a • -q a) = -(∑ a, μ a • q a) := by simp [Finset.sum_neg_distrib]
      rw [this, Pi.neg_apply, hx1]) a
  simp only [Pi.neg_apply, neg_inj] at h1
  exact h1

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

/-! ### The cube as a star-shaped domain with shape-regular meshes -/

theorem meshSize_mesh (N : ℕ) : (mesh n N).meshSize = hN N :=
  (mesh n N).meshSize_eq ⟨_, mem_freudenthalMesh_simplices.2 ⟨0, 1, rfl⟩⟩ fun _ hT => diam_eq_hN hT

/-- **The Freudenthal meshes of the cube are uniformly shape regular and quasi-uniform**, with the
constants `max n 2`, `1` of `Feec.Mesh.isShapeRegular_freudenthalMesh` and `q = 1`. -/
theorem meshData (N : ℕ) : StarShaped.MeshData (mesh n N) ((max n 2 : ℕ) : ℝ) 1 1 where
  shape T hT := by
    have := isShapeRegular_freudenthalMesh (0 : Fin n → ℝ) (1 / 2) (by norm_num) T ⟨N, hT⟩
    exact_mod_cast this
  quasi T hT := by rw [one_mul, meshSize_mesh, diam_eq_hN hT]
  meshSize_pos := by rw [meshSize_mesh]; exact hN_pos N

/-- Admissible parameters at scale `γ` on the cube are admissible at scale `γ h_N / 4` for the
star-shaped theory, with centre `center n`, `R = 1 / 4` and bump ratio `σ = 1 / 8`. -/
theorem IsAdm.starShaped {N : ℕ} {p : SmoothingParam (Fin n → ℝ)} (hp : IsAdm γ N p) :
    StarShaped.IsAdm (center n) (1 / 4) (1 / 8) (γ / 4) (mesh n N).meshSize p where
  center_eq := hp.center_eq
  abs_factor_sub_one := by rw [hp.abs_factor_sub_one, meshSize_mesh]; ring
  rIn_eq := by rw [hp.rIn_eq, meshSize_mesh]; ring
  rOut_eq := by rw [hp.rOut_eq, meshSize_mesh]; ring

variable (n) in
/-- **The smoothed-projection estimates on the cube, for all small `γ`**: the cube with its
Freudenthal meshes is an instance of the estimates on shape-regular meshes of star-shaped
domains (`StarShaped.exists_gamma`, `StarShaped.exists_norm_smoothedInterp_le`; `meshData`,
`IsAdm.starShaped`). There is `γ₀ ∈ (0, ½]`, depending only on `n`, such that for every
`γ ∈ (0, γ₀]` the smoothed interpolants `Q_N` of admissible parameters at scale `γ` are bounded in
`L²` uniformly in `N`, with `‖v - Q_N v‖ ≤ ½ ‖v‖` on `Vₕ` for the maximal family and on `V̊ₕ`
for the minimal family. -/
theorem exists_gamma₀ :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 / 2 ∧ ∀ γ, 0 < γ → γ ≤ γ₀ → ∃ C, 0 ≤ C ∧
      ∀ (N k : ℕ) (p : SmoothingParam (Fin n → ℝ)), IsAdm γ N p →
        (∀ x : L2F ℝ (mesh n N).domain (formIdx n k),
          ‖(whitneyElement n).smoothedInterp (mesh n N) p
            (isOpen_mesh_domain n N).measurableSet k x‖ ≤ C * ‖x‖) ∧
        (p.IsMaximal (center n) (1 / 4) → ∀ u ∈ (whitneyElement n).globalSpace (mesh n N) k,
          ‖(whitneyElement n).glue (mesh n N) k u - (whitneyElement n).smoothedInterp (mesh n N) p
            (isOpen_mesh_domain n N).measurableSet k ((whitneyElement n).glue (mesh n N) k u)‖ ≤
            1 / 2 * ‖(whitneyElement n).glue (mesh n N) k u‖) ∧
        (p.IsMinimal (center n) (1 / 4) → ∀ u ∈ (whitneyElement n).globalSpace₀ (mesh n N) k,
          ‖(whitneyElement n).glue (mesh n N) k u - (whitneyElement n).smoothedInterp (mesh n N) p
            (isOpen_mesh_domain n N).measurableSet k ((whitneyElement n).glue (mesh n N) k u)‖ ≤
            1 / 2 * ‖(whitneyElement n).glue (mesh n N) k u‖) := by
  have hC : (0 : ℝ) ≤ ((max n 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  obtain ⟨γ₁, K₀, hγ₁, hγ₁4, hK₀, hclose⟩ :=
    StarShaped.exists_gamma n (x₀ := center n) hC one_pos one_pos
  refine ⟨2 * γ₁, by positivity, by linarith, fun γ hγ hγγ₀ => ?_⟩
  have hγ4 : 0 < γ / 4 := by positivity
  obtain ⟨C, hC0, hbound⟩ := StarShaped.exists_norm_smoothedInterp_le (x₀ := center n)
    (R := 1 / 4) (σ := 1 / 8) (C := ((max n 2 : ℕ) : ℝ)) one_pos one_pos hγ4 (by linarith)
    (by norm_num) (by norm_num)
  refine ⟨C, hC0, fun N k p hp => ?_⟩
  have hM := meshData (n := n) N
  have hΩ := (isOpen_mesh_domain n N).measurableSet
  have hstar : StarShaped.StarBall (mesh n N).domain (center n) (1 / 4) := starBall_mesh n N
  have hRx : ∀ y ∈ closure (mesh n N).domain, ‖y - center n‖ ≤ 1 / 4 := fun y hy =>
    norm_sub_center_le (by rwa [mesh_domain] at hy)
  have hint := StarShaped.interior_subset_domain hstar (by norm_num)
  have hhR := StarShaped.meshSize_le_two_mul (by norm_num) hRx
  have hpA := hp.starShaped
  have hγh : γ / 4 * (mesh n N).meshSize / (1 / 4) ≤ 1 / 4 := by
    rw [meshSize_mesh]; have := hN_le N; have := hN_pos N; field_simp; nlinarith
  have hθ := mul_lt_mul_of_pos_right hK₀ hγ4
  have hclose' := hclose (γ / 4) hγ4 (by linarith) (mesh n N) hM hΩ hint (by norm_num) hRx hhR
    (by norm_num) p hpA k
  refine ⟨hbound (mesh n N) hM hΩ (by norm_num) hRx (by linarith) p hpA k, fun hmax u hu => ?_,
    fun hmin u hu => ?_⟩
  · exact hclose' (StarShaped.geomOK_of_isMaximal hM one_pos hC hstar (by norm_num) hmax hpA
      (by norm_num) hRx (by norm_num) hγ4 hθ k) u hu (StarShaped.sampleOK_of_isMaximal hstar hmax u)
  · exact hclose' (StarShaped.geomOK_of_isMinimal hM one_pos hC hstar (by norm_num) hint hmin hpA
      (by norm_num) hRx (by norm_num) (by norm_num) hγ4 (by linarith) hθ k) u
      ((whitneyElement n).globalSpace₀_le (mesh n N) k hu)
      (StarShaped.sampleOK_of_isMinimal hM one_pos hC hstar (by norm_num) hpA (by norm_num) hRx
        (by norm_num) hγ4 hθ hu)

/-- **The smoothing estimates from estimates on the mesh**: a uniform `L²` bound of the smoothed
interpolants and `‖v - Q_N v‖ ≤ ½ ‖v‖` on the global Whitney fields give
`SmoothingEstimates n p (max C ½)`. -/
theorem smoothingEstimates_of {p : ℕ → SmoothingParam (Fin n → ℝ)}
    (hp : ∀ N, (p N).IsMaximal (center n) (1 / 4)) {C : ℝ}
    (hb : ∀ N (k : ℕ) x, ‖(whitneyElement n).smoothedInterp (mesh n N) (p N)
      (isOpen_mesh_domain n N).measurableSet k x‖ ≤ C * ‖x‖)
    (hc : ∀ N (k : ℕ), ∀ u ∈ (whitneyElement n).globalSpace (mesh n N) k,
      ‖(whitneyElement n).glue (mesh n N) k u - (whitneyElement n).smoothedInterp (mesh n N)
        (p N) (isOpen_mesh_domain n N).measurableSet k ((whitneyElement n).glue (mesh n N) k u)‖ ≤
        1 / 2 * ‖(whitneyElement n).glue (mesh n N) k u‖) :
    SmoothingEstimates n p (max C (1 / 2)) := by
  have hest : ∀ N, (∀ i x, ‖(smoothed n N (p N) (hp N)).Q i x‖ ≤ max C (1 / 2) * ‖x‖) ∧
      ∀ i, ∀ v ∈ (whitney n N).V i, ‖v - (smoothed n N (p N) (hp N)).Q i v‖ ≤ 1 / 2 * ‖v‖ := by
    intro N
    refine commutingMapOfEq_estimates (mesh_domain n N) (isOpen_mesh_domain n N)
      (isOpen_cubeDomain n) _ (fun i x => ?_) (fun i v hv => ?_)
    · rw [LocalElement.smoothedCommutingMap_Q]
      rcases i with k | k
      · exact (hb N k x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
    · rw [LocalElement.smoothedCommutingMap_Q]
      rcases i with k | k
      · obtain ⟨u, rfl⟩ := hv
        exact hc N k u.1 u.2
      · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
  exact ⟨hp, le_max_right _ _, fun N => (hest N).1, fun N => (hest N).2⟩

/-- **The smoothing estimates with vanishing boundary DOFs from estimates on the mesh**
(`smoothingEstimates_of` for `V̊ₕ`). -/
theorem smoothingEstimatesMin_of {p : ℕ → SmoothingParam (Fin n → ℝ)}
    (hp : ∀ N, (p N).IsMinimal (center n) (1 / 4)) {C : ℝ}
    (hb : ∀ N (k : ℕ) x, ‖(whitneyElement n).smoothedInterp (mesh n N) (p N)
      (isOpen_mesh_domain n N).measurableSet k x‖ ≤ C * ‖x‖)
    (hc : ∀ N (k : ℕ), ∀ u ∈ (whitneyElement n).globalSpace₀ (mesh n N) k,
      ‖(whitneyElement n).glue (mesh n N) k u - (whitneyElement n).smoothedInterp (mesh n N)
        (p N) (isOpen_mesh_domain n N).measurableSet k ((whitneyElement n).glue (mesh n N) k u)‖ ≤
        1 / 2 * ‖(whitneyElement n).glue (mesh n N) k u‖) :
    SmoothingEstimatesMin n p (max C (1 / 2)) := by
  have hest : ∀ N, (∀ i x, ‖(smoothedMin n N (p N) (hp N)).Q i x‖ ≤ max C (1 / 2) * ‖x‖) ∧
      ∀ i, ∀ v ∈ (whitneyMin n N).V i,
        ‖v - (smoothedMin n N (p N) (hp N)).Q i v‖ ≤ 1 / 2 * ‖v‖ := by
    intro N
    refine commutingMapOfEqMin_estimates (mesh_domain n N) (isOpen_mesh_domain n N)
      (isOpen_cubeDomain n) _ (fun i x => ?_) (fun i v hv => ?_)
    · rw [LocalElement.smoothedCommutingMapMin_Q]
      rcases i with k | k
      · exact (hb N k x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
    · rw [LocalElement.smoothedCommutingMapMin_Q]
      rcases i with k | k
      · obtain ⟨u, rfl⟩ := hv
        exact hc N k u.1 u.2
      · exact (norm_eq_zero_negSucc k _).le.trans (by positivity)
  exact ⟨hp, le_max_right _ _, fun N => (hest N).1, fun N => (hest N).2⟩

/-- **The Whitney smoothing estimates for all small `γ`** ([AFW2010], §5.5;
[ChristiansenWinther2008]): for every `γ ∈ (0, γ₀]`, `γ₀` depending only on `n`, the parameters
`pMax γ` (dilation factor `1 - γ h_N` about the centre, bump radii `γ h_N / 64 < γ h_N / 32`)
satisfy `FEM.SmoothingEstimates`. -/
theorem smoothingEstimates_pMax_forall :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 / 2 ∧ ∀ (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1), γ ≤ γ₀ →
      ∃ C, SmoothingEstimates n (pMax γ hγ hγ1) C := by
  obtain ⟨γ₀, hγ₀, hγ₀2, h⟩ := exists_gamma₀ n
  refine ⟨γ₀, hγ₀, hγ₀2, fun γ hγ hγ1 hγγ₀ => ?_⟩
  obtain ⟨C, -, h⟩ := h γ hγ hγγ₀
  exact ⟨_, smoothingEstimates_of (fun N => pMax_isMaximal N)
    (fun N k => (h N k _ (pMax_isAdm N)).1)
    (fun N k => (h N k _ (pMax_isAdm N)).2.1 (pMax_isMaximal N))⟩

/-- **The Whitney smoothing estimates with vanishing boundary DOFs for all small `γ`**: as
`smoothingEstimates_pMax_forall`, for the parameters `pMin γ` (dilation factor `1 + γ h_N` towards
the centre). -/
theorem smoothingEstimatesMin_pMin_forall :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ 1 / 2 ∧ ∀ (γ : ℝ) (hγ : 0 < γ), γ ≤ γ₀ →
      ∃ C, SmoothingEstimatesMin n (pMin γ hγ) C := by
  obtain ⟨γ₀, hγ₀, hγ₀2, h⟩ := exists_gamma₀ n
  refine ⟨γ₀, hγ₀, hγ₀2, fun γ hγ hγγ₀ => ?_⟩
  obtain ⟨C, -, h⟩ := h γ hγ hγγ₀
  exact ⟨_, smoothingEstimatesMin_of (fun N => pMin_isMinimal N)
    (fun N k => (h N k _ (pMin_isAdm N)).1)
    (fun N k => (h N k _ (pMin_isAdm N)).2.2 (pMin_isMinimal N))⟩

/-- **The smoothed-projection estimates hold on the Freudenthal meshes of the cube**
([AFW2010], §5.5; [ChristiansenWinther2008]): for the parameters `pMax γ` (dilation factor
`1 - γ h_N` about the centre, bump radii `γ h_N / 64 < γ h_N / 32`) with `γ` small depending only on
`n`, the smoothed interpolants `Q_N = Π_h R_N` are bounded in `L²` uniformly in `N`, and
`‖v - Q_N v‖ ≤ ½ ‖v‖` on the Whitney spaces. -/
theorem smoothingEstimates_pMax :
    ∃ (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (C : ℝ), SmoothingEstimates n (pMax γ hγ hγ1) C := by
  obtain ⟨γ₀, hγ₀, hγ₀2, h⟩ := smoothingEstimates_pMax_forall (n := n)
  exact ⟨γ₀, hγ₀, by linarith, h γ₀ hγ₀ (by linarith) le_rfl⟩

/-- **The smoothed-projection estimates with vanishing boundary DOFs hold on the Freudenthal
meshes of the cube** ([AFW2010], §5.5; [ChristiansenWinther2008]): for the parameters `pMin γ`
(dilation factor `1 + γ h_N` towards the centre, bump radii `γ h_N / 64 < γ h_N / 32`) with `γ`
small depending only on `n`, the smoothed interpolants `Q̊_N = Π_h R_N` of the Whitney complexes
with vanishing boundary DOFs are bounded in `L²` uniformly in `N`, and `‖v - Q̊_N v‖ ≤ ½ ‖v‖`
on `V̊ₕ`. The samples of the smoother outside `Q` only meet faces lying in boundary facets, where
the DOFs of `V̊ₕ` vanish (`StarShaped.sampleOK_of_isMinimal`). -/
theorem smoothingEstimatesMin_pMin :
    ∃ (γ : ℝ) (hγ : 0 < γ) (C : ℝ), SmoothingEstimatesMin n (pMin γ hγ) C := by
  obtain ⟨γ₀, hγ₀, -, h⟩ := smoothingEstimatesMin_pMin_forall (n := n)
  exact ⟨γ₀, hγ₀, h γ₀ hγ₀ le_rfl⟩

/-- **The smoothed-projection estimates hold on the Freudenthal meshes of the cube**, as an
existence statement over the parameters (`smoothingEstimates_pMax` with the parameters `pMax γ`
made explicit). -/
theorem smoothingEstimates_exists :
    ∃ (p : ℕ → SmoothingParam (Fin n → ℝ)) (C : ℝ), SmoothingEstimates n p C := by
  obtain ⟨γ, hγ, hγ1, C, h⟩ := smoothingEstimates_pMax (n := n)
  exact ⟨_, C, h⟩

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
graph norms ([AFW2010], §5.5). -/
theorem exists_uniform_cochainProjection :
    ∃ C : ℝ, ∀ N, ∃ π : (whitney n N).CochainProjection,
      (∀ i x, ‖π.π i x‖ ≤ C * ‖x‖) ∧ ∀ i j, π.IsGraphBounded i j C := by
  obtain ⟨p, C, hE⟩ := smoothingEstimates_exists (n := n)
  exact ⟨2 * C, fun N => ⟨hE.proj N, hE.norm_proj_le N, fun i j =>
    (hE.proj N).isGraphBounded_of_norm_le (hE.norm_proj_le N i) (hE.norm_proj_le N j)⟩⟩

/-- **Uniformly bounded cochain projections onto the Whitney complexes with vanishing boundary
DOFs** (unconditionally), in `L²` and in the graph norms of `H̊Λ(Q)`. -/
theorem exists_uniform_cochainProjectionMin :
    ∃ C : ℝ, ∀ N, ∃ π : (whitneyMin n N).CochainProjection,
      (∀ i x, ‖π.π i x‖ ≤ C * ‖x‖) ∧ ∀ i j, π.IsGraphBounded i j C := by
  obtain ⟨p, C, hE⟩ := smoothingEstimatesMin_exists (n := n)
  exact ⟨2 * C, fun N => ⟨hE.proj N, hE.norm_proj_le N, fun i j =>
    (hE.proj N).isGraphBounded_of_norm_le (hE.norm_proj_le N i) (hE.norm_proj_le N j)⟩⟩

end Feec.Models.Cube.FEM
