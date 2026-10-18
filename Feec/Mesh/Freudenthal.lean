module

public import Feec.Mesh.Kuhn

/-!
# Freudenthal triangulations of boxes and their uniform refinement

The Freudenthal triangulation of `ℝⁿ` consists of the integer translates `m + K_σ` of the Kuhn
simplices (`Feec.Mesh.freudenthalSimplex`); it is globally defined by ordering fractional parts:
a point `x` lies in `⌊x⌋ + K_σ` for every `σ` sorting `fract x` decreasingly, and in no other
translate unless it lies on one of the hyperplanes `xᵢ ∈ ℤ`, `xᵢ - xⱼ ∈ ℤ`. Its face-to-face
property is `inter_closedInterior_freudenthalSimplex`.

For `N ≥ 1`, the level-`N` Freudenthal mesh of the box `∏ (bᵢ, bᵢ + s)` is the image of the
triangulation of `(0, N)ⁿ` by the cells `m + K_σ`, `m ∈ {0, …, N-1}ⁿ`, under
`x ↦ b + (s / N) x`; its simplices are `b + (s/N)(m + K_σ)` ([Freudenthal1942]; [Bey2000]).

## Main definitions

* `latticeMesh n N`: the `N ⁿ n!` simplices `m + K_σ`, `0 ≤ mᵢ < N`, as a mesh of `(0, N)ⁿ`.
* `boxMap b h`: the affine map `x ↦ b + h x`.
* `freudenthalMesh b s hs N`: the level-`N` Freudenthal mesh of `∏ (bᵢ, bᵢ + s)`.

## Main results

* `mem_freudenthalSet_floor`, `eq_floor_of_mem_freudenthalSet`: `x ∈ ⌊x⌋ + K_σ` for `σ` sorting
  `fract x`, and off the hyperplanes `xᵢ ∈ ℤ`, `xᵢ - xⱼ ∈ ℤ` this simplex is unique.
* `iUnion_freudenthalSet`: the cells `m + K_σ`, `0 ≤ mᵢ < N`, cover `[0, N]ⁿ`.
* `latticeMesh`, `freudenthalMesh`: conforming meshes (conformity across neighbouring cells is
  the face-to-face property of the global Freudenthal triangulation).
* `smul_mem_freudenthalSet`: `M⁻¹ (m + K_σ) ⊆ m' + K_σ'` with `m' = ⌊c / M⌋` for the interior
  point `c = m + g_σ`; hence `freudenthalMesh_refines`: **the level-`N M` mesh refines the level-`N`
  mesh**.
* `diam_of_mem_freudenthalMesh`, `meshSize_freudenthalMesh`: `h_T = h = s / N` (sup norm).
* `volume_freudenthalMesh_simplex`: each simplex of the level-`N` mesh has volume
  `(s / N)ⁿ / n!`.
* Symmetries: `neg_mem_freudenthalSet_iff` (the central symmetry `x ↦ -x` maps `m + K_σ` to
  `(-m - 1) + K_{σ ∘ rev}`) and `comp_mem_freudenthalSet_iff` (coordinate permutations).
* `reflect_kuhnSet_ne`: the Freudenthal triangulation is **not** invariant under a single
  reflection `x₀ ↦ -x₀` (`n = 2`): the reflected Kuhn simplex `{(-a, b) | 1 ≥ a ≥ b ≥ 0}` is not a
  Freudenthal simplex (its diagonal runs along `x₀ + x₁ = 0`). So a mesh of `(-½, ½)ⁿ` symmetric
  under the reflections `x_k ↦ -x_k` is not a Freudenthal mesh; the parity models use the
  Freudenthal mesh of `(0, ½)ⁿ` instead.

## References

* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]
* [H. W. Kuhn, *Some combinatorial lemmas in topology*][Kuhn1960]
* [J. Bey, *Simplicial grid refinement: on Freudenthal's algorithm and the optimal number of congruence classes*][Bey2000]
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (simplicial meshes)
-/

@[expose] public section

noncomputable section

open Set

namespace Feec.Mesh

variable {n : ℕ}

/-! ### Position of `m + K_σ` relative to its interior point `c = m + g_σ` -/

section Sign

variable {m : Fin n → ℤ} {σ : Equiv.Perm (Fin n)} {x : Fin n → ℝ}

/-- The interior point `c = m + g_σ` of `m + K_σ`. -/
def freudenthalCenter (m : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) : Fin n → ℝ :=
  latticePoint m + kuhnCenter σ

theorem freudenthalCenter_apply (m : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    freudenthalCenter m σ i = m i + kuhnCenter σ i := rfl

theorem le_apply_of_le_center (hx : x ∈ freudenthalSet m σ) (i : Fin n) {K : ℤ}
    (hK : (K : ℝ) ≤ freudenthalCenter m σ i) : (K : ℝ) ≤ x i := by
  have h0 := (hx.1 i).1
  have g1 := kuhnCenter_lt_one σ i
  simp only [Pi.sub_apply, latticePoint_apply] at h0
  rw [freudenthalCenter_apply] at hK
  have h1 : (K : ℝ) < ((m i + 1 : ℤ) : ℝ) := by push_cast; linarith
  have h2 : (K : ℝ) ≤ (m i : ℝ) := by exact_mod_cast (by have := Int.cast_lt.1 h1; omega : K ≤ m i)
  linarith

theorem apply_le_of_center_le (hx : x ∈ freudenthalSet m σ) (i : Fin n) {K : ℤ}
    (hK : freudenthalCenter m σ i ≤ K) : x i ≤ K := by
  have h1 := (hx.1 i).2
  have g0 := kuhnCenter_pos σ i
  simp only [Pi.sub_apply, latticePoint_apply] at h1
  rw [freudenthalCenter_apply] at hK
  have h2 : ((m i : ℤ) : ℝ) < (K : ℝ) := by linarith
  have h3 : ((m i + 1 : ℤ) : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast (by have := Int.cast_lt.1 h2; omega : m i + 1 ≤ K)
  push_cast at h3
  linarith

theorem sub_le_of_center_sub_le (hx : x ∈ freudenthalSet m σ) (i j : Fin n) {K : ℤ}
    (hK : freudenthalCenter m σ j - freudenthalCenter m σ i ≤ K) : x j - x i ≤ K := by
  have hy := hx.1
  have hi0 := (hy i).1
  have hj1 := (hy j).2
  simp only [Pi.sub_apply, latticePoint_apply] at hi0 hj1
  rw [freudenthalCenter_apply, freudenthalCenter_apply] at hK
  have hg := kuhnCenter_sub σ j i
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hi' : ((σ.symm i : ℕ) : ℝ) < n := by exact_mod_cast (σ.symm i).2
  have hj' : ((σ.symm j : ℕ) : ℝ) < n := by exact_mod_cast (σ.symm j).2
  rcases lt_or_ge (σ.symm j) (σ.symm i) with hlt | hle
  · -- `g_j > g_i`
    have hpos : 0 < kuhnCenter σ j - kuhnCenter σ i := by
      rw [hg]
      apply div_pos _ hn
      have : ((σ.symm j : ℕ) : ℝ) < (σ.symm i : ℕ) := by exact_mod_cast hlt
      linarith
    have h1 : ((m j - m i : ℤ) : ℝ) < K := by push_cast; linarith
    have h2 : ((m j - m i + 1 : ℤ) : ℝ) ≤ K := by
      exact_mod_cast (by have := Int.cast_lt.1 h1; omega : m j - m i + 1 ≤ K)
    push_cast at h2
    linarith
  · -- `g_j > g_i - 1` and `y_j ≤ y_i`
    have hgt : -1 < kuhnCenter σ j - kuhnCenter σ i := by
      rw [hg, lt_div_iff₀ hn]
      have : (0 : ℝ) ≤ (σ.symm i : ℕ) := Nat.cast_nonneg _
      linarith
    have hanti := hx.2 hle
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Pi.sub_apply,
      latticePoint_apply] at hanti
    have h1 : ((m j - m i - 1 : ℤ) : ℝ) < K := by push_cast; linarith
    have h2 : ((m j - m i : ℤ) : ℝ) ≤ K := by
      exact_mod_cast (by have := Int.cast_lt.1 h1; omega : m j - m i ≤ K)
    push_cast at h2
    linarith

/-- **Refinement of the Freudenthal triangulation.** For `M ≥ 1`, the shrunk simplex
`M⁻¹ (m + K_σ)` lies in the simplex `m' + K_σ'` with `m' = ⌊c / M⌋` and `σ'` sorting
`fract (c / M)` decreasingly, `c = m + g_σ`. -/
theorem smul_mem_freudenthalSet {M : ℕ} (hM : 0 < M) (hx : x ∈ freudenthalSet m σ) :
    (M : ℝ)⁻¹ • x ∈ freudenthalSet (fun i => ⌊freudenthalCenter m σ i / M⌋)
      (Tuple.sort fun i => -Int.fract (freudenthalCenter m σ i / M)) := by
  set c := freudenthalCenter m σ with hc
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, latticePoint_apply, sub_nonneg]
    have h1 : ((M * ⌊c i / M⌋ : ℤ) : ℝ) ≤ c i := by
      have := Int.floor_le (c i / M)
      rw [le_div_iff₀ hMpos] at this
      push_cast; linarith
    have := le_apply_of_le_center hx i h1
    push_cast at this
    rw [le_inv_mul_iff₀ hMpos]; linarith
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, latticePoint_apply, sub_le_iff_le_add]
    have h1 : c i ≤ ((M * (⌊c i / M⌋ + 1) : ℤ) : ℝ) := by
      have := Int.lt_floor_add_one (c i / M)
      rw [div_lt_iff₀ hMpos] at this
      push_cast; linarith
    have := apply_le_of_center_le hx i h1
    push_cast at this
    rw [inv_mul_le_iff₀ hMpos]; linarith
  · intro a b hab
    have hsort := Tuple.monotone_sort (fun i => -Int.fract (c i / M)) hab
    set σ' := Tuple.sort fun i => -Int.fract (c i / M)
    simp only [Function.comp_apply, neg_le_neg_iff, Int.fract] at hsort
    simp only [Function.comp_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, latticePoint_apply]
    set j := σ' b
    set i := σ' a
    have key : c j - c i ≤ ((M * (⌊c j / M⌋ - ⌊c i / M⌋) : ℤ) : ℝ) := by
      have : (c j - c i) / M ≤ (⌊c j / M⌋ : ℝ) - ⌊c i / M⌋ := by rw [sub_div]; linarith
      rw [div_le_iff₀ hMpos] at this
      push_cast; linarith
    have h := sub_le_of_center_sub_le hx i j key
    push_cast at h
    have h' := (inv_mul_le_iff₀ hMpos).2 h
    rw [mul_sub] at h'
    linarith

end Sign

/-! ### The triangulation is defined by ordering fractional parts -/

/-- **Ordering fractional parts.** Every `x ∈ ℝⁿ` lies in `⌊x⌋ + K_σ` for `σ` sorting `fract x`
decreasingly. -/
theorem mem_freudenthalSet_floor (x : Fin n → ℝ) :
    x ∈ freudenthalSet (fun i => ⌊x i⌋) (Tuple.sort fun i => -Int.fract (x i)) := by
  have hy : x - latticePoint (fun i => ⌊x i⌋) = fun i => Int.fract (x i) := by
    funext i; simp only [Pi.sub_apply, latticePoint_apply, Int.self_sub_floor]
  refine ⟨fun i => ?_, fun a b hab => ?_⟩
  · rw [hy]; exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  · rw [hy]
    have := Tuple.monotone_sort (fun i => -Int.fract (x i)) hab
    simp only [Function.comp_apply, neg_le_neg_iff] at this ⊢
    exact this

/-- Off the hyperplanes `xᵢ ∈ ℤ` (`fract xᵢ = 0`) and `xᵢ - xⱼ ∈ ℤ` (`fract xᵢ = fract xⱼ`),
`⌊x⌋ + K_σ` with `σ` sorting `fract x` is the only Freudenthal simplex containing `x`. -/
theorem eq_floor_of_mem_freudenthalSet {m : Fin n → ℤ} {σ : Equiv.Perm (Fin n)}
    {x : Fin n → ℝ} (hx : x ∈ freudenthalSet m σ) (h1 : ∀ i, Int.fract (x i) ≠ 0)
    (h2 : ∀ i j, i ≠ j → Int.fract (x i) ≠ Int.fract (x j)) :
    m = (fun i => ⌊x i⌋) ∧ σ = Tuple.sort fun i => -Int.fract (x i) := by
  have hm : m = fun i => ⌊x i⌋ := by
    funext i
    have h0 := (hx.1 i).1
    have h1' := (hx.1 i).2
    simp only [Pi.sub_apply, latticePoint_apply] at h0 h1'
    have hne : x i ≠ ((m i + 1 : ℤ) : ℝ) := by
      intro h; exact h1 i (by rw [h, Int.fract_intCast])
    push_cast at hne
    exact (Int.floor_eq_iff.2 ⟨by linarith, lt_of_le_of_ne (by linarith) hne⟩).symm
  subst hm
  refine ⟨rfl, eq_of_mem_kuhnSet_of_injective (x := fun i => Int.fract (x i))
    (fun i j h => by_contra fun hij => h2 i j hij h) ?_ ?_⟩
  · have := hx
    simp only [freudenthalSet, Set.mem_ofPred_eq] at this
    convert this using 1
    funext i; simp only [Pi.sub_apply, latticePoint_apply, Int.self_sub_floor]
  · have := mem_freudenthalSet_floor x
    simp only [freudenthalSet, Set.mem_ofPred_eq] at this
    convert this using 1
    funext i; simp only [Pi.sub_apply, latticePoint_apply, Int.self_sub_floor]

/-! ### The Freudenthal mesh of `(0, N)ⁿ` -/

/-- The lattice point of `m ∈ {0, …, N-1}ⁿ`. -/
def finLattice {N : ℕ} (m : Fin n → Fin N) : Fin n → ℤ := fun i => ((m i : ℕ) : ℤ)

theorem finLattice_injective {N : ℕ} : Function.Injective (finLattice (n := n) (N := N)) := by
  intro m m' h
  funext i
  have := congrFun h i
  simp only [finLattice, Nat.cast_inj] at this
  exact Fin.ext this

/-- The cells `m + K_σ`, `0 ≤ mᵢ < N`, cover `[0, N]ⁿ`. -/
theorem iUnion_freudenthalSet (N : ℕ) [NeZero N] :
    ⋃ p : (Fin n → Fin N) × Equiv.Perm (Fin n), freudenthalSet (finLattice p.1) p.2 =
      Set.Icc 0 fun _ => (N : ℝ) := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  apply subset_antisymm
  · refine Set.iUnion_subset fun p x hx => ⟨fun i => ?_, fun i => ?_⟩
    · have := (hx.1 i).1
      simp only [Pi.sub_apply, latticePoint_apply, finLattice] at this
      have : (0 : ℝ) ≤ ((p.1 i : ℕ) : ℤ) := by positivity
      simp only [Pi.zero_apply]; linarith
    · have := (hx.1 i).2
      simp only [Pi.sub_apply, latticePoint_apply, finLattice] at this
      have h2 : ((p.1 i : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast (p.1 i).2
      push_cast at this; linarith
  · intro x hx
    have h0 : ∀ i, 0 ≤ x i := hx.1
    have hN' : ∀ i, x i ≤ N := hx.2
    set m : Fin n → Fin N := fun i => ⟨min ⌊x i⌋₊ (N - 1), by omega⟩
    have hm : ∀ i, 0 ≤ x i - (m i : ℕ) ∧ x i - (m i : ℕ) ≤ 1 := by
      intro i
      simp only [m]
      rcases le_total ⌊x i⌋₊ (N - 1) with h | h
      · rw [min_eq_left h]
        exact ⟨by linarith [Nat.floor_le (h0 i)], by linarith [Nat.lt_floor_add_one (x i)]⟩
      · rw [min_eq_right h]
        have h1 : ((N - 1 : ℕ) : ℝ) ≤ x i :=
          (by exact_mod_cast h : ((N - 1 : ℕ) : ℝ) ≤ ⌊x i⌋₊).trans (Nat.floor_le (h0 i))
        have h2 : ((N - 1 : ℕ) : ℝ) = N - 1 := by rw [Nat.cast_sub hN, Nat.cast_one]
        constructor <;> linarith [hN' i]
    have hy : ∀ i, (x - latticePoint (finLattice m)) i = x i - (m i : ℕ) := fun i => by
      simp [finLattice]
    refine Set.mem_iUnion.2 ⟨(m, Tuple.sort fun i => -(x - latticePoint (finLattice m)) i),
      fun i => ?_, fun a b hab => ?_⟩
    · rw [hy]; exact hm i
    · have := Tuple.monotone_sort (fun i => -(x - latticePoint (finLattice m)) i) hab
      simp only [Function.comp_apply, neg_le_neg_iff] at this ⊢
      exact this

theorem closure_box (N : ℕ) [NeZero N] :
    closure (Set.univ.pi fun _ : Fin n => Set.Ioo (0 : ℝ) N) = Set.Icc 0 fun _ => (N : ℝ) := by
  rw [closure_pi_set]
  have hN : (0 : ℝ) ≠ N := by exact_mod_cast (NeZero.ne N).symm
  simp only [closure_Ioo hN]
  exact Set.pi_univ_Icc 0 _

/-- The Freudenthal mesh of `(0, N)ⁿ`: the simplices `m + K_σ`, `0 ≤ mᵢ < N`. -/
def latticeMesh (n N : ℕ) [NeZero N] : SimplicialMesh n := by
  classical
  exact SimplicialMesh.ofConforming
    (Finset.univ.image fun p : (Fin n → Fin N) × Equiv.Perm (Fin n) =>
      freudenthalSimplex (finLattice p.1) p.2)
    (Set.univ.pi fun _ => Set.Ioo (0 : ℝ) N)
    (by
      rw [closure_box, ← iUnion_freudenthalSet, Finset.set_biUnion_finset_image]
      simp [closedInterior_freudenthalSimplex])
    (by
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      rintro _ ⟨p, rfl⟩ _ ⟨p', rfl⟩
      exact inter_closedInterior_freudenthalSimplex _ _ _ _)
    (by
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      rintro _ ⟨p, rfl⟩ _ ⟨p', rfl⟩ h
      obtain ⟨h1, h2⟩ := freudenthalSimplex_eq_of_closedInterior_eq (m := finLattice p.1)
        (m' := finLattice p'.1) (σ := p.2) (σ' := p'.2) (by
          rw [← convexHull_vertexSet, h, convexHull_vertexSet])
      simp only
      rw [h1, h2])

theorem mem_latticeMesh_simplices {N : ℕ} [NeZero N] {T : Affine.Simplex ℝ (Fin n → ℝ) n} :
    T ∈ (latticeMesh n N).simplices ↔
      ∃ (m : Fin n → Fin N) (σ : Equiv.Perm (Fin n)), freudenthalSimplex (finLattice m) σ = T := by
  classical
  simp [latticeMesh, SimplicialMesh.ofConforming]

@[simp] theorem latticeMesh_domain (N : ℕ) [NeZero N] :
    (latticeMesh n N).domain = Set.univ.pi fun _ => Set.Ioo (0 : ℝ) N := rfl

/-! ### The Freudenthal mesh of a box -/

/-- The affine map `x ↦ b + h x`. -/
def boxMap (b : Fin n → ℝ) (h : ℝ) (hh : h ≠ 0) : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ) :=
  (LinearEquiv.smulOfNeZero ℝ (Fin n → ℝ) h hh).toAffineEquiv.trans
    (AffineEquiv.constVAdd ℝ (Fin n → ℝ) b)

@[simp] theorem boxMap_apply (b : Fin n → ℝ) (h : ℝ) (hh : h ≠ 0) (x : Fin n → ℝ) :
    boxMap b h hh x = b + h • x := by
  simp [boxMap]

theorem freudenthalScale_ne_zero {s : ℝ} (hs : 0 < s) (N : ℕ) [NeZero N] : s / N ≠ 0 :=
  div_ne_zero hs.ne' (by exact_mod_cast NeZero.ne N)

/-- **The level-`N` Freudenthal mesh** of the box `∏ (bᵢ, bᵢ + s)`: the simplices
`b + (s / N)(m + K_σ)`, `m ∈ {0, …, N-1}ⁿ`, `σ ∈ 𝔖ₙ`. -/
def freudenthalMesh (b : Fin n → ℝ) (s : ℝ) (hs : 0 < s) (N : ℕ) [NeZero N] :
    SimplicialMesh n :=
  (latticeMesh n N).map (boxMap b (s / N) (freudenthalScale_ne_zero hs N))

theorem mem_freudenthalMesh_simplices {b : Fin n → ℝ} {s : ℝ} {hs : 0 < s} {N : ℕ} [NeZero N]
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} :
    T ∈ (freudenthalMesh b s hs N).simplices ↔ ∃ (m : Fin n → Fin N) (σ : Equiv.Perm (Fin n)),
      mapEquiv (boxMap b (s / N) (freudenthalScale_ne_zero hs N))
        (freudenthalSimplex (finLattice m) σ) = T := by
  rw [freudenthalMesh, SimplicialMesh.mem_map_simplices]
  constructor
  · rintro ⟨T', hT', rfl⟩
    obtain ⟨m, σ, rfl⟩ := mem_latticeMesh_simplices.1 hT'
    exact ⟨m, σ, rfl⟩
  · rintro ⟨m, σ, rfl⟩
    exact ⟨_, mem_latticeMesh_simplices.2 ⟨m, σ, rfl⟩, rfl⟩

theorem freudenthalMesh_domain (b : Fin n → ℝ) (s : ℝ) (hs : 0 < s) (N : ℕ) [NeZero N] :
    (freudenthalMesh b s hs N).domain = Set.univ.pi fun i => Set.Ioo (b i) (b i + s) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hh : 0 < s / N := div_pos hs hN
  ext x
  simp only [freudenthalMesh, SimplicialMesh.map_domain, latticeMesh_domain, Set.mem_image,
    boxMap_apply, Set.mem_univ_pi, Set.mem_Ioo]
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    have := hy i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · nlinarith [this.1]
    · have : s / N * y i < s / N * N := mul_lt_mul_of_pos_left this.2 hh
      rw [div_mul_cancel₀ s hN.ne'] at this; linarith
  · intro hx
    refine ⟨(s / N)⁻¹ • (x - b), fun i => ?_, ?_⟩
    · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, inv_div]
      have := hx i
      constructor
      · apply mul_pos (div_pos hN hs); linarith
      · rw [div_mul_eq_mul_div, div_lt_iff₀ hs]
        nlinarith [this.2]
    · funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      ring

theorem closedInterior_freudenthalMesh_simplex (b : Fin n → ℝ) {h : ℝ} (hh : h ≠ 0)
    (m : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    (mapEquiv (boxMap b h hh) (freudenthalSimplex m σ)).closedInterior =
      (fun x => b + h • x) '' freudenthalSet m σ := by
  rw [closedInterior_mapEquiv, closedInterior_freudenthalSimplex]
  congr 1

/-- **Uniform refinement.** The level-`N M` Freudenthal mesh of a box refines the level-`N`
mesh. -/
theorem freudenthalMesh_refines (b : Fin n → ℝ) (s : ℝ) (hs : 0 < s) (N M : ℕ) [NeZero N]
    [NeZero M] :
    (freudenthalMesh b s hs (N * M)).Refines (freudenthalMesh b s hs N) := by
  intro T hT
  obtain ⟨m, σ, rfl⟩ := mem_freudenthalMesh_simplices.1 hT
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set c := freudenthalCenter (finLattice m) σ with hc
  -- the coarse cell `m' = ⌊c / M⌋ ∈ {0, …, N-1}ⁿ`
  have hc0 : ∀ i, 0 < c i / M := fun i => by
    apply div_pos _ hMr
    rw [hc, freudenthalCenter_apply]
    have := kuhnCenter_pos σ i
    have : (0 : ℝ) ≤ (finLattice m i : ℝ) := by simp [finLattice]
    linarith
  have hcN : ∀ i, c i / M < N := fun i => by
    rw [div_lt_iff₀ hMr, hc, freudenthalCenter_apply]
    have := kuhnCenter_lt_one σ i
    have h1 : (finLattice m i : ℝ) + 1 ≤ N * M := by
      simp only [finLattice, Int.cast_natCast]
      exact_mod_cast (m i).2
    linarith
  have hfl0 : ∀ i, 0 ≤ ⌊c i / M⌋ := fun i => Int.floor_nonneg.2 (hc0 i).le
  have hflN : ∀ i, ⌊c i / M⌋ < N := fun i => Int.floor_lt.2 (by exact_mod_cast hcN i)
  set m' : Fin n → Fin N := fun i => ⟨(⌊c i / M⌋).toNat, by
    have := hflN i; have := hfl0 i; omega⟩
  have hm' : finLattice m' = fun i => ⌊c i / M⌋ := by
    funext i; simp only [finLattice, m']; exact Int.toNat_of_nonneg (hfl0 i)
  set σ' := Tuple.sort fun i => -Int.fract (c i / M)
  refine ⟨_, mem_freudenthalMesh_simplices.2 ⟨m', σ', rfl⟩, ?_⟩
  rw [closedInterior_freudenthalMesh_simplex, closedInterior_freudenthalMesh_simplex]
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨(M : ℝ)⁻¹ • x, ?_, ?_⟩
  · rw [hm']; exact smul_mem_freudenthalSet hM hx
  · simp only [smul_smul]
    congr 2
    push_cast
    field_simp

/-! ### Mesh size -/

theorem diam_freudenthalMesh_simplex [NeZero n] (b : Fin n → ℝ) {h : ℝ} (hh : 0 < h)
    (m : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    diam (mapEquiv (boxMap b h hh.ne') (freudenthalSimplex m σ)) = h := by
  set T := mapEquiv (boxMap b h hh.ne') (freudenthalSimplex m σ)
  have hcl := closedInterior_freudenthalMesh_simplex b hh.ne' m σ
  apply le_antisymm
  · refine Metric.diam_le_of_forall_dist_le hh.le fun p hp q hq => ?_
    rw [hcl] at hp hq
    obtain ⟨x, hx, rfl⟩ := hp
    obtain ⟨y, hy, rfl⟩ := hq
    rw [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg hh.le]
    refine mul_le_of_le_one_right hh.le ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_)
    have hx0 := (hx.1 i).1
    have hx1 := (hx.1 i).2
    have hy0 := (hy.1 i).1
    have hy1 := (hy.1 i).2
    simp only [Pi.sub_apply, latticePoint_apply] at hx0 hx1 hy0 hy1
    rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  · have h0 : T.points 0 ∈ T.closedInterior := T.point_mem_closedInterior 0
    have h1 : T.points (Fin.last n) ∈ T.closedInterior := T.point_mem_closedInterior _
    have hd := Metric.dist_le_diam_of_mem T.isCompact_closedInterior.isBounded h0 h1
    refine le_of_eq_of_le ?_ hd
    simp only [T, mapEquiv_points, freudenthalSimplex_points, boxMap_apply, kuhnVertex_zero,
      kuhnVertex_last]
    rw [dist_eq_norm]
    simp only [add_zero, add_sub_add_left_eq_sub, ← smul_sub, norm_smul]
    rw [Real.norm_of_nonneg hh.le]
    simp

/-- In the level-`N` Freudenthal mesh of `∏ (bᵢ, bᵢ + s)` (with the sup norm), every simplex has
diameter `s / N`. -/
theorem diam_of_mem_freudenthalMesh [NeZero n] {b : Fin n → ℝ} {s : ℝ} {hs : 0 < s} {N : ℕ}
    [NeZero N] {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ (freudenthalMesh b s hs N).simplices) :
    diam T = s / N := by
  obtain ⟨m, σ, rfl⟩ := mem_freudenthalMesh_simplices.1 hT
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  exact diam_freudenthalMesh_simplex b (div_pos hs hN) _ σ

/-- The mesh size of the level-`N` Freudenthal mesh of `∏ (bᵢ, bᵢ + s)` is `h = s / N`. -/
theorem meshSize_freudenthalMesh [NeZero n] (b : Fin n → ℝ) (s : ℝ) (hs : 0 < s) (N : ℕ)
    [NeZero N] : (freudenthalMesh b s hs N).meshSize = s / N := by
  refine SimplicialMesh.meshSize_eq _ ?_ fun T hT => diam_of_mem_freudenthalMesh hT
  exact ⟨_, mem_freudenthalMesh_simplices.2 ⟨fun _ => 0, 1, rfl⟩⟩

/-! ### Volume -/

open Pointwise in
theorem freudenthalSet_eq_vadd (m : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    freudenthalSet m σ = latticePoint m +ᵥ kuhnSet σ := by
  ext x
  rw [Set.mem_vadd_set]
  constructor
  · intro hx; exact ⟨x - latticePoint m, hx, by simp [vadd_eq_add]⟩
  · rintro ⟨y, hy, rfl⟩; simpa [freudenthalSet, vadd_eq_add] using hy

open Pointwise MeasureTheory in
/-- The simplex `b + h (m + K_σ)` has volume `hⁿ / n!`. -/
theorem volume_freudenthalMesh_simplex (b : Fin n → ℝ) {h : ℝ} (hh : 0 < h) (m : Fin n → ℤ)
    (σ : Equiv.Perm (Fin n)) :
    volume (mapEquiv (boxMap b h hh.ne') (freudenthalSimplex m σ)).closedInterior =
      ENNReal.ofReal (h ^ n) / n.factorial := by
  rw [closedInterior_freudenthalMesh_simplex, freudenthalSet_eq_vadd]
  have e : (fun x => b + h • x) '' (latticePoint m +ᵥ kuhnSet σ) =
      b +ᵥ h • (latticePoint m +ᵥ kuhnSet σ) := by
    generalize latticePoint m +ᵥ kuhnSet σ = S
    rw [← Set.image_smul, ← Set.image_vadd, Set.image_image]; rfl
  rw [e, measure_vadd, Measure.addHaar_smul, measure_vadd, volume_kuhnSet, Module.finrank_fin_fun,
    abs_of_pos (pow_pos hh n), mul_one_div]

/-! ### Symmetries -/

/-- The central symmetry `x ↦ -x` maps `m + K_σ` onto `(-m - 1) + K_{σ ∘ rev}`. -/
theorem neg_mem_freudenthalSet_iff {m : Fin n → ℤ} {σ : Equiv.Perm (Fin n)} {x : Fin n → ℝ} :
    -x ∈ freudenthalSet (-m - 1) (σ * Fin.revPerm) ↔ x ∈ freudenthalSet m σ := by
  simp only [freudenthalSet, kuhnSet, Set.mem_ofPred_eq, Pi.sub_apply, Pi.neg_apply,
    latticePoint_apply, Pi.one_apply, Int.cast_sub, Int.cast_neg, Int.cast_one]
  constructor
  · rintro ⟨h01, ha⟩
    refine ⟨fun i => ⟨by linarith [(h01 i).2], by linarith [(h01 i).1]⟩, fun a b hab => ?_⟩
    have := ha (Fin.rev_le_rev.2 hab)
    simp only [Function.comp_apply, Equiv.Perm.coe_mul, Fin.revPerm_apply, Fin.rev_rev,
      Pi.sub_apply, Pi.neg_apply, latticePoint_apply, Int.cast_sub, Int.cast_neg,
      Int.cast_one, Pi.one_apply] at this ⊢
    linarith
  · rintro ⟨h01, ha⟩
    refine ⟨fun i => ⟨by linarith [(h01 i).2], by linarith [(h01 i).1]⟩, fun a b hab => ?_⟩
    have := ha (Fin.rev_le_rev.2 hab)
    simp only [Function.comp_apply, Equiv.Perm.coe_mul, Fin.revPerm_apply, Pi.sub_apply,
      Pi.neg_apply, latticePoint_apply, Int.cast_sub, Int.cast_neg, Int.cast_one,
      Pi.one_apply] at this ⊢
    linarith

/-- A permutation `π` of the coordinates maps `m + K_σ` onto `(m ∘ π) + K_{π⁻¹ σ}`. -/
theorem comp_mem_freudenthalSet_iff {m : Fin n → ℤ} {σ π : Equiv.Perm (Fin n)}
    {x : Fin n → ℝ} :
    x ∘ π ∈ freudenthalSet (m ∘ π) (π⁻¹ * σ) ↔ x ∈ freudenthalSet m σ := by
  simp only [freudenthalSet, kuhnSet, Set.mem_ofPred_eq, Pi.sub_apply, latticePoint_apply,
    Function.comp_apply]
  constructor
  · rintro ⟨h01, ha⟩
    refine ⟨fun i => by simpa using h01 (π.symm i), fun a b hab => ?_⟩
    have := ha hab
    simpa [Equiv.Perm.coe_mul, Equiv.Perm.inv_def] using this
  · rintro ⟨h01, ha⟩
    refine ⟨fun i => h01 (π i), fun a b hab => ?_⟩
    have := ha hab
    simpa [Equiv.Perm.coe_mul, Equiv.Perm.inv_def] using this

/-- The reflection `x₀ ↦ -x₀` of the plane. -/
def reflect₀ (x : Fin 2 → ℝ) : Fin 2 → ℝ := ![-x 0, x 1]

/-- **No reflection symmetry.** The reflection `x₀ ↦ -x₀` of the Kuhn simplex
`{1 ≥ x₀ ≥ x₁ ≥ 0}` is not a Freudenthal simplex: the Freudenthal triangulation is not invariant
under the coordinate reflections. -/
theorem reflect_kuhnSet_ne (m : Fin 2 → ℤ) (σ : Equiv.Perm (Fin 2)) :
    reflect₀ '' kuhnSet 1 ≠ freudenthalSet m σ := by
  intro h
  have hmem : ∀ p ∈ kuhnSet (1 : Equiv.Perm (Fin 2)), reflect₀ p ∈ freudenthalSet m σ :=
    fun p hp => h ▸ Set.mem_image_of_mem _ hp
  have hK : ∀ a b : ℝ, 0 ≤ b → b ≤ a → a ≤ 1 → ![a, b] ∈ kuhnSet (1 : Equiv.Perm (Fin 2)) := by
    intro a b hb hab ha
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · fin_cases i <;> simp <;> constructor <;> linarith
    · fin_cases i <;> fin_cases j <;> simp at hij ⊢
      exact hab
  have p1 := hmem _ (hK 0 0 le_rfl le_rfl zero_le_one)
  have p3 := hmem _ (hK 1 1 zero_le_one le_rfl le_rfl)
  simp only [reflect₀, freudenthalSet, kuhnSet, Set.mem_ofPred_eq] at p1 p3
  have a0 := (p1.1 0).1; have a1 := (p1.1 0).2; have b0 := (p1.1 1).1; have b1 := (p1.1 1).2
  have c0 := (p3.1 0).1; have c1 := (p3.1 0).2; have d0 := (p3.1 1).1; have d1 := (p3.1 1).2
  simp at a0 a1 b0 b1 c0 c1 d0 d1
  have hm0 : m 0 = -1 := by
    have : (m 0 : ℝ) = -1 := by linarith
    exact_mod_cast this
  have hm1 : m 1 = 0 := by omega
  have hσ : (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0) := by
    have hne : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
    revert hne
    generalize σ 0 = u
    generalize σ 1 = v
    fin_cases u <;> fin_cases v <;> simp
  have ha1 := p1.2 (show (0 : Fin 2) ≤ 1 by decide)
  have ha3 := p3.2 (show (0 : Fin 2) ≤ 1 by decide)
  rcases hσ with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
  · simp only [Function.comp_apply, h0, h1] at ha1 ha3
    revert ha1 ha3
    norm_num [latticePoint_apply, hm0, hm1]

end Feec.Mesh
