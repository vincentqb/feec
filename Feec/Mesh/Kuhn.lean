module

public import Feec.Mesh.Basic
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Kuhn simplices and the Freudenthal triangulation

For a permutation `σ` of `Fin n`, the Kuhn simplex `K_σ` has vertices
`v_j = ∑_{i<j} e_{σ i}` (`j = 0, …, n`) and is the order simplex
`K_σ = {x | 1 ≥ x_{σ 0} ≥ ⋯ ≥ x_{σ (n-1)} ≥ 0}`. The `n!` Kuhn simplices triangulate the unit
cube `[0,1]ⁿ` ([Freudenthal1942]; [Kuhn1960]). Their integer translates `m + K_σ`, `m ∈ ℤⁿ`, form
the Freudenthal triangulation of `ℝⁿ`; we prove the face-to-face property for all of them at
once: a point `x` of `m + K_σ` is a convex combination of the lattice points
`⌊x⌋ + 𝟙[t ≤ fract x]`, `t ∈ (0, 1]` (its *carrier*), which depend on `x` alone and are vertices
of every translate containing `x`.

## Main definitions

* `kuhnVertex σ j`, `kuhnSimplex σ`, `kuhnSet σ` (the order simplex).
* `kuhnMap σ` (`= B_σ`, `(B_σ x)_{σ i} = ∑_{j ≥ i} xⱼ`), with `kuhnSimplex σ = B_σ(T̂)`.
* `latticePoint m`, `freudenthalSimplex m σ = m + K_σ`, `freudenthalSet m σ`.
* `carrier x`: the lattice points `⌊x⌋ + 𝟙[t ≤ fract x]`, `0 < t ≤ 1`.

## Main results

* `kuhnMap_refPoints`: `B_σ` maps the vertices of `T̂` to the `v_j`; `kuhnSimplex` is affinely
  independent since `B_σ` is invertible (`kuhnMap_injective`).
* `closedInterior_kuhnSimplex`: `conv {v₀, …, vₙ} = {x | 1 ≥ x_{σ 0} ≥ ⋯ ≥ x_{σ(n-1)} ≥ 0}`
  (`kuhnSet` is stated with `Antitone (x ∘ σ)`).
* `iUnion_kuhnSet`: the Kuhn simplices cover `[0,1]ⁿ`;
  `eq_of_mem_kuhnSet_of_injective`: a point with distinct coordinates lies in only one.
* `inter_closedInterior_freudenthalSimplex`: **face-to-face property** of the Freudenthal
  triangulation: `(m + K_σ) ∩ (m' + K_σ') = conv (common vertices)`.
* `freudenthalSimplex_eq_of_closedInterior_eq`: distinct `(m, σ)` give distinct simplices.
* `volume_kuhnSet`, `volume_closedInterior_kuhnSimplex`: `vol K_σ = 1 / n!` (the `n!` simplices
  are permutations of each other and overlap only on the null hyperplanes `xᵢ = xⱼ`).

## References

* [H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*][Freudenthal1942]
* [H. W. Kuhn, *Some combinatorial lemmas in topology*][Kuhn1960]
* [J. Bey, *Simplicial grid refinement: on Freudenthal's algorithm and the optimal number of congruence classes*][Bey2000]
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (simplicial meshes)

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace Feec.Mesh

variable {n : ℕ}

/-! ### Tail sums -/

/-- `tailSum x t = ∑_{i ≥ t} xᵢ`. -/
def tailSum (x : Fin n → ℝ) (t : ℕ) : ℝ := ∑ i : Fin n, if t ≤ (i : ℕ) then x i else 0

theorem tailSum_zero (x : Fin n → ℝ) : tailSum x 0 = ∑ i, x i := by simp [tailSum]

theorem tailSum_of_le (x : Fin n → ℝ) {t : ℕ} (ht : n ≤ t) : tailSum x t = 0 :=
  Finset.sum_eq_zero fun i _ => ite_eq_right (by omega)

theorem tailSum_sub_succ (x : Fin n → ℝ) (i : Fin n) :
    tailSum x i - tailSum x (i + 1) = x i := by
  rw [tailSum, tailSum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    have : (k : ℕ) ≠ i := fun h => hk (Fin.ext h)
    split_ifs <;> first | omega | simp
  · simp

theorem tailSum_antitone {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) : Antitone (tailSum x) := by
  intro s t hst
  refine Finset.sum_le_sum fun i _ => ?_
  split_ifs with h1 h2 <;> first | exact le_rfl | exact hx i | omega

theorem tailSum_nonneg {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) (t : ℕ) : 0 ≤ tailSum x t :=
  Finset.sum_nonneg fun i _ => by split_ifs; exacts [hx i, le_rfl]

/-! ### The linear map `B_σ` and the Kuhn vertices -/

/-- The matrix of `B_σ`: entry `(k, i)` is `1` iff `σ⁻¹ k ≤ i`. -/
def kuhnMatrix (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun k i => if (σ.symm k : ℕ) ≤ i then 1 else 0

/-- `B_σ`, with `(B_σ x)_{σ i} = ∑_{j ≥ i} xⱼ`; it maps `eᵢ` to `v_{i+1}`. -/
def kuhnMap (σ : Equiv.Perm (Fin n)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  Matrix.toLin' (kuhnMatrix σ)

theorem kuhnMap_apply (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (k : Fin n) :
    kuhnMap σ x k = tailSum x (σ.symm k) := by
  simp [kuhnMap, kuhnMatrix, Matrix.mulVec, dotProduct, tailSum, ite_mul]

theorem kuhnMap_apply_self (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (i : Fin n) :
    kuhnMap σ x (σ i) = tailSum x i := by
  rw [kuhnMap_apply, Equiv.symm_apply_apply]

/-- `tailSum x t` in terms of `y = B_σ x`. -/
theorem tailSum_eq_of_kuhnMap (σ : Equiv.Perm (Fin n)) {x y : Fin n → ℝ} (hy : kuhnMap σ x = y)
    (t : ℕ) : tailSum x t = if h : t < n then y (σ ⟨t, h⟩) else 0 := by
  split_ifs with h
  · rw [← hy, kuhnMap_apply_self]
  · exact tailSum_of_le x (not_lt.1 h)

theorem kuhnMap_injective (σ : Equiv.Perm (Fin n)) : Function.Injective (kuhnMap σ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  funext i
  have h := tailSum_eq_of_kuhnMap σ hx
  rw [← tailSum_sub_succ x i, h, h]
  simp

/-- `B_σ` as a linear equivalence. -/
def kuhnEquiv (σ : Equiv.Perm (Fin n)) : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
  LinearEquiv.ofInjectiveEndo (kuhnMap σ) (kuhnMap_injective σ)

@[simp] theorem kuhnEquiv_apply (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    kuhnEquiv σ x = kuhnMap σ x := rfl

/-- The Kuhn vertex `v_j`: coordinate `k` is `1` iff `σ⁻¹ k < j`. -/
def kuhnVertex (σ : Equiv.Perm (Fin n)) (j : Fin (n + 1)) : Fin n → ℝ :=
  fun k => if (σ.symm k : ℕ) < j then 1 else 0

@[simp] theorem kuhnVertex_zero (σ : Equiv.Perm (Fin n)) : kuhnVertex σ 0 = 0 := by
  funext k; simp [kuhnVertex]

theorem kuhnVertex_last (σ : Equiv.Perm (Fin n)) : kuhnVertex σ (Fin.last n) = 1 := by
  funext k; simp [kuhnVertex]

theorem kuhnMap_refPoints (σ : Equiv.Perm (Fin n)) (j : Fin (n + 1)) :
    kuhnMap σ (refPoints n j) = kuhnVertex σ j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp
  · funext k
    rw [refPoints_succ, kuhnMap_apply, tailSum, Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same, kuhnVertex, Fin.val_succ]
      split_ifs <;> first | rfl | omega
    · intro b _ hb; simp [hb]
    · simp

/-- The Kuhn simplex `K_σ = B_σ(T̂)`, with vertices `kuhnVertex σ`. -/
def kuhnSimplex (σ : Equiv.Perm (Fin n)) : Affine.Simplex ℝ (Fin n → ℝ) n :=
  mapEquiv (kuhnEquiv σ).toAffineEquiv (refSimplex n)

@[simp] theorem kuhnSimplex_points (σ : Equiv.Perm (Fin n)) :
    (kuhnSimplex σ).points = kuhnVertex σ := by
  funext j; simp [kuhnSimplex, kuhnMap_refPoints]

theorem closedInterior_kuhnSimplex_eq_image (σ : Equiv.Perm (Fin n)) :
    (kuhnSimplex σ).closedInterior = kuhnMap σ '' (refSimplex n).closedInterior := by
  rw [kuhnSimplex, closedInterior_mapEquiv, LinearEquiv.coe_toAffineEquiv]; rfl

/-- The order simplex `{x | 1 ≥ x_{σ 0} ≥ ⋯ ≥ x_{σ (n-1)} ≥ 0}`. -/
def kuhnSet (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ Antitone (x ∘ σ)}

/-- **The Kuhn simplex is the order simplex**: `conv {v₀, …, vₙ} = K_σ`. -/
theorem closedInterior_kuhnSimplex (σ : Equiv.Perm (Fin n)) :
    (kuhnSimplex σ).closedInterior = kuhnSet σ := by
  rw [closedInterior_kuhnSimplex_eq_image]
  ext y
  simp only [Set.mem_image, mem_closedInterior_refSimplex]
  constructor
  · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
    have ht := tailSum_antitone hx0
    refine ⟨fun k => ⟨?_, ?_⟩, fun a b hab => ?_⟩
    · rw [kuhnMap_apply]; exact tailSum_nonneg hx0 _
    · rw [kuhnMap_apply]
      exact (ht (Nat.zero_le _)).trans (by rw [tailSum_zero]; exact hx1)
    · simp only [Function.comp_apply, kuhnMap_apply_self]
      exact ht (Fin.le_def.1 hab)
  · rintro ⟨h01, hanti⟩
    set x := (kuhnEquiv σ).symm y
    have hT := tailSum_eq_of_kuhnMap σ ((kuhnEquiv σ).apply_symm_apply y)
    refine ⟨x, ⟨fun i => ?_, ?_⟩, (kuhnEquiv σ).apply_symm_apply y⟩
    · rw [← tailSum_sub_succ x i, hT, hT, dite_eq_left i.2]
      split_ifs with h
      · have := hanti (show i ≤ ⟨i + 1, h⟩ from Fin.le_def.2 (by simp))
        simp only [Function.comp_apply] at this
        simp only [Fin.eta]; linarith
      · simp only [Fin.eta, sub_zero]; exact (h01 _).1
    · rw [← tailSum_zero, hT]
      split_ifs with h
      · exact (h01 _).2
      · exact zero_le_one

theorem isClosed_kuhnSet (σ : Equiv.Perm (Fin n)) : IsClosed (kuhnSet σ) :=
  closedInterior_kuhnSimplex σ ▸ (kuhnSimplex σ).isClosed_closedInterior

theorem kuhnSet_subset_Icc (σ : Equiv.Perm (Fin n)) : kuhnSet σ ⊆ Set.Icc 0 1 :=
  fun _ hx => ⟨fun i => (hx.1 i).1, fun i => (hx.1 i).2⟩

/-- The Kuhn simplices cover the unit cube. -/
theorem iUnion_kuhnSet : ⋃ σ : Equiv.Perm (Fin n), kuhnSet σ = Set.Icc 0 1 := by
  refine subset_antisymm (Set.iUnion_subset kuhnSet_subset_Icc) fun x hx => ?_
  refine Set.mem_iUnion.2 ⟨Tuple.sort fun i => -x i, fun i => ⟨hx.1 i, hx.2 i⟩, ?_⟩
  intro a b hab
  have := Tuple.monotone_sort (fun i => -x i) hab
  simp only [Function.comp_apply, neg_le_neg_iff] at this ⊢
  exact this

/-- A point with pairwise distinct coordinates lies in only one Kuhn simplex. -/
theorem eq_of_mem_kuhnSet_of_injective {σ τ : Equiv.Perm (Fin n)} {x : Fin n → ℝ}
    (hx : Function.Injective x) (hσ : x ∈ kuhnSet σ) (hτ : x ∈ kuhnSet τ) : σ = τ := by
  have h := Tuple.unique_monotone (f := fun i => -x i) (σ := σ) (τ := τ)
    (fun a b hab => by simpa using hσ.2 hab) (fun a b hab => by simpa using hτ.2 hab)
  ext i
  have := congrFun h i
  simp only [Function.comp_apply, neg_inj] at this
  exact congrArg Fin.val (hx this)

/-! ### A generic interior point -/

/-- The point `g` of `K_σ` with `g_{σ i} = (n - i) / (n + 1)`; its coordinates are distinct and in
`(0, 1)`. -/
def kuhnCenter (σ : Equiv.Perm (Fin n)) : Fin n → ℝ :=
  fun k => ((n : ℝ) - (σ.symm k : ℕ)) / (n + 1)

theorem kuhnCenter_pos (σ : Equiv.Perm (Fin n)) (k : Fin n) : 0 < kuhnCenter σ k := by
  have : ((σ.symm k : ℕ) : ℝ) < n := by exact_mod_cast (σ.symm k).2
  unfold kuhnCenter; apply div_pos <;> linarith

theorem kuhnCenter_lt_one (σ : Equiv.Perm (Fin n)) (k : Fin n) : kuhnCenter σ k < 1 := by
  have : (0 : ℝ) ≤ ((σ.symm k : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold kuhnCenter; rw [div_lt_one (by positivity)]; linarith

theorem kuhnCenter_sub (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    kuhnCenter σ i - kuhnCenter σ j = (((σ.symm j : ℕ) : ℝ) - (σ.symm i : ℕ)) / (n + 1) := by
  unfold kuhnCenter; field_simp; ring

theorem kuhnCenter_injective (σ : Equiv.Perm (Fin n)) : Function.Injective (kuhnCenter σ) := by
  intro i j h
  have h' := kuhnCenter_sub σ i j
  rw [h, sub_self, eq_comm, div_eq_zero_iff, sub_eq_zero] at h'
  rcases h' with h' | h'
  · exact σ.symm.injective (Fin.ext (by exact_mod_cast h'.symm))
  · exact absurd h' (by positivity)

theorem kuhnCenter_mem (σ : Equiv.Perm (Fin n)) : kuhnCenter σ ∈ kuhnSet σ := by
  refine ⟨fun k => ⟨(kuhnCenter_pos σ k).le, (kuhnCenter_lt_one σ k).le⟩, fun a b hab => ?_⟩
  simp only [Function.comp_apply, kuhnCenter, Equiv.symm_apply_apply]
  have : ((a : ℕ) : ℝ) ≤ (b : ℕ) := by exact_mod_cast Fin.le_def.1 hab
  apply div_le_div_of_nonneg_right _ (by positivity); linarith

/-! ### Integer translates: the Freudenthal triangulation of `ℝⁿ` -/

/-- The lattice point `m ∈ ℤⁿ` as a point of `ℝⁿ`. -/
def latticePoint (m : Fin n → ℤ) : Fin n → ℝ := fun i => (m i : ℝ)

@[simp] theorem latticePoint_apply (m : Fin n → ℤ) (i : Fin n) : latticePoint m i = m i := rfl

@[simp] theorem latticePoint_zero : latticePoint (0 : Fin n → ℤ) = 0 := by
  funext i; simp

/-- The translate `m + K_σ`. -/
def freudenthalSimplex (m : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    Affine.Simplex ℝ (Fin n → ℝ) n :=
  mapEquiv (AffineEquiv.constVAdd ℝ (Fin n → ℝ) (latticePoint m)) (kuhnSimplex σ)

@[simp] theorem freudenthalSimplex_points (m : Fin n → ℤ) (σ : Equiv.Perm (Fin n))
    (j : Fin (n + 1)) :
    (freudenthalSimplex m σ).points j = latticePoint m + kuhnVertex σ j := by
  simp [freudenthalSimplex]

/-- The set `m + K_σ = {x | x - m ∈ K_σ}`. -/
def freudenthalSet (m : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  {x | x - latticePoint m ∈ kuhnSet σ}

theorem closedInterior_freudenthalSimplex (m : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    (freudenthalSimplex m σ).closedInterior = freudenthalSet m σ := by
  rw [freudenthalSimplex, closedInterior_mapEquiv, closedInterior_kuhnSimplex]
  ext x
  simp only [Set.mem_image, AffineEquiv.constVAdd_apply, vadd_eq_add, freudenthalSet,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · intro hx; exact ⟨x - latticePoint m, hx, by abel⟩

/-! ### The carrier of a point and the face-to-face property -/

/-- The lattice point `⌊x⌋ + 𝟙[t ≤ fract x]`. -/
def carrierPoint (x : Fin n → ℝ) (t : ℝ) : Fin n → ℝ :=
  fun i => (⌊x i⌋ : ℝ) + if t ≤ Int.fract (x i) then 1 else 0

/-- The carrier of `x`: the lattice points `⌊x⌋ + 𝟙[t ≤ fract x]`, `0 < t ≤ 1`. -/
def carrier (x : Fin n → ℝ) : Set (Fin n → ℝ) := carrierPoint x '' Set.Ioc 0 1

/-- On `m + K_σ`, `⌊x⌋ + 𝟙[t ≤ fract x] = m + 𝟙[t ≤ x - m]` for `0 < t ≤ 1`. -/
theorem carrierPoint_eq {m : Fin n → ℤ} {σ : Equiv.Perm (Fin n)} {x : Fin n → ℝ}
    (hx : x ∈ freudenthalSet m σ) {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    carrierPoint x t = latticePoint m + fun i => if t ≤ x i - m i then 1 else 0 := by
  funext i
  have h0 := (hx.1 i).1
  have h1 := (hx.1 i).2
  simp only [Pi.sub_apply, latticePoint_apply] at h0 h1
  simp only [carrierPoint, Pi.add_apply, latticePoint_apply]
  rcases h1.lt_or_eq with h1 | h1
  · have hfl : ⌊x i⌋ = m i := Int.floor_eq_iff.2 ⟨by linarith, by linarith⟩
    rw [Int.fract, hfl]
  · have hfl : ⌊x i⌋ = m i + 1 := Int.floor_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
    rw [Int.fract, hfl, h1]
    have : ¬ t ≤ x i - ((m i + 1 : ℤ) : ℝ) := by push_cast; linarith [ht.1]
    rw [ite_eq_right this, ite_eq_left ht.2]
    push_cast; ring

/-- A downward closed set of `Fin n` is an initial segment. -/
theorem mem_iff_lt_card_of_lowerSet {L : Finset (Fin n)} (hL : ∀ a b, a ≤ b → b ∈ L → a ∈ L)
    (a : Fin n) : a ∈ L ↔ (a : ℕ) < L.card := by
  constructor
  · intro ha
    have : Finset.Iic a ⊆ L := fun b hb => hL b a (Finset.mem_Iic.1 hb) ha
    have := Finset.card_le_card this
    rw [Fin.card_Iic] at this; omega
  · intro hlt
    by_contra ha
    have : L ⊆ Finset.Iio a := fun b hb => Finset.mem_Iio.2 (lt_of_not_ge fun hab =>
      ha (hL a b hab hb))
    have := Finset.card_le_card this
    rw [Fin.card_Iio] at this; omega

/-- On `m + K_σ`, the carrier of `x` consists of vertices of `m + K_σ`. -/
theorem carrier_subset_range {m : Fin n → ℤ} {σ : Equiv.Perm (Fin n)} {x : Fin n → ℝ}
    (hx : x ∈ freudenthalSet m σ) :
    carrier x ⊆ Set.range (freudenthalSimplex m σ).points := by
  classical
  rintro _ ⟨t, ht, rfl⟩
  rw [carrierPoint_eq hx ht]
  set y := x - latticePoint m
  have hy : ∀ i, x i - m i = y (σ (σ.symm i)) := fun i => by simp [y]
  set L : Finset (Fin n) := Finset.univ.filter fun a => t ≤ y (σ a)
  have hL : ∀ a b, a ≤ b → b ∈ L → a ∈ L := by
    intro a b hab hb
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact hb.trans (hx.2 hab)
  refine ⟨⟨L.card, Nat.lt_succ_of_le ((Finset.card_le_univ L).trans (by simp))⟩, ?_⟩
  rw [freudenthalSimplex_points]
  congr 1
  funext i
  simp only [kuhnVertex]
  have := mem_iff_lt_card_of_lowerSet hL (σ.symm i)
  simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at this
  rw [hy i]
  by_cases h : t ≤ y (σ (σ.symm i))
  · rw [ite_eq_left h, ite_eq_left (this.1 h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (this.2 h'))]

/-- Every point of `m + K_σ` is a convex combination of its carrier. -/
theorem mem_convexHull_carrier {m : Fin n → ℤ} {σ : Equiv.Perm (Fin n)} {x : Fin n → ℝ}
    (hx : x ∈ freudenthalSet m σ) : x ∈ convexHull ℝ (carrier x) := by
  classical
  set y := x - latticePoint m with hydef
  set z := (kuhnEquiv σ).symm y
  have hBz : kuhnMap σ z = y := (kuhnEquiv σ).apply_symm_apply y
  have hT := tailSum_eq_of_kuhnMap σ hBz
  -- `z ∈ T̂`
  have hz : z ∈ (refSimplex n).closedInterior := by
    have : y ∈ (kuhnSimplex σ).closedInterior := (closedInterior_kuhnSimplex σ).symm ▸ hx
    rw [closedInterior_kuhnSimplex_eq_image] at this
    obtain ⟨z', hz', hz'y⟩ := this
    have : z' = z := (kuhnMap_injective σ) (hz'y.trans hBz.symm)
    exact this ▸ hz'
  rw [mem_closedInterior_refSimplex] at hz
  have hTa := tailSum_antitone hz.1
  -- barycentric weights
  set w : Fin (n + 1) → ℝ := Fin.cons (1 - ∑ i, z i) z with hw
  have hw0 : ∀ j, 0 ≤ w j := Fin.cases (by simp [hw]; exact hz.2) fun i => by simp [hw, hz.1 i]
  have hw1 : ∑ j, w j = 1 := by simp [hw, Fin.sum_univ_succ]
  have hyk : ∀ k, y k = tailSum z (σ.symm k) := fun k => by
    rw [← hBz, kuhnMap_apply]
  -- the vertices with positive weight are in the carrier
  have hpos : ∀ j, 0 < w j → latticePoint m + kuhnVertex σ j ∈ carrier x := by
    intro j hj
    obtain ⟨t, ht, hiff⟩ : ∃ t ∈ Set.Ioc (0 : ℝ) 1,
        ∀ k, t ≤ y k ↔ (σ.symm k : ℕ) < j := by
      refine Fin.cases (fun hj => ?_) (fun i hj => ?_) j hj
      · refine ⟨1, ⟨one_pos, le_rfl⟩, fun k => ?_⟩
        simp only [hw, Fin.cons_zero, sub_pos] at hj
        simp only [Fin.val_zero, Nat.not_lt_zero, iff_false, not_le, hyk]
        rw [← tailSum_zero] at hj
        exact (hTa (Nat.zero_le _)).trans_lt hj
      · simp only [hw, Fin.cons_succ] at hj
        rw [← tailSum_sub_succ z i, sub_pos] at hj
        refine ⟨tailSum z i, ⟨(tailSum_nonneg hz.1 _).trans_lt hj, ?_⟩, fun k => ?_⟩
        · exact (hTa (Nat.zero_le _)).trans (by rw [tailSum_zero]; exact hz.2)
        · rw [hyk, Fin.val_succ]
          constructor
          · intro h
            by_contra hk
            exact absurd ((hTa (by omega : (i : ℕ) + 1 ≤ σ.symm k)).trans_lt hj) (not_lt.2 h)
          · intro hk; exact hTa (by omega)
    refine ⟨t, ht, ?_⟩
    rw [carrierPoint_eq hx ht]
    congr 1
    funext k
    simp only [kuhnVertex]
    have : x k - m k = y k := by simp [y]
    rw [this]
    by_cases h : t ≤ y k
    · rw [ite_eq_left h, ite_eq_left ((hiff k).1 h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ((hiff k).2 h'))]
  -- the convex combination
  have hsum : ∑ j, w j • (latticePoint m + kuhnVertex σ j) = x := by
    simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hw1, one_smul]
    have : ∑ j, w j • kuhnVertex σ j = y := by
      rw [← hBz]
      simp only [← kuhnMap_refPoints, ← map_smul, ← map_sum]
      congr 1
      rw [sum_smul_refPoints]
      funext k; simp [hw, z]
    rw [this, hydef]; abel
  have := (convex_convexHull ℝ (carrier x)).finsum_mem hw0 (by rwa [finsum_eq_sum_of_fintype])
    fun j hj => subset_convexHull ℝ _ (hpos j ((hw0 j).lt_of_ne' hj))
  rwa [finsum_eq_sum_of_fintype, hsum] at this

/-- **Face-to-face property of the Freudenthal triangulation**: two integer translates of Kuhn
simplices meet in the convex hull of their common vertices. -/
theorem inter_closedInterior_freudenthalSimplex (m m' : Fin n → ℤ) (σ σ' : Equiv.Perm (Fin n)) :
    (freudenthalSimplex m σ).closedInterior ∩ (freudenthalSimplex m' σ').closedInterior =
      convexHull ℝ ((vertexSet (freudenthalSimplex m σ) : Set (Fin n → ℝ)) ∩
        vertexSet (freudenthalSimplex m' σ')) := by
  apply subset_antisymm
  · rintro x ⟨hx, hx'⟩
    rw [closedInterior_freudenthalSimplex] at hx hx'
    refine convexHull_mono ?_ (mem_convexHull_carrier hx)
    rw [coe_vertexSet, coe_vertexSet]
    exact Set.subset_inter (carrier_subset_range hx) (carrier_subset_range hx')
  · refine Set.subset_inter ?_ ?_
    · rw [← convexHull_vertexSet]; exact convexHull_mono Set.inter_subset_left
    · rw [← convexHull_vertexSet (freudenthalSimplex m' σ')]
      exact convexHull_mono Set.inter_subset_right

theorem center_mem_freudenthalSet (m : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    latticePoint m + kuhnCenter σ ∈ freudenthalSet m σ := by
  simpa [freudenthalSet] using kuhnCenter_mem σ

/-- The generic point `m + g_σ` lies in `m' + K_σ'` only if `(m', σ') = (m, σ)`. -/
theorem eq_of_center_mem {m m' : Fin n → ℤ} {σ σ' : Equiv.Perm (Fin n)}
    (h : latticePoint m + kuhnCenter σ ∈ freudenthalSet m' σ') : m = m' ∧ σ = σ' := by
  have hm : m = m' := by
    funext i
    have h0 := (h.1 i).1
    have h1 := (h.1 i).2
    simp only [Pi.sub_apply, Pi.add_apply, latticePoint_apply] at h0 h1
    have g0 := kuhnCenter_pos σ i
    have g1 := kuhnCenter_lt_one σ i
    have a : ((m' i : ℤ) : ℝ) < ((m i + 1 : ℤ) : ℝ) := by push_cast; linarith
    have b : ((m i : ℤ) : ℝ) < ((m' i + 1 : ℤ) : ℝ) := by push_cast; linarith
    have a' := Int.cast_lt.1 a
    have b' := Int.cast_lt.1 b
    omega
  subst hm
  refine ⟨rfl, eq_of_mem_kuhnSet_of_injective (kuhnCenter_injective σ) (kuhnCenter_mem σ) ?_⟩
  simpa [freudenthalSet] using h

/-- Distinct `(m, σ)` give distinct closed simplices `m + K_σ`. -/
theorem freudenthalSimplex_eq_of_closedInterior_eq {m m' : Fin n → ℤ}
    {σ σ' : Equiv.Perm (Fin n)}
    (h : (freudenthalSimplex m σ).closedInterior = (freudenthalSimplex m' σ').closedInterior) :
    m = m' ∧ σ = σ' := by
  apply eq_of_center_mem
  rw [← closedInterior_freudenthalSimplex, ← h, closedInterior_freudenthalSimplex]
  exact center_mem_freudenthalSet m σ

/-! ### Volume -/

theorem kuhnSet_eq_preimage (σ : Equiv.Perm (Fin n)) :
    kuhnSet σ = (fun x : Fin n → ℝ => x ∘ σ) ⁻¹' kuhnSet (1 : Equiv.Perm (Fin n)) := by
  ext x
  simp only [kuhnSet, Set.mem_preimage, Set.mem_ofPred_eq, Function.comp_apply,
    Equiv.Perm.coe_one, Function.comp_id]
  exact ⟨fun ⟨h, ha⟩ => ⟨fun i => h (σ i), ha⟩,
    fun ⟨h, ha⟩ => ⟨fun i => by simpa using h (σ.symm i), ha⟩⟩

theorem volume_kuhnSet_eq (σ : Equiv.Perm (Fin n)) :
    volume (kuhnSet σ) = volume (kuhnSet (1 : Equiv.Perm (Fin n))) := by
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) σ.symm
  have hf : ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm) =
      fun x : Fin n → ℝ => x ∘ σ := by
    funext x i; simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
  rw [kuhnSet_eq_preimage σ, ← hf]
  exact hmp.measure_preimage (isClosed_kuhnSet 1).measurableSet.nullMeasurableSet

theorem volume_diagonal {i j : Fin n} (hij : i ≠ j) :
    volume {x : Fin n → ℝ | x i = x j} = 0 := by
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) - (LinearMap.proj j : (Fin n → ℝ) →ₗ[ℝ] ℝ)
  have hs : ((LinearMap.ker L : Submodule ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)) =
      {x | x i = x j} := by
    ext x; simp [L, sub_eq_zero]
  rw [← hs]
  refine Measure.addHaar_submodule _ _ fun htop => ?_
  have : (Pi.single i (1 : ℝ) : Fin n → ℝ) ∈ LinearMap.ker L := htop ▸ Submodule.mem_top
  simp [L, hij.symm] at this

theorem volume_inter_kuhnSet {σ τ : Equiv.Perm (Fin n)} (h : σ ≠ τ) :
    volume (kuhnSet σ ∩ kuhnSet τ) = 0 := by
  refine measure_mono_null (t := ⋃ i, ⋃ j, ⋃ (_ : i ≠ j), {x : Fin n → ℝ | x i = x j}) ?_
    (measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun hij =>
      volume_diagonal hij)
  rintro x ⟨hσ, hτ⟩
  by_contra hx
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists] at hx
  exact h (eq_of_mem_kuhnSet_of_injective (fun a b hab => by_contra fun hne => hx a b hne hab)
    hσ hτ)

/-- **Volume of a Kuhn simplex**: `vol K_σ = 1 / n!`. -/
theorem volume_kuhnSet (σ : Equiv.Perm (Fin n)) :
    volume (kuhnSet σ) = 1 / (n.factorial : ENNReal) := by
  have hU : volume (⋃ σ : Equiv.Perm (Fin n), kuhnSet σ) =
      ∑' σ : Equiv.Perm (Fin n), volume (kuhnSet σ) :=
    measure_iUnion₀ (fun σ τ h => volume_inter_kuhnSet h)
      fun σ => (isClosed_kuhnSet σ).measurableSet.nullMeasurableSet
  rw [iUnion_kuhnSet, Real.volume_Icc_pi, tsum_fintype] at hU
  simp only [Pi.one_apply, Pi.zero_apply, sub_zero, ENNReal.ofReal_one, Finset.prod_const_one,
    volume_kuhnSet_eq, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul] at hU
  rw [volume_kuhnSet_eq, ENNReal.eq_div_iff (by exact_mod_cast n.factorial_ne_zero)
    (ENNReal.natCast_ne_top _)]
  exact hU.symm

theorem volume_closedInterior_kuhnSimplex (σ : Equiv.Perm (Fin n)) :
    volume (kuhnSimplex σ).closedInterior = 1 / (n.factorial : ENNReal) := by
  rw [closedInterior_kuhnSimplex, volume_kuhnSet]

end Feec.Mesh
