module

public import Feec.Semigroup.LumerPhillips
public import Feec.HilbertComplex.HodgeLaplacian
public import Feec.Evolution.WellPosed
public import Feec.Evolution.Energy

/-!
# The Hodge heat equation

TODO
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap Feec.Operator

@[expose] public noncomputable section

/-! ### Classical solutions for an m-dissipative generator -/

namespace LinearPMap.IsMDissipative

open Feec

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] {A : E →ₗ.[𝕜] E}

/-- **Well-posedness for an m-dissipative generator**: for `U₀ ∈ D(A)` and admissible forcing
`F ∈ C([a,b]; E) ∩ (W^{1,1}(a,b; E) ∪ L¹(a,b; D(A)))`, `U' = A U + F`, `U a = U₀` has a classical
solution on `[a, b]` (Duhamel's formula for the Lumer–Phillips semigroup), unique among strong
solutions. Cf. [Pazy1983], §4.1–4.2. -/
theorem existsUnique_classicalSolution (hA : A.IsMDissipative) {U₀ : E} (hU₀ : U₀ ∈ A.domain)
    {F : ℝ → E} {a b : ℝ} (hF : Evolution.ForcingClass.admissible A a b F) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution A (Icc a b) F U ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution A (Icc a b) F V → EqOn V U (Icc a b) := by
  have h := hA.semigroup.existsUnique_classicalSolution (U₀ := U₀) (F := F) (a := a) (b := b)
  rw [hA.generator_semigroup] at h
  exact h hU₀ hF

end LinearPMap.IsMDissipative

/-! ### Graphs of differences and squares -/

namespace LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem mem_graph_sub_iff {P Q : E →ₗ.[𝕜] E} {x y : E} :
    (x, y) ∈ (P - Q).graph ↔ ∃ a b, (x, a) ∈ P.graph ∧ (x, b) ∈ Q.graph ∧ y = a - b := by
  rw [mem_graph_iff_exists]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨_, _, P.mem_graph ⟨x, h.1⟩, Q.mem_graph ⟨x, h.2⟩, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    obtain ⟨ha', rfl⟩ := mem_graph_iff_exists.1 ha
    obtain ⟨hb', rfl⟩ := mem_graph_iff_exists.1 hb
    exact ⟨⟨ha', hb'⟩, rfl⟩

theorem mem_graph_sq_iff {A : E →ₗ.[𝕜] E} {x z : E} :
    (x, z) ∈ A.sq.graph ↔ ∃ y, (x, y) ∈ A.graph ∧ (y, z) ∈ A.graph := by
  rw [mem_graph_iff_exists]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨_, A.mem_graph (sqFst ⟨x, h⟩), A.mem_graph (sqSnd ⟨x, h⟩)⟩
  · rintro ⟨y, hy, hz⟩
    obtain ⟨hx, rfl⟩ := mem_graph_iff_exists.1 hy
    obtain ⟨hy', rfl⟩ := mem_graph_iff_exists.1 hz
    exact ⟨⟨hx, hy'⟩, rfl⟩

theorem mem_graph_sq_neg_iff {A : E →ₗ.[𝕜] E} {x z : E} :
    (x, z) ∈ (-A).sq.graph ↔ (x, z) ∈ A.sq.graph := by
  rw [mem_graph_sq_iff, mem_graph_sq_iff]
  constructor
  · rintro ⟨y, h1, h2⟩
    exact ⟨-y, mem_graph_neg_iff.1 h1, by simpa using A.graph.neg_mem (mem_graph_neg_iff.1 h2)⟩
  · rintro ⟨y, h1, h2⟩
    exact ⟨-y, mem_graph_neg_iff.2 (by simpa using h1),
      mem_graph_neg_iff.2 (by simpa using A.graph.neg_mem h2)⟩

/-- `(-A)² = A²`. -/
theorem sq_neg (A : E →ₗ.[𝕜] E) : (-A).sq = A.sq :=
  eq_of_eq_graph (Submodule.ext fun _ => mem_graph_sq_neg_iff)

theorem mem_graph_sq_sub_comm {P Q : E →ₗ.[𝕜] E} {x z : E} :
    (x, z) ∈ (Q - P).sq.graph ↔ (x, z) ∈ (P - Q).sq.graph := by
  have h : ∀ {x y : E}, (x, y) ∈ (Q - P).graph ↔ (x, -y) ∈ (P - Q).graph := by
    intro x y
    rw [mem_graph_sub_iff, mem_graph_sub_iff]
    constructor
    · rintro ⟨a, b, ha, hb, rfl⟩; exact ⟨b, a, hb, ha, by abel⟩
    · rintro ⟨a, b, ha, hb, e⟩; exact ⟨b, a, hb, ha, by rw [← neg_neg y, e]; abel⟩
  rw [mem_graph_sq_iff, mem_graph_sq_iff]
  constructor
  · rintro ⟨y, h1, h2⟩
    refine ⟨-y, h.1 h1, ?_⟩
    have := (P - Q).graph.neg_mem (h.1 h2)
    simpa using this
  · rintro ⟨y, h1, h2⟩
    refine ⟨-y, h.2 (by simpa using h1), h.2 ?_⟩
    have := (P - Q).graph.neg_mem h2
    simpa using this

/-- **`P` commutes with `(P - Q)²`** when `P P = 0` and `Q Q = 0` (graph form): if
`(u, z) ∈ graph (P - Q)²`, `(u, a) ∈ graph P` and `(z, b) ∈ graph P`, then
`(a, b) ∈ graph (P - Q)²`. With `L = P - Q`, `L² = -(P Q + Q P)` and `L² P = -P Q P = P L²`. -/
theorem mem_graph_sq_sub_of_comp_eq_zero {P Q : E →ₗ.[𝕜] E}
    (hP : ∀ {x a}, (x, a) ∈ P.graph → (a, 0) ∈ P.graph)
    (hQ : ∀ {x a}, (x, a) ∈ Q.graph → (a, 0) ∈ Q.graph) {u z a b : E}
    (huz : (u, z) ∈ (P - Q).sq.graph) (hua : (u, a) ∈ P.graph) (hzb : (z, b) ∈ P.graph) :
    (a, b) ∈ (P - Q).sq.graph := by
  obtain ⟨y, huy, hyz⟩ := mem_graph_sq_iff.1 huz
  obtain ⟨a', b', ha', hb', rfl⟩ := mem_graph_sub_iff.1 huy
  obtain rfl := P.mem_graph_snd_inj hua ha' rfl
  obtain ⟨c, d, hc, hd, rfl⟩ := mem_graph_sub_iff.1 hyz
  -- `(b', -c) ∈ graph P` since `b' = a - y`
  have hb'P : (b', -c) ∈ P.graph := by
    have := P.graph.sub_mem (hP hua) hc
    simpa using this
  -- `(a, d) ∈ graph Q` since `a = y + b'`
  have haQ : (a, d) ∈ Q.graph := by
    have := Q.graph.add_mem hd (hQ hb')
    simpa using this
  -- `(d, -b) ∈ graph P` since `d = c - z`
  have hdP : (d, -b) ∈ P.graph := by
    have := P.graph.sub_mem (hP hc) hzb
    simpa using this
  refine mem_graph_sq_iff.2 ⟨-d, mem_graph_sub_iff.2 ⟨0, d, hP hua, haQ, by simp⟩,
    mem_graph_sub_iff.2 ⟨b, 0, ?_, ?_, by simp⟩⟩
  · simpa using P.graph.neg_mem hdP
  · simpa using Q.graph.neg_mem (hQ haQ)

end LinearPMap

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 c W) [Fintype ι]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### `-Δ` is m-dissipative -/

/-- `-Δ = L²` for the wave operator `L = 𝐝 − 𝐝*`. -/
theorem neg_hodgeLaplacian : -H.hodgeLaplacian = H.wave.sq := neg_neg _

/-- **`-Δ` is m-dissipative**: self-adjoint and nonpositive. -/
theorem isMDissipative_neg_hodgeLaplacian : (-H.hodgeLaplacian).IsMDissipative := by
  have hsa : IsSelfAdjoint (-H.hodgeLaplacian) := by
    have h1 : H.hodgeLaplacian† = H.hodgeLaplacian := H.isSelfAdjoint_hodgeLaplacian
    change (-H.hodgeLaplacian)† = -H.hodgeLaplacian
    rw [adjoint_neg _ H.dense_hodgeLaplacian_domain, h1]
  refine hsa.isMDissipative fun x => ?_
  have := H.re_inner_hodgeLaplacian_self_nonneg x
  rw [LinearPMap.neg_apply, inner_neg_left, _root_.map_neg]
  linarith

/-- `𝐝 𝐝 = 0` in graph form. -/
theorem totalD_graph_comp {x a : PiLp 2 W} (h : (x, a) ∈ H.totalD.graph) :
    (a, 0) ∈ H.totalD.graph := by
  obtain ⟨hx, rfl⟩ := mem_graph_iff_exists.1 h
  exact mem_graph_iff_exists.2 ⟨H.totalD_mapsTo ⟨x, hx⟩, H.totalD_comp_totalD ⟨x, hx⟩⟩

/-- **`𝐝` commutes with `-Δ = L²`**: for `u ∈ D(Δ)` with `Δ u ∈ D(𝐝)`, `𝐝 u ∈ D(Δ)` and
`Δ 𝐝 u = 𝐝 Δ u` (graph form). -/
theorem mem_graph_wave_sq_totalD {u z a b : PiLp 2 W} (huz : (u, z) ∈ H.wave.sq.graph)
    (hua : (u, a) ∈ H.totalD.graph) (hzb : (z, b) ∈ H.totalD.graph) :
    (a, b) ∈ H.wave.sq.graph :=
  mem_graph_sq_sub_of_comp_eq_zero H.totalD_graph_comp H.dual.totalD_graph_comp huz hua hzb

/-- **`𝐝*` commutes with `-Δ = L²`** (graph form). -/
theorem mem_graph_wave_sq_dual_totalD {u z a b : PiLp 2 W} (huz : (u, z) ∈ H.wave.sq.graph)
    (hua : (u, a) ∈ H.dual.totalD.graph) (hzb : (z, b) ∈ H.dual.totalD.graph) :
    (a, b) ∈ H.wave.sq.graph := by
  have hP : ∀ {x a}, (x, a) ∈ H.dual.dual.totalD.graph → (a, 0) ∈ H.dual.dual.totalD.graph :=
    fun h => H.dual.dual.totalD_graph_comp h
  have h := mem_graph_sq_sub_of_comp_eq_zero (P := H.dual.totalD) (Q := H.dual.dual.totalD)
    H.dual.totalD_graph_comp hP (u := u) (z := z) (a := a) (b := b)
    (mem_graph_sq_sub_comm.1 (by rw [dual_dual_totalD]; exact huz)) hua hzb
  rw [dual_dual_totalD] at h
  exact mem_graph_sq_sub_comm.1 h

/-! ### Harmonic forms -/

/-- The harmonic forms `⊕ ℌⁱ ⊆ PiLp 2 W`: the kernel of the Hodge Laplacian. -/
def harmonicSum : Submodule 𝕜 (PiLp 2 W) := H.hodgeLaplacian.ker

theorem mem_harmonicSum_iff {x : PiLp 2 W} : x ∈ H.harmonicSum ↔ ∀ i, x i ∈ H.harmonic i :=
  H.mem_ker_hodgeLaplacian_iff

theorem isClosed_harmonicSum : _root_.IsClosed (H.harmonicSum : Set (PiLp 2 W)) := by
  have h : H.hodgeLaplacian† = H.hodgeLaplacian := H.isSelfAdjoint_hodgeLaplacian
  have hc : H.hodgeLaplacian.IsClosed := h ▸ adjoint_isClosed H.dense_hodgeLaplacian_domain
  exact LinearPMap.isClosed_ker hc

instance : CompleteSpace H.harmonicSum := H.isClosed_harmonicSum.completeSpace_coe

theorem mem_ker_totalD_iff {x : PiLp 2 W} : x ∈ H.totalD.ker ↔ ∀ i, x i ∈ H.cycles i := by
  constructor
  · intro hx
    obtain ⟨y, rfl, hy⟩ := LinearPMap.mem_ker_iff.1 hx
    exact (H.totalD_eq_zero_iff y).1 hy
  · intro hc
    have hx : x ∈ H.totalD.domain := fun i j => H.domain_next_le i j (H.cycles_le_domain i (hc i))
    exact LinearPMap.mem_ker_iff.2 ⟨⟨x, hx⟩, rfl, (H.totalD_eq_zero_iff ⟨x, hx⟩).2 hc⟩

/-- `⊕ ℌⁱ = ker 𝐝 ∩ ker 𝐝*`. -/
theorem mem_harmonicSum_iff_ker {x : PiLp 2 W} :
    x ∈ H.harmonicSum ↔ x ∈ H.totalD.ker ∧ x ∈ H.dual.totalD.ker := by
  rw [mem_harmonicSum_iff, mem_ker_totalD_iff, H.dual.mem_ker_totalD_iff]
  simp only [harmonic_eq_cycles_inf_dual, Submodule.mem_inf]
  exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩, fun h i => ⟨h.1 i, h.2 i⟩⟩

theorem mem_ker_neg_hodgeLaplacian_iff {x : PiLp 2 W} :
    x ∈ (-H.hodgeLaplacian).ker ↔ x ∈ H.harmonicSum := by
  simp only [harmonicSum, LinearPMap.mem_ker_iff, LinearPMap.neg_apply, neg_eq_zero]
  rfl

/-! ### The heat semigroup -/

section Heat

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- The **Hodge heat semigroup** `e^{-tΔ}`: the Lumer–Phillips contraction semigroup of the
m-dissipative `-Δ`. -/
def heatSemigroup : C0Semigroup 𝕜 (PiLp 2 W) := H.isMDissipative_neg_hodgeLaplacian.semigroup

/-- The generator of the heat semigroup is `-Δ`, domain included. -/
theorem generator_heatSemigroup : H.heatSemigroup.generator = -H.hodgeLaplacian :=
  H.isMDissipative_neg_hodgeLaplacian.generator_semigroup

theorem isContraction_heatSemigroup : H.heatSemigroup.IsContraction :=
  H.isMDissipative_neg_hodgeLaplacian.isContraction_semigroup

theorem norm_heatSemigroup_S_apply_le (t : ℝ) (x : PiLp 2 W) :
    ‖H.heatSemigroup.S t x‖ ≤ ‖x‖ :=
  H.isMDissipative_neg_hodgeLaplacian.norm_semigroup_S_apply_le t x

/-- **Uniqueness of the heat semigroup**: every strongly continuous semigroup generated by `-Δ`
is `e^{-tΔ}` for `t ≥ 0`. -/
theorem eqOn_heatSemigroup {G : C0Semigroup 𝕜 (PiLp 2 W)} (hG : G.generator = -H.hodgeLaplacian) :
    EqOn G.S H.heatSemigroup.S (Ici 0) :=
  H.isMDissipative_neg_hodgeLaplacian.eqOn_semigroup hG

/-- **The heat semigroup exists and is unique** (normalized by `S t = 1` for `t < 0`). -/
theorem existsUnique_heatSemigroup :
    ∃! G : C0Semigroup 𝕜 (PiLp 2 W),
      (∀ t < 0, G.S t = 1) ∧ G.IsContraction ∧ G.generator = -H.hodgeLaplacian :=
  H.isMDissipative_neg_hodgeLaplacian.existsUnique_normalized_contraction

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem isSymmetric_neg_hodgeLaplacian : (-H.hodgeLaplacian).IsSymmetric := by
  intro x y
  have h := H.isSkewAdjoint_wave.isSkewSymmetric.isSymmetric_neg_sq x y
  change ⟪-(-H.wave.sq) x, (y : PiLp 2 W)⟫ = ⟪(x : PiLp 2 W), -(-H.wave.sq) y⟫
  rw [inner_neg_left, inner_neg_right, h]

/-- **The heat semigroup is self-adjoint**: `⟪S t x, y⟫ = ⟪x, S t y⟫` for `t ≥ 0`. -/
theorem inner_heatSemigroup_S_left {t : ℝ} (ht : 0 ≤ t) (x y : PiLp 2 W) :
    ⟪H.heatSemigroup.S t x, y⟫ = ⟪x, H.heatSemigroup.S t y⟫ :=
  C0Semigroup.inner_S_left_of_isSymmetric
    (by rw [generator_heatSemigroup]; exact H.isSymmetric_neg_hodgeLaplacian) ht x y

theorem isSelfAdjoint_heatSemigroup_S {t : ℝ} (ht : 0 ≤ t) :
    IsSelfAdjoint (H.heatSemigroup.S t) :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).2 fun x y =>
    H.inner_heatSemigroup_S_left ht x y

/-- **Well-posedness of the Hodge heat equation** `u' = -Δ u + F`: for `u₀ ∈ D(Δ)` and
admissible forcing, a classical solution exists on `[a, b]` and is unique among strong
solutions. -/
theorem existsUnique_classicalSolution_heat {U₀ : PiLp 2 W} (hU₀ : U₀ ∈ H.hodgeLaplacian.domain)
    {F : ℝ → PiLp 2 W} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible (-H.hodgeLaplacian) a b F) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution (-H.hodgeLaplacian) (Icc a b) F U ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution (-H.hodgeLaplacian) (Icc a b) F V →
        EqOn V U (Icc a b) :=
  H.isMDissipative_neg_hodgeLaplacian.existsUnique_classicalSolution hU₀ hF

/-- The orbit `t ↦ e^{-tΔ} u₀` of `u₀ ∈ D(Δ)` is a classical solution of `u' = -Δ u`. -/
theorem isClassicalSolution_heatSemigroup {U₀ : PiLp 2 W} (hU₀ : U₀ ∈ H.hodgeLaplacian.domain)
    (b : ℝ) : Evolution.IsClassicalSolution (-H.hodgeLaplacian) (Icc 0 b) 0
      fun t => H.heatSemigroup.S t U₀ := by
  have h := H.heatSemigroup.isClassicalSolution_orbit
    (by rw [generator_heatSemigroup]; exact hU₀) 0 b
  rw [generator_heatSemigroup] at h
  simpa using h

omit [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
/-- **The energy identity** for the Hodge heat equation: a strong solution of `u' = -Δ u` has
`d/dt ‖u‖² = -2 (‖𝐝 u‖² + ‖𝐝* u‖²)`. -/
theorem hasDerivWithinAt_norm_sq_heat {I : Set ℝ} {U : ℝ → PiLp 2 W}
    (hU : Evolution.IsStrongSolution (-H.hodgeLaplacian) I 0 U) {t : ℝ} (ht : t ∈ I) :
    HasDerivWithinAt (fun s => ‖U s‖ ^ 2)
      (-2 * (‖H.totalD ⟨U t, (hU.mem_domain ht).1.1⟩‖ ^ 2 +
        ‖H.dual.totalD ⟨U t, (hU.mem_domain ht).1.2⟩‖ ^ 2)) I t := by
  have h := hU.hasDerivWithinAt_norm_sq ht
  convert h using 1
  have e := H.re_inner_hodgeLaplacian_self ⟨U t, hU.mem_domain ht⟩
  rw [Pi.zero_apply, add_zero, LinearPMap.neg_apply, inner_neg_left, _root_.map_neg]
  change _ = 2 * -RCLike.re ⟪H.hodgeLaplacian ⟨U t, hU.mem_domain ht⟩, U t⟫
  rw [e]; ring

/-! ### Stationary harmonic forms and the harmonic projection -/

/-- **Harmonic forms are stationary**: `e^{-tΔ} h = h` for `h ∈ ⊕ ℌⁱ`, `t ≥ 0`. -/
theorem heatSemigroup_S_apply_of_mem_harmonicSum {x : PiLp 2 W} (hx : x ∈ H.harmonicSum)
    {t : ℝ} (ht : 0 ≤ t) : H.heatSemigroup.S t x = x :=
  C0Semigroup.S_apply_of_mem_ker
    (by rw [generator_heatSemigroup]; exact H.mem_ker_neg_hodgeLaplacian_iff.2 hx) ht

/-- `P_ℌ e^{-tΔ} = P_ℌ`. -/
theorem starProjection_heatSemigroup_S {t : ℝ} (ht : 0 ≤ t) (x : PiLp 2 W) :
    H.harmonicSum.starProjection (H.heatSemigroup.S t x) = H.harmonicSum.starProjection x :=
  C0Semigroup.starProjection_S_of_isSymmetric
    (by rw [generator_heatSemigroup]; exact H.isSymmetric_neg_hodgeLaplacian) ht
    (fun _ hk => H.heatSemigroup_S_apply_of_mem_harmonicSum hk ht) x

/-- `e^{-tΔ} P_ℌ = P_ℌ`. -/
theorem heatSemigroup_S_starProjection {t : ℝ} (ht : 0 ≤ t) (x : PiLp 2 W) :
    H.heatSemigroup.S t (H.harmonicSum.starProjection x) = H.harmonicSum.starProjection x :=
  H.heatSemigroup_S_apply_of_mem_harmonicSum (H.harmonicSum.starProjection_apply_mem x) ht

/-- **The heat semigroup commutes with the harmonic projection.** -/
theorem heatSemigroup_S_comm_starProjection {t : ℝ} (ht : 0 ≤ t) (x : PiLp 2 W) :
    H.heatSemigroup.S t (H.harmonicSum.starProjection x) =
      H.harmonicSum.starProjection (H.heatSemigroup.S t x) := by
  rw [H.heatSemigroup_S_starProjection ht, H.starProjection_heatSemigroup_S ht]

/-- The heat semigroup preserves `(⊕ ℌⁱ)ᗮ`. -/
theorem heatSemigroup_S_mem_orthogonal {x : PiLp 2 W} (hx : x ∈ H.harmonicSumᗮ) {t : ℝ}
    (ht : 0 ≤ t) : H.heatSemigroup.S t x ∈ H.harmonicSumᗮ := by
  rw [← Submodule.starProjection_apply_eq_zero_iff] at hx ⊢
  rw [H.starProjection_heatSemigroup_S ht, hx]

/-! ### Commuting with `𝐝` and `𝐝*` -/

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem isMDissipative_wave_sq : H.wave.sq.IsMDissipative :=
  H.neg_hodgeLaplacian ▸ H.isMDissipative_neg_hodgeLaplacian

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem wave_sq_domain_le_totalD : H.wave.sq.domain ≤ H.totalD.domain := fun _ hx => hx.1.1

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem wave_sq_domain_le_dual_totalD : H.wave.sq.domain ≤ H.dual.totalD.domain :=
  fun _ hx => hx.1.2

/-- **The heat semigroup commutes with `𝐝`**: if `x ∈ D(𝐝)` then `e^{-tΔ} x ∈ D(𝐝)` and
`𝐝 e^{-tΔ} x = e^{-tΔ} 𝐝 x` (graph form). -/
theorem heatSemigroup_mem_graph_totalD (t : ℝ) {x y : PiLp 2 W} (h : (x, y) ∈ H.totalD.graph) :
    (H.heatSemigroup.S t x, H.heatSemigroup.S t y) ∈ H.totalD.graph := by
  refine H.isMDissipative_neg_hodgeLaplacian.semigroup_mem_graph H.isClosed_totalD
    (fun μ hμ x y hxy => ?_) t h
  rw [H.neg_hodgeLaplacian]
  exact H.isMDissipative_wave_sq.resolvent_mem_graph H.wave_sq_domain_le_totalD
    (fun u hAu => H.mem_graph_wave_sq_totalD (H.wave.sq.mem_graph u)
      (H.totalD.mem_graph ⟨u, H.wave_sq_domain_le_totalD u.2⟩)
      (H.totalD.mem_graph ⟨_, hAu⟩)) hμ hxy

/-- **The heat semigroup commutes with `𝐝*`** (graph form). -/
theorem heatSemigroup_mem_graph_dual_totalD (t : ℝ) {x y : PiLp 2 W}
    (h : (x, y) ∈ H.dual.totalD.graph) :
    (H.heatSemigroup.S t x, H.heatSemigroup.S t y) ∈ H.dual.totalD.graph := by
  refine H.isMDissipative_neg_hodgeLaplacian.semigroup_mem_graph H.dual.isClosed_totalD
    (fun μ hμ x y hxy => ?_) t h
  rw [H.neg_hodgeLaplacian]
  exact H.isMDissipative_wave_sq.resolvent_mem_graph H.wave_sq_domain_le_dual_totalD
    (fun u hAu => H.mem_graph_wave_sq_dual_totalD (H.wave.sq.mem_graph u)
      (H.dual.totalD.mem_graph ⟨u, H.wave_sq_domain_le_dual_totalD u.2⟩)
      (H.dual.totalD.mem_graph ⟨_, hAu⟩)) hμ hxy

theorem totalD_heatSemigroup_S (t : ℝ) (x : H.totalD.domain) :
    ∃ h : H.heatSemigroup.S t x ∈ H.totalD.domain,
      H.totalD ⟨_, h⟩ = H.heatSemigroup.S t (H.totalD x) :=
  mem_graph_iff_exists.1 (H.heatSemigroup_mem_graph_totalD t (H.totalD.mem_graph x))

theorem dual_totalD_heatSemigroup_S (t : ℝ) (x : H.dual.totalD.domain) :
    ∃ h : H.heatSemigroup.S t x ∈ H.dual.totalD.domain,
      H.dual.totalD ⟨_, h⟩ = H.heatSemigroup.S t (H.dual.totalD x) :=
  mem_graph_iff_exists.1 (H.heatSemigroup_mem_graph_dual_totalD t (H.dual.totalD.mem_graph x))

omit [∀ i, CompleteSpace (W i)] [Fintype ι] [∀ i, NormedSpace ℝ (W i)]
  [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem mem_ker_iff_mem_graph {T : PiLp 2 W →ₗ.[𝕜] PiLp 2 W} {x : PiLp 2 W} :
    x ∈ T.ker ↔ (x, 0) ∈ T.graph := by
  rw [LinearPMap.mem_ker_iff, mem_graph_iff_exists]
  exact ⟨fun ⟨y, hy, h0⟩ => ⟨hy ▸ y.2, by subst hy; exact h0⟩, fun ⟨h, h0⟩ => ⟨⟨x, h⟩, rfl, h0⟩⟩

/-- **The heat semigroup preserves cycles**, degree by degree: if `x i ∈ 𝔷ⁱ` for all `i`, then
`(e^{-tΔ} x) i ∈ 𝔷ⁱ`. -/
theorem heatSemigroup_S_mem_cycles {x : PiLp 2 W} (hx : ∀ i, x i ∈ H.cycles i) (t : ℝ) (i : ι) :
    H.heatSemigroup.S t x i ∈ H.cycles i := by
  have h := H.heatSemigroup_mem_graph_totalD t (mem_ker_iff_mem_graph.1 (H.mem_ker_totalD_iff.2 hx))
  rw [_root_.map_zero] at h
  exact H.mem_ker_totalD_iff.1 (mem_ker_iff_mem_graph.2 h) i

/-- **The heat semigroup preserves dual cycles**, degree by degree. -/
theorem heatSemigroup_S_mem_dual_cycles {x : PiLp 2 W} (hx : ∀ i, x i ∈ H.dual.cycles i)
    (t : ℝ) (i : ι) : H.heatSemigroup.S t x i ∈ H.dual.cycles i := by
  have h := H.heatSemigroup_mem_graph_dual_totalD t
    (mem_ker_iff_mem_graph.1 (H.dual.mem_ker_totalD_iff.2 hx))
  rw [_root_.map_zero] at h
  exact H.dual.mem_ker_totalD_iff.1 (mem_ker_iff_mem_graph.2 h) i

/-- **The heat semigroup preserves the boundaries `R(𝐝)`.** -/
theorem heatSemigroup_S_mem_range_totalD {x : PiLp 2 W}
    (hx : x ∈ LinearMap.range H.totalD.toFun) (t : ℝ) :
    H.heatSemigroup.S t x ∈ LinearMap.range H.totalD.toFun := by
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨h, e⟩ := H.totalD_heatSemigroup_S t z
  exact ⟨⟨_, h⟩, e⟩

/-- **The heat semigroup preserves the dual boundaries `R(𝐝*)`.** -/
theorem heatSemigroup_S_mem_range_dual_totalD {x : PiLp 2 W}
    (hx : x ∈ LinearMap.range H.dual.totalD.toFun) (t : ℝ) :
    H.heatSemigroup.S t x ∈ LinearMap.range H.dual.totalD.toFun := by
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨h, e⟩ := H.dual_totalD_heatSemigroup_S t z
  exact ⟨⟨_, h⟩, e⟩

end Heat

end Feec.HilbertComplex
