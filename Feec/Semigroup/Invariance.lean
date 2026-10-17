module

public import Feec.ForMathlib.LinearPMap.Reducing
public import Feec.Semigroup.Basic

/-!
# Invariant subspaces of a group: the invariant core and reducing subspaces

For a strongly continuous group `G` and a subspace `K`:

* `C0Group.invariantCore G K = ⨅ t, (S t)⁻¹ K`: the largest `G`-invariant subspace of `K`
  (`le_invariantCore`, `isGreatest_invariantCore`), closed when `K` is
  (`isClosed_invariantCore`).

For an isometric group on a Hilbert space with generator `A`:

* **`C0Group.IsIsometric.isReducing_iff_invariant`**: `K` reduces `A` iff `S t K ⊆ K` for every
  `t ∈ ℝ`. (`⇒`: `P_K S t x` and `S t P_K x` solve the same equation; `⇐`: `Kᗮ` is invariant
  too, so `P_K` commutes with `S t`.)
* `IsIsometric.isReducing_invariantCore`: `A` is reduced by `invariantCore G K`, which is the
  largest reducing subspace of `A` contained in `K` (`IsIsometric.isGreatest_isReducing`).
* `IsIsometric.apply_mem_invariantCore`, `mem_invariantCore_of_generator_eq_zero` (stationary
  points), `dense_domain_inter_invariantCore`.
* `LinearPMap.IsSkewSymmetric.eq_zero_of_hasDerivAt`: the energy argument (a solution of
  `e' = A e` with `e 0 = 0` vanishes when `A` is skew-symmetric).

## References

* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.10 (groups of isometries)
* [T. Kato, *Perturbation Theory for Linear Operators*][Kato1995], §III.5.6 (reducing subspaces)
-/

open Set Filter Topology LinearPMap

@[expose] public noncomputable section

namespace Feec

variable {𝕜 E : Type*} [RCLike 𝕜]

/-! ### The invariant core -/

namespace C0Group

section NormedSpace

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] (G : C0Group 𝕜 E)

/-- The **invariant core** of `K`: `{x | S t x ∈ K for all t}`, the largest `G`-invariant
subspace of `K`. -/
def invariantCore (K : Submodule 𝕜 E) : Submodule 𝕜 E :=
  ⨅ t : ℝ, K.comap (G.S t : E →ₗ[𝕜] E)

variable {G} {K M : Submodule 𝕜 E}

theorem mem_invariantCore {x : E} : x ∈ G.invariantCore K ↔ ∀ t, G.S t x ∈ K := by
  simp [invariantCore]

theorem invariantCore_le : G.invariantCore K ≤ K := fun x hx => by
  simpa using mem_invariantCore.1 hx 0

/-- The invariant core is invariant. -/
theorem S_mem_invariantCore {x : E} (hx : x ∈ G.invariantCore K) (s : ℝ) :
    G.S s x ∈ G.invariantCore K :=
  mem_invariantCore.2 fun t => by rw [← map_add_apply]; exact mem_invariantCore.1 hx _

theorem map_le_iff_forall {M : Submodule 𝕜 E} :
    (∀ t, M.map (G.S t : E →ₗ[𝕜] E) ≤ M) ↔ ∀ t, ∀ x ∈ M, G.S t x ∈ M := by
  simp only [Submodule.map_le_iff_le_comap]
  exact forall_congr' fun t => Iff.rfl

theorem map_invariantCore_le (t : ℝ) : (G.invariantCore K).map (G.S t : E →ₗ[𝕜] E) ≤ G.invariantCore K :=
  map_le_iff_forall.2 (fun t _ hx => S_mem_invariantCore hx t) t

/-- **Maximality**: every invariant subspace of `K` lies in the invariant core. -/
theorem le_invariantCore (hM : M ≤ K) (hinv : ∀ t, M.map (G.S t : E →ₗ[𝕜] E) ≤ M) :
    M ≤ G.invariantCore K := fun x hx =>
  mem_invariantCore.2 fun t => hM (map_le_iff_forall.1 hinv t x hx)

/-- The invariant core is the largest invariant subspace of `K`. -/
theorem isGreatest_invariantCore :
    IsGreatest {M | M ≤ K ∧ ∀ t, M.map (G.S t : E →ₗ[𝕜] E) ≤ M} (G.invariantCore K) :=
  ⟨⟨invariantCore_le, map_invariantCore_le⟩, fun _ hM => le_invariantCore hM.1 hM.2⟩

theorem invariantCore_eq_self_iff : G.invariantCore K = K ↔ ∀ t, K.map (G.S t : E →ₗ[𝕜] E) ≤ K := by
  refine ⟨fun h => h ▸ map_invariantCore_le, fun h => le_antisymm invariantCore_le
    (le_invariantCore le_rfl h)⟩

theorem invariantCore_mono (h : K ≤ M) : G.invariantCore K ≤ G.invariantCore M := fun _ hx =>
  mem_invariantCore.2 fun t => h (mem_invariantCore.1 hx t)

@[simp] theorem invariantCore_top : G.invariantCore ⊤ = ⊤ :=
  invariantCore_eq_self_iff.2 fun _ => le_top

@[simp] theorem invariantCore_bot : G.invariantCore ⊥ = ⊥ :=
  le_bot_iff.1 invariantCore_le

/-- The invariant core of a closed subspace is closed. -/
theorem isClosed_invariantCore (hK : IsClosed (K : Set E)) :
    IsClosed (G.invariantCore K : Set E) := by
  have e : (G.invariantCore K : Set E) = ⋂ t, (G.S t) ⁻¹' K := by
    ext; simp [mem_invariantCore]
  rw [e]
  exact isClosed_iInter fun t => hK.preimage (G.S t).continuous

end NormedSpace

/-! ### Isometric groups: reducing subspaces -/

section Isometric

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {G : C0Group 𝕜 E} {K : Submodule 𝕜 E}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

instance [CompleteSpace E] [K.HasOrthogonalProjection] :
    (G.invariantCore K).HasOrthogonalProjection := by
  have hK : IsClosed (K : Set E) := by
    rw [← Submodule.orthogonal_orthogonal K]; exact Submodule.isClosed_orthogonal _
  have : CompleteSpace (G.invariantCore K) := (isClosed_invariantCore hK).completeSpace_coe
  infer_instance

/-- An isometric group leaving `K` invariant leaves `Kᗮ` invariant. -/
theorem IsIsometric.S_mem_orthogonal (hG : G.IsIsometric) (hK : ∀ t, ∀ x ∈ K, G.S t x ∈ K)
    (t : ℝ) {y : E} (hy : y ∈ Kᗮ) : G.S t y ∈ Kᗮ := by
  rw [Submodule.mem_orthogonal] at hy ⊢
  intro u hu
  have h := hG.inner_S_left (-t) u y
  rw [neg_neg] at h
  rw [← h]
  exact hy _ (hK _ u hu)

/-- An isometric group leaving the closed subspace `K` invariant commutes with `P_K`. -/
theorem IsIsometric.S_starProjection (hG : G.IsIsometric) [K.HasOrthogonalProjection]
    (hK : ∀ t, ∀ x ∈ K, G.S t x ∈ K) (t : ℝ) (x : E) :
    G.S t (K.starProjection x) = K.starProjection (G.S t x) := by
  refine (K.eq_starProjection_of_mem_orthogonal' (hK t _ (K.starProjection_apply_mem x))
    (z := G.S t (x - K.starProjection x))
    (hG.S_mem_orthogonal hK t (K.sub_starProjection_mem_orthogonal x))
    (by rw [_root_.map_sub]; abel)).symm

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace E]

/-- An invariant closed subspace of an isometric group reduces its generator. -/
theorem IsIsometric.isReducing_of_invariant (hG : G.IsIsometric) [K.HasOrthogonalProjection]
    (hK : ∀ t, ∀ x ∈ K, G.S t x ∈ K) : G.generator.IsReducing K := by
  have hd : ∀ x : G.generator.domain, HasDerivAt (fun t => G.S t (K.starProjection x))
      (K.starProjection (G.generator x)) 0 := fun x => by
    have := (K.starProjection).hasDerivAt_apply_of_hasDerivAt (G.hasDerivAt_generator x)
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    exact hG.S_starProjection hK t x
  have hmem : ∀ x : G.generator.domain, K.starProjection (x : E) ∈ G.generator.domain :=
    fun x => (G.mem_domain_generator_iff _).2 (hd x).differentiableAt
  exact ⟨hmem, fun x => G.generator_apply_eq (hd x)⟩

end Isometric

end C0Group

/-! ### The energy argument -/

section Energy

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedSpace ℝ E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- **Energy argument**: if `A` is skew-symmetric, `e' = A e` on `ℝ` and `e 0 = 0`, then
`e = 0`. -/
theorem _root_.LinearPMap.IsSkewSymmetric.eq_zero_of_hasDerivAt {A : E →ₗ.[𝕜] E}
    (hA : A.IsSkewSymmetric) {e : ℝ → E} (hmem : ∀ s, e s ∈ A.domain)
    (hde : ∀ s, HasDerivAt e (A ⟨e s, hmem s⟩) s) (he : e 0 = 0) (t : ℝ) : e t = 0 := by
  have hn : ∀ s, HasDerivAt (fun s => ⟪e s, e s⟫) 0 s := by
    intro s
    have := (hde s).inner 𝕜 (hde s)
    rwa [hA ⟨e s, hmem s⟩ ⟨e s, hmem s⟩, add_neg_cancel] at this
  have hc := is_const_of_deriv_eq_zero (fun s => (hn s).differentiableAt)
    (fun s => (hn s).deriv) t 0
  simp only [he, inner_zero_left] at hc
  exact inner_self_eq_zero.1 hc

end Energy

namespace C0Group

section Isometric

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [CompleteSpace E] {G : C0Group 𝕜 E} {K M : Submodule 𝕜 E}

/-- A closed subspace reducing the generator of an isometric group is invariant. -/
theorem IsIsometric.invariant_of_isReducing (hG : G.IsIsometric) [K.HasOrthogonalProjection]
    (hK : G.generator.IsReducing K) (t : ℝ) : ∀ x ∈ K, G.S t x ∈ K := by
  set A := G.generator
  set P := K.starProjection
  have hcomm : ∀ x : A.domain, P (G.S t x) = G.S t (P x) := by
    intro x
    have hm1 : ∀ s, P (G.S s x) ∈ A.domain := fun s => hK.proj_mem ⟨_, G.mapsTo_domain x s⟩
    have hm2 : ∀ s, G.S s (P x) ∈ A.domain := fun s => G.mapsTo_domain ⟨_, hK.proj_mem x⟩ s
    set e : ℝ → E := fun s => P (G.S s x) - G.S s (P x)
    have hmem : ∀ s, e s ∈ A.domain := fun s => A.domain.sub_mem (hm1 s) (hm2 s)
    have hde : ∀ s, HasDerivAt e (A ⟨e s, hmem s⟩) s := by
      intro s
      have h1 := P.hasDerivAt_apply_of_hasDerivAt (G.hasDerivAt_apply x s)
      have h2 := G.hasDerivAt_apply' ⟨_, hK.proj_mem x⟩ s
      have e1 : A ⟨P (G.S s x), hm1 s⟩ = P (G.S s (A x)) := by
        rw [hK.comm ⟨_, G.mapsTo_domain x s⟩, G.generator_apply_S]
      have e3 : (⟨e s, hmem s⟩ : A.domain) = ⟨P (G.S s x), hm1 s⟩ - ⟨G.S s (P x), hm2 s⟩ := rfl
      rw [e3, LinearPMap.map_sub, e1]
      exact h1.sub h2
    have h0 := hG.isSkewSymmetric_generator.eq_zero_of_hasDerivAt hmem hde
      (by simp [e]) t
    exact sub_eq_zero.1 h0
  have hall : ∀ x, P (G.S t x) = G.S t (P x) := by
    intro x
    have := Continuous.ext_on G.dense_domain_generator
      (P.continuous.comp (G.S t).continuous) ((G.S t).continuous.comp P.continuous)
      (fun x hx => hcomm ⟨x, hx⟩)
    exact congrFun this x
  intro x hx
  rw [← (K.starProjection_eq_self_iff).2 hx]
  change G.S t (P x) ∈ K
  rw [← hall]
  exact K.starProjection_apply_mem _

/-- **Reducing subspaces of an isometric group**: a closed subspace `K` reduces the generator
iff `S t K ⊆ K` for every `t ∈ ℝ`. -/
theorem IsIsometric.isReducing_iff_invariant (hG : G.IsIsometric) [K.HasOrthogonalProjection] :
    G.generator.IsReducing K ↔ ∀ t, K.map (G.S t : E →ₗ[𝕜] E) ≤ K := by
  rw [map_le_iff_forall]
  exact ⟨fun h t => hG.invariant_of_isReducing h t, hG.isReducing_of_invariant⟩

/-- The invariant core reduces the generator. -/
theorem IsIsometric.isReducing_invariantCore (hG : G.IsIsometric) [K.HasOrthogonalProjection] :
    G.generator.IsReducing (G.invariantCore K) :=
  hG.isReducing_of_invariant fun t _ hx => S_mem_invariantCore hx t

/-- The invariant core is the largest closed subspace of `K` reducing the generator. -/
theorem IsIsometric.le_invariantCore_of_isReducing (hG : G.IsIsometric)
    [M.HasOrthogonalProjection] (hMK : M ≤ K) (hM : G.generator.IsReducing M) :
    M ≤ G.invariantCore K :=
  le_invariantCore hMK ((hG.isReducing_iff_invariant).1 hM)

/-- The generator maps `D(A) ∩ invariantCore K` into `invariantCore K`. -/
theorem IsIsometric.apply_mem_invariantCore (hG : G.IsIsometric) [K.HasOrthogonalProjection]
    (x : G.generator.domain) (hx : (x : E) ∈ G.invariantCore K) :
    G.generator x ∈ G.invariantCore K :=
  hG.isReducing_invariantCore.mapsTo x hx

/-- `D(A) ∩ invariantCore K` is dense in `invariantCore K`. -/
theorem IsIsometric.mem_closure_domain_inter_invariantCore (hG : G.IsIsometric)
    [K.HasOrthogonalProjection] {k : E} (hk : k ∈ G.invariantCore K) :
    k ∈ closure ((G.generator.domain : Set E) ∩ G.invariantCore K) := by
  set N := G.invariantCore K
  have hP : ∀ x ∈ G.generator.domain, N.starProjection x ∈ G.generator.domain :=
    fun x hx => hG.isReducing_invariantCore.proj_mem ⟨x, hx⟩
  have := map_mem_closure N.starProjection.continuous (G.dense_domain_generator k)
    (t := (G.generator.domain : Set E) ∩ N) fun x hx => ⟨hP x hx, N.starProjection_apply_mem x⟩
  rwa [N.starProjection_eq_self_iff.2 hk] at this

end Isometric

section Stationary

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [CompleteSpace E] {G : C0Group 𝕜 E} {K : Submodule 𝕜 E}

/-- A zero of the generator is a stationary point: `S t x = x`. -/
theorem S_apply_eq_of_generator_eq_zero (x : G.generator.domain) (h0 : G.generator x = 0)
    (t : ℝ) : G.S t x = x := by
  have hd : ∀ s, HasDerivAt (fun s => G.S s x) 0 s := fun s => by
    simpa [h0] using G.hasDerivAt_apply x s
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simpa using hc

/-- Stationary points of `K` lie in the invariant core. -/
theorem mem_invariantCore_of_generator_eq_zero (x : G.generator.domain) (hx : (x : E) ∈ K)
    (h0 : G.generator x = 0) : (x : E) ∈ G.invariantCore K :=
  mem_invariantCore.2 fun t => by rw [S_apply_eq_of_generator_eq_zero x h0]; exact hx

end Stationary

end C0Group

end Feec
