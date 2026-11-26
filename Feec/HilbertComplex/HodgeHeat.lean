module

public import Feec.Semigroup.LumerPhillips
public import Feec.HilbertComplex.HodgeLaplacian
public import Feec.Evolution.WellPosed
public import Feec.Evolution.Energy

/-!
# The Hodge heat equation

For a finite Hilbert complex the Hodge heat equation `u' = -Δ u + F` is well posed; its semigroup
`e^{-tΔ}` fixes the harmonic forms and, under a Poincaré inequality, decays exponentially to the
harmonic part.

## References

* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap Feec.Operator

@[expose] public noncomputable section

/-! ### Classical solutions for an m-dissipative generator -/

namespace LinearPMap.IsMDissipative

open Feec

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] {A : E →ₗ.[𝕜] E}

/-- **Well-posedness for an m-dissipative generator**: for `U₀ ∈ D(A)` and admissible forcing,
a classical solution of `U' = A U + F`, unique among strong solutions. [Pazy1983], §4.1–4.2 -/
theorem existsUnique_classicalSolution (hA : A.IsMDissipative) {U₀ : E} (hU₀ : U₀ ∈ A.domain)
    {F : ℝ → E} {a b : ℝ} (hF : Evolution.ForcingClass.admissible A a b F) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution A (Icc a b) F U ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution A (Icc a b) F V → EqOn V U (Icc a b) := by
  have h := hA.semigroup.existsUnique_classicalSolution (U₀ := U₀) (F := F) (a := a) (b := b)
  rw [hA.generator_semigroup] at h
  exact h hU₀ hF

end LinearPMap.IsMDissipative

/-! ### Poincaré inequalities for a closed operator and its adjoint -/

namespace LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

section Poincare

variable [CompleteSpace E]

theorem norm_le_of_poincare_adjoint {T S : E →ₗ.[𝕜] E} (hD : Dense (T.domain : Set E))
    (hc : T.IsClosed) (hS : T† = S) {C : ℝ}
    (hP : ∀ x : T.domain, (x : E) ∈ T.kerᗮ → ‖(x : E)‖ ≤ C * ‖T x‖) (y : S.domain)
    (hy : (y : E) ∈ S.kerᗮ) : ‖(y : E)‖ ≤ C * ‖S y‖ := by
  subst hS
  have hR := isClosed_range_of_norm_le hc hP
  rw [orthogonal_ker_adjoint T hD, hR.submodule_topologicalClosure_eq] at hy
  obtain ⟨x, hx⟩ := hy
  obtain ⟨z, hz, hTz⟩ := exists_mem_orthogonal_ker_eq hc x
  have hyz : (y : E) = T z := by rw [hTz]; exact hx.symm
  have h1 : ‖(y : E)‖ ^ 2 ≤ C * ‖(y : E)‖ * ‖T† y‖ := by
    have e : ⟪(y : E), (y : E)⟫_𝕜 = ⟪T† y, (z : E)⟫_𝕜 := by
      rw [adjoint_isFormalAdjoint hD y z]; nth_rewrite 2 [hyz]; rfl
    have h2 : ‖(y : E)‖ ^ 2 = RCLike.re ⟪T† y, (z : E)⟫_𝕜 := by
      rw [← e, inner_self_eq_norm_sq]
    rw [h2]
    calc RCLike.re ⟪T† y, (z : E)⟫_𝕜 ≤ ‖T† y‖ * ‖(z : E)‖ :=
          (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
      _ ≤ ‖T† y‖ * (C * ‖T z‖) := mul_le_mul_of_nonneg_left (hP z hz) (norm_nonneg _)
      _ = C * ‖(y : E)‖ * ‖T† y‖ := by rw [← hyz]; ring
  rcases (norm_nonneg (y : E)).eq_or_lt with h0 | h0
  · have hy0 : y = 0 := Subtype.ext (norm_eq_zero.1 h0.symm)
    rw [← h0, hy0, LinearPMap.map_zero, norm_zero, mul_zero]
  · nlinarith

theorem norm_sq_le_of_poincare {T S : E →ₗ.[𝕜] E} (hD : Dense (T.domain : Set E))
    (hc : T.IsClosed) (hmaps : ∀ x : T.domain, (T x : E) ∈ T.domain)
    (hcomp : ∀ x : T.domain, T ⟨T x, hmaps x⟩ = 0) (hS : T† = S) {C : ℝ}
    (hP : ∀ x : T.domain, (x : E) ∈ T.kerᗮ → ‖(x : E)‖ ≤ C * ‖T x‖) {v : E}
    (hv1 : v ∈ T.domain) (hv2 : v ∈ S.domain) (hv : v ∈ (T.ker ⊓ S.ker)ᗮ) :
    ‖v‖ ^ 2 ≤ C ^ 2 * (‖T ⟨v, hv1⟩‖ ^ 2 + ‖S ⟨v, hv2⟩‖ ^ 2) := by
  have hPS := norm_le_of_poincare_adjoint hD hc hS hP
  subst hS
  have hK : T.kerᗮ ≤ T†.ker := Feec.Operator.orthogonal_ker_le_ker_adjoint hD hmaps hcomp
  have : CompleteSpace T.ker := (isClosed_ker hc).completeSpace_coe
  set K := T.ker
  set b := K.starProjection v
  set a := v - b
  have hbK : b ∈ K := K.starProjection_apply_mem v
  have haK : a ∈ Kᗮ := K.sub_starProjection_mem_orthogonal v
  have haS : a ∈ T†.ker := hK haK
  have hbD : b ∈ T.domain := T.ker_le_domain hbK
  have haD : a ∈ T.domain := T.domain.sub_mem hv1 hbD
  have haD' : a ∈ T†.domain := T†.ker_le_domain haS
  have hbD' : b ∈ T†.domain := by
    have : b = v - a := by simp [a]
    rw [this]; exact T†.domain.sub_mem hv2 haD'
  have hTa : T ⟨a, haD⟩ = T ⟨v, hv1⟩ := by
    have e : (⟨a, haD⟩ : T.domain) = ⟨v, hv1⟩ - ⟨b, hbD⟩ := rfl
    rw [e, LinearPMap.map_sub, (coe_mem_ker_iff (x := ⟨b, hbD⟩)).1 hbK, sub_zero]
  have hSb : T† ⟨b, hbD'⟩ = T† ⟨v, hv2⟩ := by
    have e : (⟨b, hbD'⟩ : T†.domain) = ⟨v, hv2⟩ - ⟨a, haD'⟩ := Subtype.ext (by simp [a])
    rw [e, LinearPMap.map_sub, (coe_mem_ker_iff (x := ⟨a, haD'⟩)).1 haS, sub_zero]
  -- `b ⊥ N(T†)`
  have hbo : b ∈ T†.kerᗮ := by
    rw [Submodule.mem_orthogonal]
    intro k hk
    have hk1 : k - K.starProjection k ∈ Kᗮ := K.sub_starProjection_mem_orthogonal k
    have hk2 : K.starProjection k ∈ K ⊓ T†.ker := by
      refine ⟨K.starProjection_apply_mem k, ?_⟩
      have : K.starProjection k = k - (k - K.starProjection k) := by abel
      rw [this]; exact T†.ker.sub_mem hk (hK hk1)
    have e1 : ⟪k, b⟫_𝕜 = ⟪K.starProjection k, b⟫_𝕜 + ⟪k - K.starProjection k, b⟫_𝕜 := by
      rw [← inner_add_left, add_sub_cancel]
    rw [e1, Submodule.inner_left_of_mem_orthogonal hbK hk1, add_zero]
    have e2 : b = v - a := by simp [a]
    rw [e2, inner_sub_right, Submodule.inner_right_of_mem_orthogonal hk2 hv,
      Submodule.inner_right_of_mem_orthogonal (K.starProjection_apply_mem k) haK, sub_zero]
  have ha := hP ⟨a, haD⟩ haK
  have hb := hPS ⟨b, hbD'⟩ hbo
  rw [hTa] at ha
  rw [hSb] at hb
  have hab : ⟪a, b⟫_𝕜 = 0 := Submodule.inner_left_of_mem_orthogonal hbK haK
  have hv' : v = a + b := by simp [a]
  have hpy : ‖v‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    rw [hv', pow_two, pow_two, pow_two,
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero a b hab]
  have ha2 : ‖a‖ ^ 2 ≤ (C * ‖T ⟨v, hv1⟩‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
  have hb2 : ‖b‖ ^ 2 ≤ (C * ‖T† ⟨v, hv2⟩‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [hpy]
  nlinarith

end Poincare

end LinearPMap

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 c W) [Fintype ι]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### `-Δ` is m-dissipative -/

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

/-! ### Harmonic forms -/

/-- The harmonic forms `⊕ ℌⁱ ⊆ PiLp 2 W`: the kernel of the Hodge Laplacian. -/
def harmonicSum : Submodule 𝕜 (PiLp 2 W) := H.hodgeLaplacian.ker

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

theorem mem_harmonicSum_iff_ker {x : PiLp 2 W} :
    x ∈ H.harmonicSum ↔ x ∈ H.totalD.ker ∧ x ∈ H.dual.totalD.ker := by
  rw [harmonicSum, mem_ker_hodgeLaplacian_iff, mem_ker_totalD_iff, H.dual.mem_ker_totalD_iff]
  simp only [harmonic_eq_cycles_inf_dual, Submodule.mem_inf]
  exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩, fun h i => ⟨h.1 i, h.2 i⟩⟩

theorem mem_ker_neg_hodgeLaplacian_iff {x : PiLp 2 W} :
    x ∈ (-H.hodgeLaplacian).ker ↔ x ∈ H.harmonicSum := by
  simp only [harmonicSum, LinearPMap.mem_ker_iff, LinearPMap.neg_apply, neg_eq_zero]
  rfl

/-! ### The heat semigroup -/

section Heat

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- The **Hodge heat semigroup** `e^{-tΔ}` of the m-dissipative `-Δ`. -/
def heatSemigroup : C0Semigroup 𝕜 (PiLp 2 W) := H.isMDissipative_neg_hodgeLaplacian.semigroup

theorem generator_heatSemigroup : H.heatSemigroup.generator = -H.hodgeLaplacian :=
  H.isMDissipative_neg_hodgeLaplacian.generator_semigroup

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem isSymmetric_neg_hodgeLaplacian : (-H.hodgeLaplacian).IsSymmetric := by
  intro x y
  have h := H.isSkewAdjoint_wave.isSkewSymmetric.isSymmetric_neg_sq x y
  change ⟪-(-H.wave.sq) x, (y : PiLp 2 W)⟫ = ⟪(x : PiLp 2 W), -(-H.wave.sq) y⟫
  rw [inner_neg_left, inner_neg_right, h]

/-- **Well-posedness of the Hodge heat equation** `u' = -Δ u + F`: for `u₀ ∈ D(Δ)` and admissible
forcing, a classical solution on `[a, b]`, unique among strong solutions. -/
theorem existsUnique_classicalSolution_heat {U₀ : PiLp 2 W} (hU₀ : U₀ ∈ H.hodgeLaplacian.domain)
    {F : ℝ → PiLp 2 W} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible (-H.hodgeLaplacian) a b F) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution (-H.hodgeLaplacian) (Icc a b) F U ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution (-H.hodgeLaplacian) (Icc a b) F V →
        EqOn V U (Icc a b) :=
  H.isMDissipative_neg_hodgeLaplacian.existsUnique_classicalSolution hU₀ hF

/-! ### Stationary harmonic forms and the harmonic projection -/

theorem heatSemigroup_S_apply_of_mem_harmonicSum {x : PiLp 2 W} (hx : x ∈ H.harmonicSum)
    {t : ℝ} (ht : 0 ≤ t) : H.heatSemigroup.S t x = x :=
  C0Semigroup.S_apply_of_mem_ker
    (by rw [generator_heatSemigroup]; exact H.mem_ker_neg_hodgeLaplacian_iff.2 hx) ht

theorem starProjection_heatSemigroup_S {t : ℝ} (ht : 0 ≤ t) (x : PiLp 2 W) :
    H.harmonicSum.starProjection (H.heatSemigroup.S t x) = H.harmonicSum.starProjection x :=
  C0Semigroup.starProjection_S_of_isSymmetric
    (by rw [generator_heatSemigroup]; exact H.isSymmetric_neg_hodgeLaplacian) ht
    (fun _ hk => H.heatSemigroup_S_apply_of_mem_harmonicSum hk ht) x

theorem heatSemigroup_S_starProjection {t : ℝ} (ht : 0 ≤ t) (x : PiLp 2 W) :
    H.heatSemigroup.S t (H.harmonicSum.starProjection x) = H.harmonicSum.starProjection x :=
  H.heatSemigroup_S_apply_of_mem_harmonicSum (H.harmonicSum.starProjection_apply_mem x) ht

theorem heatSemigroup_S_mem_orthogonal {x : PiLp 2 W} (hx : x ∈ H.harmonicSumᗮ) {t : ℝ}
    (ht : 0 ≤ t) : H.heatSemigroup.S t x ∈ H.harmonicSumᗮ := by
  rw [← Submodule.starProjection_apply_eq_zero_iff] at hx ⊢
  rw [H.starProjection_heatSemigroup_S ht, hx]

end Heat

/-! ### Exponential decay to the harmonic part -/

theorem harmonicSum_eq_inf : H.harmonicSum = H.totalD.ker ⊓ H.dual.totalD.ker :=
  Submodule.ext fun _ => H.mem_harmonicSum_iff_ker

theorem norm_sq_le_re_inner_hodgeLaplacian {cP : ℝ}
    (hP : ∀ x : H.totalD.domain, (x : PiLp 2 W) ∈ H.totalD.kerᗮ →
      ‖(x : PiLp 2 W)‖ ≤ cP * ‖H.totalD x‖)
    (x : H.hodgeLaplacian.domain) (hx : (x : PiLp 2 W) ∈ H.harmonicSumᗮ) :
    ‖(x : PiLp 2 W)‖ ^ 2 ≤ cP ^ 2 * RCLike.re ⟪H.hodgeLaplacian x, (x : PiLp 2 W)⟫ := by
  rw [H.re_inner_hodgeLaplacian_self]
  rw [harmonicSum_eq_inf] at hx
  exact norm_sq_le_of_poincare H.dense_totalD_domain H.isClosed_totalD H.totalD_mapsTo
    H.totalD_comp_totalD H.adjoint_totalD hP x.2.1.1 x.2.1.2 hx

section Decay

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- **Exponential decay to the harmonic part**: with a Poincaré constant `cP` for `𝐝`,
`‖e^{-tΔ} u₀ - P_ℌ u₀‖ ≤ e^{-t / cP²} ‖u₀ - P_ℌ u₀‖` for `t ≥ 0`. -/
theorem norm_heatSemigroup_sub_starProjection_le {cP : ℝ}
    (hP : ∀ x : H.totalD.domain, (x : PiLp 2 W) ∈ H.totalD.kerᗮ →
      ‖(x : PiLp 2 W)‖ ≤ cP * ‖H.totalD x‖)
    {t : ℝ} (ht : 0 ≤ t) (u₀ : PiLp 2 W) :
    ‖H.heatSemigroup.S t u₀ - H.harmonicSum.starProjection u₀‖ ≤
      Real.exp (-t / cP ^ 2) * ‖u₀ - H.harmonicSum.starProjection u₀‖ := by
  set G := H.heatSemigroup
  set P := H.harmonicSum.starProjection
  set lam : ℝ := (cP ^ 2)⁻¹
  have hgen := H.generator_heatSemigroup
  -- the estimate on `D(Δ) ∩ ℌᗮ`
  have key : ∀ w : PiLp 2 W, w ∈ H.hodgeLaplacian.domain → w ∈ H.harmonicSumᗮ →
      ‖G.S t w‖ ≤ Real.exp (-lam * (t - 0)) * ‖w‖ := by
    intro w hw hwo
    set w' : G.generator.domain := ⟨w, by rw [hgen]; exact hw⟩
    have hdom : ∀ y, y ∈ G.generator.domain → y ∈ H.hodgeLaplacian.domain := fun y hy => by
      rw [hgen] at hy; exact hy
    have happ : ∀ y (hy : y ∈ G.generator.domain),
        G.generator ⟨y, hy⟩ = -H.hodgeLaplacian ⟨y, hdom y hy⟩ := by
      have : ∀ (T : PiLp 2 W →ₗ.[𝕜] PiLp 2 W) (e : T = -H.hodgeLaplacian) y (hy : y ∈ T.domain),
          T ⟨y, hy⟩ = -H.hodgeLaplacian ⟨y, by rw [e] at hy; exact hy⟩ := by
        rintro T rfl y hy; rfl
      exact fun y hy => this _ hgen y hy
    have h := _root_.norm_le_of_re_inner_deriv_le (𝕜 := 𝕜) (g := fun _ => 0) (a := 0) (b := t)
      (lam := lam) (e := fun s => G.S s w) (e' := fun s => G.S s (G.generator w'))
      ((G.strongCont w).mono Icc_subset_Ici_self)
      (fun s hs => G.hasDerivWithinAt_Ici_apply w' hs.1) continuousOn_const (fun _ _ => le_rfl)
      (fun s hs => ?_) t ⟨ht, le_rfl⟩
    · simpa using h
    · have hm := G.mapsTo_domain w' hs.1
      rw [← G.generator_apply_S w' hs.1, happ _ hm, inner_neg_left,
        _root_.map_neg, zero_mul, add_zero]
      set y : H.hodgeLaplacian.domain := ⟨G.S s w, hdom _ hm⟩
      have hyo : (y : PiLp 2 W) ∈ H.harmonicSumᗮ := H.heatSemigroup_S_mem_orthogonal hwo hs.1
      have hP' := H.norm_sq_le_re_inner_hodgeLaplacian hP y hyo
      have hre := H.re_inner_hodgeLaplacian_self_nonneg y
      change -RCLike.re ⟪H.hodgeLaplacian y, (y : PiLp 2 W)⟫ ≤ -lam * ‖(y : PiLp 2 W)‖ ^ 2
      rcases eq_or_ne cP 0 with h0 | h0
      · simp only [lam, h0]; simp; exact hre
      · have hc2 : 0 < cP ^ 2 := by positivity
        have : lam * ‖(y : PiLp 2 W)‖ ^ 2 ≤ RCLike.re ⟪H.hodgeLaplacian y, (y : PiLp 2 W)⟫ := by
          rw [show lam * ‖(y : PiLp 2 W)‖ ^ 2 = ‖(y : PiLp 2 W)‖ ^ 2 / cP ^ 2 by
            simp [lam, div_eq_inv_mul]]
          rw [div_le_iff₀ hc2]; linarith
        linarith
  -- density
  have hS : ∀ u, G.S t u - P u = G.S t (u - P u) := fun u => by
    rw [_root_.map_sub, H.heatSemigroup_S_starProjection ht]
  have hexp : Real.exp (-lam * (t - 0)) = Real.exp (-t / cP ^ 2) := by
    congr 1; simp only [lam, sub_zero]; ring
  have hcl : _root_.IsClosed {u : PiLp 2 W | ‖G.S t (u - P u)‖ ≤
      Real.exp (-t / cP ^ 2) * ‖u - P u‖} :=
    isClosed_le ((G.S t).continuous.comp (continuous_id.sub P.continuous)).norm
      (continuous_const.mul (continuous_id.sub P.continuous).norm)
  have hsub : (H.hodgeLaplacian.domain : Set (PiLp 2 W)) ⊆
      {u : PiLp 2 W | ‖G.S t (u - P u)‖ ≤ Real.exp (-t / cP ^ 2) * ‖u - P u‖} := by
    intro u hu
    have hPu : P u ∈ H.hodgeLaplacian.domain :=
      H.hodgeLaplacian.ker_le_domain (H.harmonicSum.starProjection_apply_mem u)
    have := key (u - P u) (H.hodgeLaplacian.domain.sub_mem hu hPu)
      (H.harmonicSum.sub_starProjection_mem_orthogonal u)
    rw [hexp] at this
    exact this
  have hall := closure_minimal hsub hcl
  rw [H.dense_hodgeLaplacian_domain.closure_eq] at hall
  have := hall (mem_univ u₀)
  rw [Set.mem_ofPred_eq, ← hS] at this
  exact this

end Decay

end Feec.HilbertComplex
