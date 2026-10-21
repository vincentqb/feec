module

public import Feec.Semigroup.LumerPhillips
public import Feec.HilbertComplex.HodgeLaplacian
public import Feec.Evolution.WellPosed
public import Feec.Evolution.Energy

/-!
# The Hodge heat equation

For a Hilbert complex `H` on a finite index type (any shape, `𝕜 = ℝ` or `ℂ`), with total
differential `𝐝`, its adjoint `𝐝* = 𝐝†`, wave operator `L = 𝐝 − 𝐝*` and Hodge Laplacian
`Δ = -L² = 𝐝 𝐝* + 𝐝* 𝐝` (`Feec.HilbertComplex.hodgeLaplacian`), the **Hodge heat equation**
`u' = -Δ u + F` is well posed, and its semigroup `e^{-tΔ}` is self-adjoint, contractive,
commutes with `𝐝`, `𝐝*` and the harmonic projection, and decays exponentially to the harmonic
part under closed range. No closed range is needed except for the decay.

## Main results

* `HilbertComplex.isMDissipative_neg_hodgeLaplacian`: `-Δ` is m-dissipative (self-adjoint,
  `re ⟪Δ x, x⟫ = ‖𝐝 x‖² + ‖𝐝* x‖² ≥ 0`).
* `HilbertComplex.heatSemigroup`: the Lumer–Phillips contraction semigroup of `-Δ`, with
  `generator_heatSemigroup`, `isContraction_heatSemigroup`, `existsUnique_heatSemigroup`,
  `eqOn_heatSemigroup` (uniqueness), `isSelfAdjoint_heatSemigroup_S`.
* `HilbertComplex.existsUnique_classicalSolution_heat`: classical solutions of
  `u' = -Δ u + F` for `u₀ ∈ D(Δ)` and admissible forcing, unique among strong solutions
  (from `LinearPMap.IsMDissipative.existsUnique_classicalSolution`, any m-dissipative generator).
* `HilbertComplex.hasDerivWithinAt_norm_sq_heat`: the energy identity
  `d/dt ‖u‖² = -2 (‖𝐝 u‖² + ‖𝐝* u‖²)` for strong solutions of `u' = -Δ u`.
* Harmonic forms `⊕ ℌⁱ = ker Δ = ker 𝐝 ∩ ker 𝐝*` (`HilbertComplex.harmonicSum`): stationary
  (`heatSemigroup_S_apply_of_mem_harmonicSum`), and `e^{-tΔ}` commutes with their orthogonal
  projection (`heatSemigroup_S_comm_starProjection`, `starProjection_heatSemigroup_S`).
* `HilbertComplex.heatSemigroup_mem_graph_totalD`, `heatSemigroup_mem_graph_dual_totalD`:
  `e^{-tΔ}` maps `D(𝐝)` and `D(𝐝*)` into themselves and commutes with `𝐝`, `𝐝*`; hence it
  preserves `N(𝐝)`, `N(𝐝*)` (`heatSemigroup_S_mem_cycles`, `heatSemigroup_S_mem_dual_cycles`),
  the ranges `R(𝐝)`, `R(𝐝*)` and their closures, i.e. the three summands of the total Hodge
  decomposition. The key identity is `L² 𝐝 = -𝐝 𝐝* 𝐝 = 𝐝 L²`
  (`LinearPMap.mem_graph_sq_sub_of_comp_eq_zero`), passed to the resolvents and then to the
  Yosida approximations (`LinearPMap.IsMDissipative.resolvent_mem_graph`,
  `LinearPMap.IsMDissipative.semigroup_mem_graph`).
* **Degree-wise invariance**: `Δ` commutes with the degree projections
  `HilbertComplex.degreeProj` (`mem_graph_wave_sq_degreeProj`, from `𝐝 P_p = P_{p ∘ prev} 𝐝`),
  so `e^{-tΔ}` does (`heatSemigroup_S_degreeProj`): `(e^{-tΔ} x)ᵢ` depends only on `xᵢ`
  (`heatSemigroup_S_single_apply`) and a form of degree `i` stays of degree `i`. Hence in every
  degree `e^{-tΔ}` preserves the cycles, boundaries and closed boundaries of `d` and of `d*`
  (`heatSemigroup_S_apply_mem_cycles`, `heatSemigroup_S_apply_mem_boundaries`,
  `heatSemigroup_S_apply_mem_closure_boundaries` and their `dual` versions) and fixes the
  harmonic forms (`heatSemigroup_S_apply_of_mem_harmonic`): it preserves the three summands
  `cl 𝔅ⁱ ⊕ ℌⁱ ⊕ cl 𝔅*ⁱ` of the Hodge decomposition of each `Wⁱ`. The dual complex has the same
  heat semigroup (`heatSemigroup_dual`).
* `HilbertComplex.hasDerivWithinAt_norm_sq_heatSemigroup` and
  `HilbertComplex.norm_sq_heatSemigroup_add_integral`: along the flow from `u₀ ∈ D(Δ)`,
  `‖u(t)‖² + 2 ∫₀ᵗ (‖𝐝 u‖² + ‖𝐝* u‖²) = ‖u₀‖²`.
* `HilbertComplex.exists_poincare_totalD`: closed range at every index gives a total Poincaré
  inequality `‖x‖ ≤ c_P ‖𝐝 x‖` on `D(𝐝) ∩ N(𝐝)ᗮ`; `LinearPMap.norm_le_of_poincare_adjoint` (same
  constant for `𝐝*`) and `LinearPMap.norm_sq_le_of_poincare` give
  `‖x‖² ≤ c_P² (‖𝐝 x‖² + ‖𝐝* x‖²)` on `D(𝐝) ∩ D(𝐝*) ∩ (⊕ ℌⁱ)ᗮ`.
* **`HilbertComplex.norm_heatSemigroup_sub_starProjection_le`**: exponential decay
  `‖e^{-tΔ} u₀ - P_ℌ u₀‖ ≤ e^{-t / c_P²} ‖u₀ - P_ℌ u₀‖`, and
  `tendsto_heatSemigroup_of_closedRangeAt`: `e^{-tΔ} u₀ → P_ℌ u₀` as `t → ∞` when every range is
  closed.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.1–§3.2 (Hodge decomposition, Poincaré inequality, the abstract Hodge Laplacian)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 4 (the abstract Hodge
  Laplacian)
* [A. Gillette, M. Holst, Y. Zhu, *Finite element exterior calculus for evolution problems*][GilletteHolstZhu2017]
  (the Hodge heat equation in FEEC)
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §1.4 (Lumer–Phillips), §4.1–4.2 (the inhomogeneous problem)

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


section Poincare

variable [CompleteSpace E]

/-- **Poincaré inequality for the adjoint, with the same constant**: if `‖x‖ ≤ C ‖T x‖` on
`D(T) ∩ N(T)ᗮ`, then `‖y‖ ≤ C ‖T† y‖` on `D(T†) ∩ N(T†)ᗮ` (`y = T x` with `x ⊥ N(T)`, and
`‖y‖² = ⟪x, T† y⟫`). -/
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

/-- **The Poincaré inequality for `T` and `T†` together**: for a closed densely defined `T` with
`T T = 0` and a Poincaré constant `C` for `T`, every `v ∈ D(T) ∩ D(T†)` orthogonal to
`N(T) ∩ N(T†)` satisfies `‖v‖² ≤ C² (‖T v‖² + ‖T† v‖²)`. Split `v = a + b`, `b = P_{N(T)} v`:
`a ⊥ N(T)`, `b ⊥ N(T†)`, `T a = T v`, `T† b = T† v`. -/
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

/-- **The heat semigroup preserves `N(𝐝)`**, written componentwise: if `x i ∈ 𝔷ⁱ` for all `i`,
then `(e^{-tΔ} x) i ∈ 𝔷ⁱ` for all `i`. The single-degree version is
`heatSemigroup_S_apply_mem_cycles`. -/
theorem heatSemigroup_S_mem_cycles {x : PiLp 2 W} (hx : ∀ i, x i ∈ H.cycles i) (t : ℝ) (i : ι) :
    H.heatSemigroup.S t x i ∈ H.cycles i := by
  have h := H.heatSemigroup_mem_graph_totalD t (mem_ker_iff_mem_graph.1 (H.mem_ker_totalD_iff.2 hx))
  rw [_root_.map_zero] at h
  exact H.mem_ker_totalD_iff.1 (mem_ker_iff_mem_graph.2 h) i

/-- **The heat semigroup preserves `N(𝐝*)`**, written componentwise. The single-degree version is
`heatSemigroup_S_apply_mem_dual_cycles`. -/
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

/-- **The heat semigroup preserves the closed range `cl R(𝐝)`**, one of the three summands of the
total Hodge decomposition `PiLp 2 W = cl R(𝐝) ⊕ ⊕ ℌⁱ ⊕ cl R(𝐝*)`. -/
theorem heatSemigroup_S_mem_closure_range_totalD {x : PiLp 2 W}
    (hx : x ∈ (LinearMap.range H.totalD.toFun).topologicalClosure) (t : ℝ) :
    H.heatSemigroup.S t x ∈ (LinearMap.range H.totalD.toFun).topologicalClosure := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hx ⊢
  exact map_mem_closure (H.heatSemigroup.S t).continuous hx
    fun y hy => H.heatSemigroup_S_mem_range_totalD hy t

/-- The heat semigroup preserves the closed dual boundaries `cl R(𝐝*)`. -/
theorem heatSemigroup_S_mem_closure_range_dual_totalD {x : PiLp 2 W}
    (hx : x ∈ (LinearMap.range H.dual.totalD.toFun).topologicalClosure) (t : ℝ) :
    H.heatSemigroup.S t x ∈ (LinearMap.range H.dual.totalD.toFun).topologicalClosure := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hx ⊢
  exact map_mem_closure (H.heatSemigroup.S t).continuous hx
    fun y hy => H.heatSemigroup_S_mem_range_dual_totalD hy t

end Heat

/-! ### Degree-wise invariance and the energy identity -/

section DegreeProj

variable (𝕜 W) in
/-- The orthogonal projection of `PiLp 2 W` onto the degrees in `{j | p j}`:
`(degreeProj p x) j = x j` if `p j`, `0` otherwise. -/
def degreeProj (p : ι → Prop) [DecidablePred p] : PiLp 2 W →L[𝕜] PiLp 2 W :=
  LinearMap.mkContinuous
    { toFun := fun x => WithLp.toLp 2 fun j => if p j then x j else 0
      map_add' := fun x y => by
        ext j; simp only [PiLp.add_apply]; split_ifs <;> simp
      map_smul' := fun a x => by
        ext j; simp only [PiLp.smul_apply, RingHom.id_apply]
        split_ifs <;> simp } 1 fun x => by
    rw [one_mul]
    refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs <;> simp

variable (p : ι → Prop) [DecidablePred p]

omit [∀ i, CompleteSpace (W i)] in
theorem degreeProj_apply (x : PiLp 2 W) (j : ι) :
    degreeProj 𝕜 W p x j = if p j then x j else 0 := rfl



/-- `(𝐝 x) j = d (prev j) j (x (prev j))`: only the incoming differential contributes. -/
theorem totalD_apply_prev (x : H.totalD.domain) (j : ι) :
    (H.totalD x) j = H.d (c.prev j) j ⟨(x : PiLp 2 W) (c.prev j), x.2 _ j⟩ := by
  rw [totalD_apply]
  refine Finset.sum_eq_single (c.prev j) (fun a _ ha => ?_)
    (fun h => absurd (Finset.mem_univ _) h)
  exact apply_eq_zero_of_eq_zero (H.shape a j fun h => ha (c.prev_eq' h).symm) _

theorem degreeProj_mem_totalD_domain {x : PiLp 2 W} (hx : x ∈ H.totalD.domain) :
    degreeProj 𝕜 W p x ∈ H.totalD.domain := by
  intro a b
  rw [degreeProj_apply]
  split_ifs
  · exact hx a b
  · exact Submodule.zero_mem _

/-- **`𝐝` shifts degrees**: `𝐝 P_p = P_{p ∘ prev} 𝐝` (graph form). -/
theorem mem_graph_totalD_degreeProj {x y : PiLp 2 W} (h : (x, y) ∈ H.totalD.graph) :
    (degreeProj 𝕜 W p x, degreeProj 𝕜 W (p ∘ c.prev) y) ∈ H.totalD.graph := by
  obtain ⟨hx, rfl⟩ := mem_graph_iff_exists.1 h
  refine mem_graph_iff_exists.2 ⟨H.degreeProj_mem_totalD_domain p hx, PiLp.ext fun j => ?_⟩
  rw [totalD_apply_prev]
  conv_rhs => rw [degreeProj_apply]
  by_cases hp : (p ∘ c.prev) j
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hp), totalD_apply_prev]
    exact congrArg (H.d (c.prev j) j) (Subtype.ext (by have hp' : p (c.prev j) := hp; simp [degreeProj_apply, hp']))
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hp)]
    exact apply_mk_eq_zero _ _ (by have hp' : ¬p (c.prev j) := hp; simp [degreeProj_apply, hp'])

/-- On the range of `𝐝` only the degrees `j` with an incoming arrow `prev j → j` matter. -/
theorem degreeProj_eq_of_mem_graph_totalD {q : ι → Prop} [DecidablePred q] {x y : PiLp 2 W}
    (h : (x, y) ∈ H.totalD.graph) (hpq : ∀ j, c.Rel (c.prev j) j → (p j ↔ q j)) :
    degreeProj 𝕜 W p y = degreeProj 𝕜 W q y := by
  obtain ⟨hx, rfl⟩ := mem_graph_iff_exists.1 h
  refine PiLp.ext fun j => ?_
  rw [degreeProj_apply, degreeProj_apply]
  by_cases hr : c.Rel (c.prev j) j
  · by_cases hq : q j
    · simp [hq, (hpq j hr).2 hq]
    · have hp : ¬p j := fun hp => hq ((hpq j hr).1 hp)
      simp [hq, hp]
  · have h0 : H.totalD ⟨x, hx⟩ j = 0 := by
      rw [totalD_apply_prev]; exact apply_eq_zero_of_eq_zero (H.shape _ _ hr) _
    rw [h0, ite_self, ite_self]

/-- **The degree projections commute with `L² = -Δ`** (graph form): `Δ` preserves degrees. -/
theorem mem_graph_wave_sq_degreeProj {u z : PiLp 2 W} (h : (u, z) ∈ H.wave.sq.graph) :
    (degreeProj 𝕜 W p u, degreeProj 𝕜 W p z) ∈ H.wave.sq.graph := by
  obtain ⟨y, huy, hyz⟩ := mem_graph_sq_iff.1 h
  have huy' : (u, y) ∈ (H.totalD - H.dual.totalD).graph := huy
  have hyz' : (y, z) ∈ (H.totalD - H.dual.totalD).graph := hyz
  obtain ⟨a, b, ha, hb, rfl⟩ := mem_graph_sub_iff.1 huy'
  obtain ⟨e₁, e₂, he₁, he₂, rfl⟩ := mem_graph_sub_iff.1 hyz'
  have ha0 := H.totalD_graph_comp ha
  have hb0 := H.dual.totalD_graph_comp hb
  have hbd : (b, -e₁) ∈ H.totalD.graph := by simpa using H.totalD.graph.sub_mem ha0 he₁
  have had : (a, e₂) ∈ H.dual.totalD.graph := by simpa using H.dual.totalD.graph.add_mem he₂ hb0
  have h1 := H.mem_graph_totalD_degreeProj p ha
  have h2 := H.dual.mem_graph_totalD_degreeProj p hb
  have h3 := H.mem_graph_totalD_degreeProj (p ∘ c.prev) ha0
  have h4 := H.mem_graph_totalD_degreeProj (p ∘ c.symm.prev) hbd
  rw [H.degreeProj_eq_of_mem_graph_totalD _ hbd (q := p) (fun j hj => by
    simp only [Function.comp_apply]
    rw [c.symm.prev_eq' (show c.symm.Rel j (c.prev j) from hj)])] at h4
  have h5 := H.dual.mem_graph_totalD_degreeProj (p ∘ c.prev) had
  rw [H.dual.degreeProj_eq_of_mem_graph_totalD _ had (q := p) (fun j hj => by
    simp only [Function.comp_apply]
    rw [c.prev_eq' (show c.Rel j (c.symm.prev j) from hj)])] at h5
  have h6 := H.dual.mem_graph_totalD_degreeProj (p ∘ c.symm.prev) hb0
  rw [_root_.map_zero] at h3 h6
  refine mem_graph_sq_iff.2 ⟨_, mem_graph_sub_iff.2 ⟨_, _, h1, h2, rfl⟩,
    mem_graph_sub_iff.2 ⟨degreeProj 𝕜 W p e₁, degreeProj 𝕜 W p e₂, ?_, ?_, by rw [_root_.map_sub]⟩⟩
  · simpa using H.totalD.graph.sub_mem h3 h4
  · simpa using H.dual.totalD.graph.sub_mem h5 h6

section Heat

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- **The heat semigroup preserves degrees**: `e^{-tΔ}` commutes with every degree projection. -/
theorem heatSemigroup_S_degreeProj (t : ℝ) (x : PiLp 2 W) :
    H.heatSemigroup.S t (degreeProj 𝕜 W p x) = degreeProj 𝕜 W p (H.heatSemigroup.S t x) := by
  set T : PiLp 2 W →ₗ.[𝕜] PiLp 2 W :=
    ((degreeProj 𝕜 W p : PiLp 2 W →L[𝕜] PiLp 2 W) : PiLp 2 W →ₗ[𝕜] PiLp 2 W).toPMap ⊤
  have hT : ∀ x, (x, degreeProj 𝕜 W p x) ∈ T.graph := fun x =>
    mem_graph_iff_exists.2 ⟨Submodule.mem_top, rfl⟩
  have key := H.isMDissipative_neg_hodgeLaplacian.semigroup_mem_graph (T := T)
    (ContinuousLinearMap.isClosed_toPMap_top _) (fun μ hμ x y hxy => ?_) t (hT x)
  · obtain ⟨_, e⟩ := mem_graph_iff_exists.1 key
    exact e.symm
  rw [H.neg_hodgeLaplacian]
  exact H.isMDissipative_wave_sq.resolvent_mem_graph (T := T) (fun _ _ => Submodule.mem_top)
    (fun u _ => H.mem_graph_wave_sq_degreeProj p (H.wave.sq.mem_graph u)) hμ hxy

theorem heatSemigroup_dual : H.dual.heatSemigroup = H.heatSemigroup := by
  have e : -H.dual.hodgeLaplacian = -H.hodgeLaplacian := by
    simp only [hodgeLaplacian, wave_dual, sq_neg]
  have key : ∀ {A B : PiLp 2 W →ₗ.[𝕜] PiLp 2 W} (_ : A = B) (hA : A.IsMDissipative)
      (hB : B.IsMDissipative), hA.semigroup = hB.semigroup := by
    rintro A B rfl hA hB; rfl
  exact key e _ _

variable [DecidableEq ι] {i : ι}

omit [∀ i, CompleteSpace (W i)] [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem degreeProj_eq_single (i : ι) (x : PiLp 2 W) :
    degreeProj 𝕜 W (· = i) x = PiLp.single 2 i (x i) := by
  refine PiLp.ext fun j => ?_
  rw [degreeProj_apply]
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

/-- **`(e^{-tΔ} x)ᵢ` depends only on `xᵢ`**: `(e^{-tΔ} x)ᵢ = (e^{-tΔ} (xᵢ in degree i))ᵢ`. -/
theorem heatSemigroup_S_single_apply (t : ℝ) (x : PiLp 2 W) (i : ι) :
    H.heatSemigroup.S t (PiLp.single 2 i (x i)) i = H.heatSemigroup.S t x i := by
  rw [← degreeProj_eq_single (𝕜 := 𝕜), H.heatSemigroup_S_degreeProj (· = i), degreeProj_apply]
  simp

/-- **A form concentrated in degree `i` stays in degree `i`.** -/
theorem heatSemigroup_S_single_apply_of_ne (t : ℝ) (v : W i) {j : ι} (hj : j ≠ i) :
    H.heatSemigroup.S t (PiLp.single 2 i v) j = 0 := by
  have h := H.heatSemigroup_S_degreeProj (· = i) t (PiLp.single 2 i v)
  rw [degreeProj_eq_single, PiLp.single_eq_same] at h
  rw [h, degreeProj_apply]
  simp [hj]

/-- **The heat semigroup preserves the cycles in each degree**: `xᵢ ∈ 𝔷ⁱ ⇒ (e^{-tΔ} x)ᵢ ∈ 𝔷ⁱ`. -/
theorem heatSemigroup_S_apply_mem_cycles {x : PiLp 2 W} (hx : x i ∈ H.cycles i) (t : ℝ) :
    H.heatSemigroup.S t x i ∈ H.cycles i := by
  rw [← H.heatSemigroup_S_single_apply]
  refine H.heatSemigroup_S_mem_cycles (fun j => ?_) t i
  by_cases hj : j = i
  · subst hj; rwa [PiLp.single_eq_same]
  · rw [PiLp.single_eq_of_ne (p := 2) hj]; exact Submodule.zero_mem _

/-- **Harmonic forms are stationary in each degree**: `xᵢ ∈ ℌⁱ ⇒ (e^{-tΔ} x)ᵢ = xᵢ`. -/
theorem heatSemigroup_S_apply_of_mem_harmonic {x : PiLp 2 W} (hx : x i ∈ H.harmonic i) {t : ℝ}
    (ht : 0 ≤ t) : H.heatSemigroup.S t x i = x i := by
  rw [← H.heatSemigroup_S_single_apply, H.heatSemigroup_S_apply_of_mem_harmonicSum
    (H.mem_harmonicSum_iff.2 fun j => ?_) ht, PiLp.single_eq_same]
  by_cases hj : j = i
  · subst hj; rwa [PiLp.single_eq_same]
  · rw [PiLp.single_eq_of_ne (p := 2) hj]; exact Submodule.zero_mem _

/-- **The heat semigroup preserves the boundaries in each degree**:
`xᵢ ∈ 𝔅ⁱ ⇒ (e^{-tΔ} x)ᵢ ∈ 𝔅ⁱ`. -/
theorem heatSemigroup_S_apply_mem_boundaries {x : PiLp 2 W} (hx : x i ∈ H.boundaries i)
    (t : ℝ) : H.heatSemigroup.S t x i ∈ H.boundaries i := by
  obtain ⟨w, hw⟩ := LinearMap.mem_range.1 hx
  by_cases hr : c.Rel (c.prev i) i
  · have hz : PiLp.single 2 (c.prev i) (w : W (c.prev i)) ∈ H.totalD.domain :=
      H.single_mem_totalDomain _ (by rw [c.next_eq' hr]; exact w.2)
    have hdz : H.totalD ⟨_, hz⟩ i = x i := by
      rw [totalD_apply_prev, ← hw]
      exact congrArg (H.d (c.prev i) i) (Subtype.ext (by simp))
    rw [← H.heatSemigroup_S_single_apply, ← hdz, H.heatSemigroup_S_single_apply]
    obtain ⟨h, e⟩ := H.totalD_heatSemigroup_S t ⟨_, hz⟩
    rw [← e, totalD_apply_prev]
    exact LinearMap.mem_range.2 ⟨_, rfl⟩
  · have h0 : x i = 0 := by rw [← hw]; exact apply_eq_zero_of_eq_zero (H.shape _ _ hr) _
    rw [← H.heatSemigroup_S_single_apply, h0, (PiLp.single_eq_zero_iff 2 i).2 rfl, _root_.map_zero]
    exact Submodule.zero_mem _

theorem continuous_heatSemigroup_S_single (t : ℝ) (i : ι) :
    Continuous fun v : W i => H.heatSemigroup.S t (PiLp.single 2 i v) i :=
  (PiLp.continuous_apply 2 W i).comp ((H.heatSemigroup.S t).continuous.comp
    ((PiLp.continuous_toLp 2 W).comp (continuous_single i)))

/-- **The heat semigroup preserves the closed boundaries in each degree.** -/
theorem heatSemigroup_S_apply_mem_closure_boundaries {x : PiLp 2 W}
    (hx : x i ∈ (H.boundaries i).topologicalClosure) (t : ℝ) :
    H.heatSemigroup.S t x i ∈ (H.boundaries i).topologicalClosure := by
  rw [← H.heatSemigroup_S_single_apply]
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hx ⊢
  exact map_mem_closure (H.continuous_heatSemigroup_S_single t i) hx fun v hv =>
    H.heatSemigroup_S_apply_mem_boundaries (x := PiLp.single 2 i v)
      (by rwa [PiLp.single_eq_same]) t

/-- **The heat semigroup preserves the dual cycles in each degree.** -/
theorem heatSemigroup_S_apply_mem_dual_cycles {x : PiLp 2 W} (hx : x i ∈ H.dual.cycles i)
    (t : ℝ) : H.heatSemigroup.S t x i ∈ H.dual.cycles i := by
  simpa only [heatSemigroup_dual] using H.dual.heatSemigroup_S_apply_mem_cycles hx t

/-- **The heat semigroup preserves the dual boundaries `𝔅*ⁱ` in each degree.** -/
theorem heatSemigroup_S_apply_mem_dual_boundaries {x : PiLp 2 W}
    (hx : x i ∈ H.dual.boundaries i) (t : ℝ) :
    H.heatSemigroup.S t x i ∈ H.dual.boundaries i := by
  simpa only [heatSemigroup_dual] using H.dual.heatSemigroup_S_apply_mem_boundaries hx t

/-- **The heat semigroup preserves the closed dual boundaries in each degree.** -/
theorem heatSemigroup_S_apply_mem_closure_dual_boundaries {x : PiLp 2 W}
    (hx : x i ∈ (H.dual.boundaries i).topologicalClosure) (t : ℝ) :
    H.heatSemigroup.S t x i ∈ (H.dual.boundaries i).topologicalClosure := by
  simpa only [heatSemigroup_dual] using H.dual.heatSemigroup_S_apply_mem_closure_boundaries hx t

end Heat

end DegreeProj

section Energy

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- **The energy identity along the heat flow**: for `u₀ ∈ D(Δ)` and `t ≥ 0`,
`d/dt ‖e^{-tΔ} u₀‖² = -2 (‖e^{-tΔ} 𝐝 u₀‖² + ‖e^{-tΔ} 𝐝* u₀‖²)
= -2 (‖𝐝 e^{-tΔ} u₀‖² + ‖𝐝* e^{-tΔ} u₀‖²)`. -/
theorem hasDerivWithinAt_norm_sq_heatSemigroup (x : H.hodgeLaplacian.domain) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => ‖H.heatSemigroup.S s x‖ ^ 2)
      (-2 * (‖H.heatSemigroup.S t (H.totalD ⟨x, x.2.1.1⟩)‖ ^ 2 +
        ‖H.heatSemigroup.S t (H.dual.totalD ⟨x, x.2.1.2⟩)‖ ^ 2)) (Ici 0) t := by
  have hU := (H.isClassicalSolution_heatSemigroup x.2 (t + 1)).toIsStrongSolution
  have htI : t ∈ Icc 0 (t + 1) := ⟨ht, by linarith⟩
  have h := H.hasDerivWithinAt_norm_sq_heat hU htI
  obtain ⟨h1, e1⟩ := H.totalD_heatSemigroup_S t ⟨x, x.2.1.1⟩
  obtain ⟨h2, e2⟩ := H.dual_totalD_heatSemigroup_S t ⟨x, x.2.1.2⟩
  have hmem : Icc 0 (t + 1) ∈ 𝓝[Ici 0] t := by
    rw [← Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
  rw [← e1, ← e2]
  exact h.mono_of_mem_nhdsWithin hmem

/-- **The integrated energy identity** for the Hodge heat flow: for `u₀ ∈ D(Δ)` and `t ≥ 0`,
`‖e^{-tΔ} u₀‖² + 2 ∫₀ᵗ (‖𝐝 e^{-sΔ} u₀‖² + ‖𝐝* e^{-sΔ} u₀‖²) ds = ‖u₀‖²`, written with
`𝐝 e^{-sΔ} = e^{-sΔ} 𝐝` and `𝐝* e^{-sΔ} = e^{-sΔ} 𝐝*`. -/
theorem norm_sq_heatSemigroup_add_integral (x : H.hodgeLaplacian.domain) {t : ℝ} (ht : 0 ≤ t) :
    ‖H.heatSemigroup.S t x‖ ^ 2 + 2 * ∫ s in 0..t,
      (‖H.heatSemigroup.S s (H.totalD ⟨x, x.2.1.1⟩)‖ ^ 2 +
        ‖H.heatSemigroup.S s (H.dual.totalD ⟨x, x.2.1.2⟩)‖ ^ 2) = ‖(x : PiLp 2 W)‖ ^ 2 := by
  set G := H.heatSemigroup
  set a := H.totalD ⟨x, x.2.1.1⟩
  set b := H.dual.totalD ⟨x, x.2.1.2⟩
  have hg : ContinuousOn (fun s => ‖G.S s a‖ ^ 2 + ‖G.S s b‖ ^ 2) (Ici 0) :=
    ((G.strongCont a).norm.pow 2).add ((G.strongCont b).norm.pow 2)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
    (((G.strongCont x).norm.pow 2).mono Icc_subset_Ici_self)
    (fun s hs => (H.hasDerivWithinAt_norm_sq_heatSemigroup x hs.1.le).mono
      fun r hr => le_of_lt (lt_trans hs.1 hr))
    ((continuousOn_const.mul hg).mono (by
      rw [uIcc_of_le ht]; exact Icc_subset_Ici_self)).intervalIntegrable
  rw [intervalIntegral.integral_const_mul] at hFTC
  have e0 : ((fun s => ‖G.S s x‖) ^ 2) t - ((fun s => ‖G.S s x‖) ^ 2) 0 =
      ‖G.S t x‖ ^ 2 - ‖(x : PiLp 2 W)‖ ^ 2 := by simp
  linarith

end Energy

/-! ### Exponential decay to the harmonic part -/

/-- **The total Poincaré inequality** from closed range at every index: `‖x‖ ≤ C ‖𝐝 x‖` on
`D(𝐝) ∩ N(𝐝)ᗮ`, from the Poincaré inequalities `‖xⁱ‖ ≤ Cᵢ ‖d xⁱ‖` on `Vⁱ ∩ (𝔷ⁱ)ᗮ`. -/
theorem exists_poincare_totalD (h : ∀ i, H.ClosedRangeAt i) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : H.totalD.domain, (x : PiLp 2 W) ∈ H.totalD.kerᗮ →
      ‖(x : PiLp 2 W)‖ ≤ C * ‖H.totalD x‖ := by
  classical
  have hloc : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : (H.d i (c.next i)).domain,
      (x : W i) ∈ (H.cycles i)ᗮ → ‖(x : W i)‖ ≤ C * ‖H.d i (c.next i) x‖ := by
    intro i
    by_cases hr : c.Rel i (c.next i)
    · obtain ⟨C, hC⟩ := (H.closedRangeAt_iff_poincare_of_rel hr).1 (h (c.next i))
      refine ⟨max C 0, le_max_right _ _, fun x hx => (hC x hx).trans ?_⟩
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    · refine ⟨0, le_rfl, fun x hx => ?_⟩
      have htop : H.cycles i = ⊤ := by
        rw [cycles, H.shape _ _ hr]
        exact Submodule.eq_top_iff'.2 fun y => LinearPMap.mem_ker_iff.2
          ⟨⟨y, by simp⟩, rfl, rfl⟩
      rw [htop, Submodule.top_orthogonal_eq_bot, Submodule.mem_bot] at hx
      simp [hx]
  choose Cf hCf0 hCf using hloc
  set C₀ := ∑ i, Cf i ^ 2
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg fun i _ => sq_nonneg _
  refine ⟨C₀ + 1, by positivity, fun x hx => ?_⟩
  have hxi : ∀ i, (x : PiLp 2 W) i ∈ (H.cycles i)ᗮ := by
    intro i
    rw [Submodule.mem_orthogonal]
    intro z hz
    have hs : PiLp.single 2 i z ∈ H.totalD.ker := H.mem_ker_totalD_iff.2 fun k => by
      by_cases hk : k = i
      · subst hk; rw [PiLp.single_eq_same]; exact hz
      · rw [PiLp.single_eq_of_ne (p := 2) hk]; exact Submodule.zero_mem _
    have h0 := Submodule.inner_right_of_mem_orthogonal hs hx
    rw [PiLp.inner_apply, Finset.sum_eq_single i (fun k _ hk => by
      rw [PiLp.single_eq_of_ne (p := 2) hk, inner_zero_left]) (by simp),
      PiLp.single_eq_same] at h0
    exact h0
  have hb : ∀ i, ‖(x : PiLp 2 W) i‖ ^ 2 ≤ Cf i ^ 2 * ‖H.totalD x‖ ^ 2 := by
    intro i
    have h1 := hCf i ⟨(x : PiLp 2 W) i, x.2 i (c.next i)⟩ (hxi i)
    have h2 := H.norm_d_le_norm_totalD x i (c.next i)
    have h3 : ‖(x : PiLp 2 W) i‖ ≤ Cf i * ‖H.totalD x‖ :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (hCf0 i))
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h3 2
  have hsq : ‖(x : PiLp 2 W)‖ ^ 2 ≤ ((C₀ + 1) * ‖H.totalD x‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc ∑ i, ‖(x : PiLp 2 W) i‖ ^ 2 ≤ ∑ i, Cf i ^ 2 * ‖H.totalD x‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => hb i
      _ = C₀ * ‖H.totalD x‖ ^ 2 := by rw [Finset.sum_mul]
      _ ≤ (C₀ + 1) ^ 2 * ‖H.totalD x‖ ^ 2 := by
          gcongr; nlinarith
      _ = ((C₀ + 1) * ‖H.totalD x‖) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

theorem harmonicSum_eq_inf : H.harmonicSum = H.totalD.ker ⊓ H.dual.totalD.ker :=
  Submodule.ext fun _ => H.mem_harmonicSum_iff_ker

/-- **The Poincaré inequality for the Hodge Laplacian**: with a Poincaré constant `cP` for `𝐝`,
`‖x‖² ≤ cP² (‖𝐝 x‖² + ‖𝐝* x‖²) = cP² re ⟪Δ x, x⟫` for `x ∈ D(Δ) ∩ (⊕ ℌⁱ)ᗮ`. -/
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

/-- **Exponential decay of the Hodge heat flow to the harmonic projection**: with a Poincaré
constant `cP` for `𝐝`, `‖e^{-tΔ} u₀ - P_ℌ u₀‖ ≤ e^{-t / cP²} ‖u₀ - P_ℌ u₀‖` for `t ≥ 0`.
Energy method: on `D(Δ) ∩ ℌᗮ`, `re ⟪-Δ u, u⟫ ≤ -‖u‖² / cP²`; then density. -/
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

/-- **Convergence to the harmonic projection**: with a positive Poincaré constant,
`e^{-tΔ} u₀ → P_ℌ u₀` as `t → ∞`. -/
theorem tendsto_heatSemigroup_starProjection {cP : ℝ} (hcP : 0 < cP)
    (hP : ∀ x : H.totalD.domain, (x : PiLp 2 W) ∈ H.totalD.kerᗮ →
      ‖(x : PiLp 2 W)‖ ≤ cP * ‖H.totalD x‖) (u₀ : PiLp 2 W) :
    Tendsto (fun t => H.heatSemigroup.S t u₀) atTop (𝓝 (H.harmonicSum.starProjection u₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hexp : Tendsto (fun t : ℝ => Real.exp (-t / cP ^ 2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.atBot_div_const (by positivity))
  have hlim := hexp.mul_const ‖u₀ - H.harmonicSum.starProjection u₀‖
  rw [zero_mul] at hlim
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 0] with t ht
  exact H.norm_heatSemigroup_sub_starProjection_le hP ht u₀

/-- **Exponential decay under closed range**: if every range of the complex is closed, there is
`cP > 0` with `‖e^{-tΔ} u₀ - P_ℌ u₀‖ ≤ e^{-t / cP²} ‖u₀ - P_ℌ u₀‖` for all `t ≥ 0`, and
`e^{-tΔ} u₀ → P_ℌ u₀`. -/
theorem exists_norm_heatSemigroup_sub_starProjection_le (h : ∀ i, H.ClosedRangeAt i) :
    ∃ cP : ℝ, 0 < cP ∧ ∀ t, 0 ≤ t → ∀ u₀ : PiLp 2 W,
      ‖H.heatSemigroup.S t u₀ - H.harmonicSum.starProjection u₀‖ ≤
        Real.exp (-t / cP ^ 2) * ‖u₀ - H.harmonicSum.starProjection u₀‖ := by
  obtain ⟨cP, hcP, hP⟩ := H.exists_poincare_totalD h
  exact ⟨cP, hcP, fun t ht u₀ => H.norm_heatSemigroup_sub_starProjection_le hP ht u₀⟩

theorem tendsto_heatSemigroup_of_closedRangeAt (h : ∀ i, H.ClosedRangeAt i) (u₀ : PiLp 2 W) :
    Tendsto (fun t => H.heatSemigroup.S t u₀) atTop (𝓝 (H.harmonicSum.starProjection u₀)) := by
  obtain ⟨cP, hcP, hP⟩ := H.exists_poincare_totalD h
  exact H.tendsto_heatSemigroup_starProjection hcP hP u₀

end Decay

end Feec.HilbertComplex
