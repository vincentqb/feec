module

public import Solution.Bridge
public import Solution.Rational
public import Feec.HilbertComplex.Approximation.FullyDiscrete
public import Feec.HilbertComplex.Approximation.HeatCrime
public import Feec.HilbertComplex.Approximation.RationalScheme

/-!
# The bridge for windows and evolutions

The window operators of the challenge are those of `Feec` (`HilbertComplex.totalD_eq`,
`HilbertComplex.wave_eq`, `HilbertComplex.heat_eq`), closed ranges of the complex give closed
ranges of its windows (`HilbertComplex.closedRangeAt_window`), strong solutions are `Feec`'s
(`isStrongSolution_iff`), and the conclusions of the dissipative and fully discrete FEEC theorems
of `Feec` give the evolution verdict of the challenge (`evolutionVerdict_of`, with the rational
schemes of `Solution.Rational`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015], §4.4–§4.6
* [P. Brenner, V. Thomée, *On Rational Approximations of Semigroups*][BrennerThomee1979]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Set LinearPMap

@[expose] public noncomputable section

namespace FEEC

variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

/-! ### Evolutions -/

section Evolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] {κ : Type*}

omit [CompleteSpace E] [IsScalarTower ℝ 𝕜 E] in
theorem IsStrongSolution.congr {A : SetRel E E} {I : Set ℝ} {u v : ℝ → E}
    (hu : IsStrongSolution A I u) (h : EqOn v u I) : IsStrongSolution A I v :=
  ⟨hu.1.congr h, fun t ht => by
    obtain ⟨w, hw, hd⟩ := hu.2 t ht
    exact ⟨w, h ht ▸ hw, hd.congr h (h ht)⟩⟩

omit [CompleteSpace E] [IsScalarTower ℝ 𝕜 E] in
/-- **The strong solutions are those of the earlier challenge** (stated for a `LinearPMap`): for
the graph of `A`, continuous on `I` with, at every `t ∈ I`, a derivative `v` within `I` and
`(u t, v) ∈ A.graph`. -/
theorem isStrongSolution_graph_iff {A : E →ₗ.[𝕜] E} {I : Set ℝ} {u : ℝ → E} :
    IsStrongSolution A.graph I u ↔
      ContinuousOn u I ∧ ∀ t ∈ I, ∃ v, (u t, v) ∈ A.graph ∧ HasDerivWithinAt u v I t :=
  Iff.rfl

omit [CompleteSpace E] [IsScalarTower ℝ 𝕜 E] in
theorem isStrongSolution_iff {A : E →ₗ.[𝕜] E} {I : Set ℝ} {u : ℝ → E} :
    IsStrongSolution A.graph I u ↔ Feec.Evolution.IsStrongSolution A I 0 u := by
  refine ⟨fun h => ⟨h.1, fun t ht => ?_⟩, fun h => ⟨h.continuousOn, fun t ht => ?_⟩⟩
  · obtain ⟨v, hv, hd⟩ := h.2 t ht
    exact ⟨v, hv, by simpa using hd⟩
  · obtain ⟨v, hv, hd⟩ := h.deriv t ht
    exact ⟨v, hv, by simpa using hd⟩

omit [IsScalarTower ℝ 𝕜 E] in
/-- **The evolution verdict from `Feec`'s**: the conclusions of the dissipative and fully discrete
FEEC theorems, restated. -/
theorem evolutionVerdict_of {A : E →ₗ.[𝕜] E} {l : Filter κ} {X : κ → Type*}
    [∀ h, NormedAddCommGroup (X h)] [∀ h, InnerProductSpace 𝕜 (X h)] [∀ h, CompleteSpace (X h)]
    [∀ h, NormedSpace ℝ (X h)] [∀ h, IsScalarTower ℝ 𝕜 (X h)] {ι : ∀ h, X h →L[𝕜] E} {B : ∀ h, X h →L[𝕜] X h} {S S' : ℝ → E →L[𝕜] E}
    (hSS' : ∀ t, 0 ≤ t → S t = S' t)
    (hA : A.IsMDissipative)
    (hB : ∀ h x, RCLike.re ⟪B h x, x⟫_𝕜 ≤ 0)
    (hsol : ∀ (x : A.domain) (T : ℝ),
      Feec.Evolution.IsClassicalSolution A (Icc 0 T) 0 fun t => S' t x)
    (huniq : ∀ (x : A.domain) (T : ℝ) (U : ℝ → E), U 0 = x →
      Feec.Evolution.IsStrongSolution A (Icc 0 T) 0 U → EqOn U (fun t => S' t x) (Icc 0 T))
    (hanti : ∀ x, AntitoneOn (fun t => ‖S' t x‖) (Ici 0)) (hS0 : ∀ x, S' 0 x = x)
    (hconv : ∀ (x : E) (v : ∀ h, X h), Tendsto (fun h => ι h (v h)) l (𝓝 x) → ∀ T : ℝ,
      TendstoUniformlyOn (fun h t => ι h ((Feec.C0Group.ofBounded (B h)).S t (v h)))
        (fun t => S' t x) l (Icc 0 T))
    (hrat : ∀ (r : Feec.TimeStepping.RationalScheme) (_ : r.IsAStable) {p : ℕ} (_ : r.HasOrder p)
      (_ : 0 < p) (τ : κ → ℝ) (_ : ∀ h, 0 < τ h), Tendsto τ l (𝓝 0) →
      ∀ (x : E) (v : ∀ h, X h), Tendsto (fun h => ι h (v h)) l (𝓝 x) → ∀ (T ε : ℝ), 0 < ε →
        ∀ᶠ h in l, ∀ n : ℕ, (n : ℝ) * τ h ∈ Icc 0 T →
          ‖S' (n * τ h) x - ι h ((r.apply ((τ h : 𝕜) • B h) ^ n) (v h))‖ < ε) :
    EvolutionVerdict A l X ι B S where
  dense := hA.dense_domain
  solution x hx T := (isStrongSolution_iff.2 (hsol ⟨x, hx⟩ T).toIsStrongSolution).congr
    fun t ht => by simp only [hSS' t ht.1]
  unique x hx T u hu0 hu := fun t ht => by
    simp only [hSS' t ht.1]; exact huniq ⟨x, hx⟩ T u hu0 (isStrongSolution_iff.1 hu) ht
  initial x := by rw [hSS' 0 le_rfl]; exact hS0 x
  contraction x t ht := by
    have := hanti x (Set.mem_Ici.2 le_rfl) ht ht
    dsimp only at this
    rwa [hS0, ← hSS' t ht] at this
  semidiscrete x v hv T := by
    simpa only [semiflow, Feec.C0Group.ofBounded_S] using
      (hconv x v hv T).congr_right fun t ht => by simp only [hSS' t ht.1]
  rational P Q hr p hp hp0 τ hτ hτ0 x v hv T ε hε := by
    filter_upwards [hrat hr.scheme hr.scheme_isAStable (hr.scheme_hasOrder hp) hp0 τ hτ hτ0 x v hv
      T ε hε] with h hh n hn
    rw [hSS' _ hn.1, hr.rationalApply_eq]
    exact hh n hn
  rational_temporal P Q hr p hp :=
    ⟨(hr.scheme.remainder p).supNorm + 1 / (p + 1).factorial, fun h τ hτ n w => by
      rw [norm_sub_rev, hr.rationalApply_eq]
      exact hr.scheme.norm_apply_pow_sub_exp_le (hB h) hr.scheme_isAStable (hr.scheme_hasOrder hp)
        hτ n w⟩

end Evolution

/-! ### Windows -/

namespace HilbertComplex

section Window

variable (H : HilbertComplex 𝕜 W) (a : ℤ) (m : ℕ)

theorem totalD_eq : H.totalD a m = (H.toFeec.window a m).totalD := by
  refine LinearPMap.ext rfl fun x hx hy => ?_
  ext j
  rw [Feec.HilbertComplex.totalD_apply]
  rfl

theorem wave_eq : H.wave a m = (H.toFeec.window a m).wave := by
  rw [wave, totalD_eq, Feec.HilbertComplex.wave_eq]

omit [∀ i, CompleteSpace (W i)] in
theorem sq_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : sq A = A.sq := by
  have hd : (sq A).domain = A.sq.domain := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hx⟩
      exact ⟨hx, hy⟩
    · rintro ⟨hx, hAx⟩
      exact ⟨Submodule.mem_map.2 ⟨⟨x, hx⟩, hAx, rfl⟩, hx⟩
  exact LinearPMap.ext hd fun x hx hy => rfl

theorem heat_eq : sq (H.wave a m) = -(H.toFeec.window a m).hodgeLaplacian := by
  rw [sq_eq, wave_eq, Feec.HilbertComplex.hodgeLaplacian, neg_neg]

/-- Closed ranges of `H` in the degrees `a + 1, …, a + m - 1` give closed ranges of the window. -/
theorem closedRangeAt_window
    (hcr : ∀ i : Fin m, 0 < (i : ℕ) → IsClosed (H.boundaries (a + (i : ℕ)) : Set (W (a + (i : ℕ)))))
    (i : Fin m) :
    (H.toFeec.window a m).ClosedRangeAt i := by
  by_cases hi : (ComplexShape.window m).Rel ((ComplexShape.window m).prev i) i
  · rw [Feec.HilbertComplex.ClosedRangeAt, Feec.HilbertComplex.boundaries_eq _ hi]
    have hrel : (ComplexShape.up ℤ).Rel (a + (((ComplexShape.window m).prev i : Fin m) : ℕ))
        (a + ((i : ℕ) : ℤ)) := by
      change _ + 1 = _
      rw [ComplexShape.window_rel] at hi
      omega
    have hi0 : 0 < (i : ℕ) := by rw [ComplexShape.window_rel] at hi; omega
    have := (H.closedRangeAt_iff _).2 (hcr i hi0)
    rwa [Feec.HilbertComplex.ClosedRangeAt, H.toFeec.boundaries_eq hrel] at this
  · rw [Feec.HilbertComplex.ClosedRangeAt, Feec.HilbertComplex.boundaries_eq_bot_of_not_rel _ hi,
      Submodule.bot_coe]
    exact isClosed_singleton

end Window

end HilbertComplex

end FEEC
