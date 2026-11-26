module

public import Feec.Evolution.WellPosed
public import Feec.Evolution.Energy

/-!
# Inhomogeneous boundary data by lifting

For operators `A ≤ A_max`, `A` the restriction to homogeneous boundary values, and a lifting `G`
of the boundary data, `U` solves `U' = A_max U + F` with `U − G ∈ D(A)` iff `U − G` solves
`W' = A W + (F − G' + A_max G)`, which gives existence, uniqueness and energy estimates.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Filter

@[expose] public noncomputable section

namespace Feec.Evolution

section General

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] {Amax A : E →ₗ.[𝕜] E} {I : Set ℝ} {F G U V : ℝ → E}

omit [NormedSpace ℝ E] in
theorem _root_.LinearPMap.eq_of_mem_graph {f : E →ₗ.[𝕜] E} {x y₁ y₂ : E}
    (h₁ : (x, y₁) ∈ f.graph) (h₂ : (x, y₂) ∈ f.graph) : y₁ = y₂ := by
  have h := f.graph.sub_mem h₁ h₂
  rw [Prod.mk_sub_mk, sub_self] at h
  exact sub_eq_zero.1 (f.graph_fst_eq_zero_snd h rfl)

omit [NormedSpace ℝ E] in
theorem _root_.LinearPMap.mem_graph_of_le {f g : E →ₗ.[𝕜] E} (hle : f ≤ g) {x y : E}
    (hx : x ∈ f.domain) (h : (x, y) ∈ g.graph) : (x, y) ∈ f.graph := by
  have h₁ : (x, f ⟨x, hx⟩) ∈ f.graph := f.mem_graph ⟨x, hx⟩
  rwa [LinearPMap.eq_of_mem_graph h (LinearPMap.le_graph_iff.2 hle h₁)]

/-- `U` solves `U' = A_max U + F` on `I` **with the boundary values of `G`**: `U − G ∈ D(A)`. -/
structure IsBoundarySolution (Amax A : E →ₗ.[𝕜] E) (I : Set ℝ) (F G U : ℝ → E) : Prop where
  toIsStrongSolution : IsStrongSolution Amax I F U
  sub_mem : ∀ t ∈ I, U t - G t ∈ A.domain

/-- `G` is a **lifting** on `I`: `G(t) ∈ D(A_max)`, `A_max G = AG` and `G' = DG`. -/
structure IsLifting (Amax : E →ₗ.[𝕜] E) (I : Set ℝ) (G DG AG : ℝ → E) : Prop where
  mem_graph : ∀ t ∈ I, (G t, AG t) ∈ Amax.graph
  hasDerivWithinAt : ∀ t ∈ I, HasDerivWithinAt G (DG t) I t

/-- **Reduction to homogeneous boundary values**: `U` solves `U' = A_max U + F` with the boundary
values of `G` iff `U − G` is a strong solution of `W' = A W + (F − G' + A_max G)`. -/
theorem isBoundarySolution_iff (hle : A ≤ Amax) {DG AG : ℝ → E} (hG : IsLifting Amax I G DG AG) :
    IsBoundarySolution Amax A I F G U ↔ IsStrongSolution A I (F - DG + AG) (U - G) := by
  constructor
  · rintro ⟨hU, hsub⟩
    refine IsStrongSolution.of_deriv fun t ht => ?_
    obtain ⟨v, hv, hd⟩ := hU.deriv t ht
    have hg := hG.mem_graph t ht
    have hW : (U t - G t, v - AG t) ∈ Amax.graph := by
      simpa using Amax.graph.sub_mem hv hg
    refine ⟨v - AG t, LinearPMap.mem_graph_of_le hle (hsub t ht) hW, ?_⟩
    have := hd.sub (hG.hasDerivWithinAt t ht)
    convert this using 1
    simp only [Pi.add_apply, Pi.sub_apply]
    abel
  · intro hW
    refine ⟨IsStrongSolution.of_deriv fun t ht => ?_, fun t ht => hW.mem_domain ht⟩
    obtain ⟨w, hw, hd⟩ := hW.deriv t ht
    have hg := hG.mem_graph t ht
    have hU : (U t, w + AG t) ∈ Amax.graph := by
      have := Amax.graph.add_mem (LinearPMap.le_graph_iff.2 hle hw) hg
      simpa using this
    refine ⟨w + AG t, hU, ?_⟩
    have := hd.add (hG.hasDerivWithinAt t ht)
    convert this using 1
    · funext s; simp
    · simp only [Pi.add_apply, Pi.sub_apply]
      abel

theorem isBoundarySolution_zero_iff (hle : A ≤ Amax) :
    IsBoundarySolution Amax A I F 0 U ↔ IsStrongSolution A I F U := by
  have hG : IsLifting Amax I 0 0 0 :=
    ⟨fun _ _ => Amax.graph.zero_mem, fun t _ => hasDerivWithinAt_const t I (0 : E)⟩
  rw [isBoundarySolution_iff hle hG, sub_zero, add_zero, sub_zero]

theorem IsBoundarySolution.sub {F₂ G₂ : ℝ → E} (hU : IsBoundarySolution Amax A I F G U)
    (hV : IsBoundarySolution Amax A I F₂ G₂ V) :
    IsBoundarySolution Amax A I (F - F₂) (G - G₂) (U - V) := by
  refine ⟨hU.toIsStrongSolution.sub hV.toIsStrongSolution, fun t ht => ?_⟩
  have := A.domain.sub_mem (hU.sub_mem t ht) (hV.sub_mem t ht)
  convert this using 1
  simp only [Pi.sub_apply]
  abel

theorem IsBoundarySolution.isStrongSolution_sub (hle : A ≤ Amax)
    (hU : IsBoundarySolution Amax A I F G U) (hV : IsBoundarySolution Amax A I F G V) :
    IsStrongSolution A I 0 (U - V) := by
  have h := hU.sub hV
  rw [sub_self, sub_self] at h
  have := (isBoundarySolution_zero_iff (I := I) (F := 0) (U := U - V) hle).1 h
  exact this

theorem IsBoundarySolution.unique (hle : A ≤ Amax) (hA : A.IsDissipative) {a b : ℝ}
    (hU : IsBoundarySolution Amax A (Icc a b) F G U)
    (hV : IsBoundarySolution Amax A (Icc a b) F G V) (h0 : U a = V a) : EqOn U V (Icc a b) := by
  have hW := hU.isStrongSolution_sub hle hV
  intro t ht
  have := hW.unique hA (IsStrongSolution.zero (A := A) (I := Icc a b)) (by simp [h0]) ht
  simpa [sub_eq_zero] using this

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

theorem IsBoundarySolution.norm_sub_le (hle : A ≤ Amax) (hA : A.IsDissipative) {a b : ℝ}
    {DG AG : ℝ → E} (hG : IsLifting Amax (Icc a b) G DG AG)
    (hU : IsBoundarySolution Amax A (Icc a b) F G U)
    (hc : ContinuousOn (F - DG + AG) (Icc a b)) :
    ∀ t ∈ Icc a b, ‖U t - G t‖ ≤ ‖U a - G a‖ + ∫ s in a..t, ‖F s - DG s + AG s‖ := by
  have hW := (isBoundarySolution_iff hle hG).1 hU
  intro t ht
  simpa using hW.norm_le_add_integral hA hc t ht

theorem IsBoundarySolution.norm_le (hle : A ≤ Amax) (hA : A.IsDissipative) {a b : ℝ}
    {DG AG : ℝ → E} (hG : IsLifting Amax (Icc a b) G DG AG)
    (hU : IsBoundarySolution Amax A (Icc a b) F G U)
    (hc : ContinuousOn (F - DG + AG) (Icc a b)) :
    ∀ t ∈ Icc a b, ‖U t‖ ≤ ‖G t‖ + (‖U a - G a‖ + ∫ s in a..t, ‖F s - DG s + AG s‖) := by
  intro t ht
  calc ‖U t‖ = ‖G t + (U t - G t)‖ := by rw [add_sub_cancel]
    _ ≤ ‖G t‖ + ‖U t - G t‖ := norm_add_le _ _
    _ ≤ _ := by gcongr; exact hU.norm_sub_le hle hA hG hc t ht

theorem IsBoundarySolution.hasDerivWithinAt_norm_sq (hU : IsBoundarySolution Amax A I F G U)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivWithinAt (fun s => ‖U s‖ ^ 2)
      (2 * RCLike.re ⟪Amax ⟨U t, hU.toIsStrongSolution.mem_domain ht⟩ + F t, U t⟫) I t :=
  hU.toIsStrongSolution.hasDerivWithinAt_norm_sq ht

theorem isBoundarySolution_self_unique {a b : ℝ} (hle : A ≤ Amax) (hA : A.IsDissipative)
    (hG : IsStrongSolution Amax (Icc a b) F G) {V : ℝ → E} (hV0 : V a = G a)
    (hV : IsBoundarySolution Amax A (Icc a b) F G V) : EqOn V G (Icc a b) :=
  hV.unique hle hA ⟨hG, fun t _ => by rw [sub_self]; exact A.domain.zero_mem⟩ hV0

end General

section Existence

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] {Amax A : E →ₗ.[𝕜] E}
  {F G DG AG : ℝ → E} {a b : ℝ}

theorem _root_.Feec.C0Semigroup.existsUnique_isBoundarySolution (S : C0Semigroup 𝕜 E)
    (hgen : S.generator = A) (hle : A ≤ Amax) (hG : IsLifting Amax (Icc a b) G DG AG) {U₀ : E}
    (hU₀ : U₀ - G a ∈ A.domain) (hF : ForcingClass.admissible A a b (F - DG + AG)) :
    ∃ U, U a = U₀ ∧ IsBoundarySolution Amax A (Icc a b) F G U ∧
      IsClassicalSolution A (Icc a b) (F - DG + AG) (U - G) ∧
      ∀ V, V a = U₀ → IsBoundarySolution Amax A (Icc a b) F G V → EqOn V U (Icc a b) := by
  subst hgen
  obtain ⟨W, hW0, hW, -⟩ := S.existsUnique_classicalSolution hU₀ hF
  have hUG : (W + G) - G = W := add_sub_cancel_right W G
  have hb : IsBoundarySolution Amax S.generator (Icc a b) F G (W + G) :=
    (isBoundarySolution_iff hle hG).2 (by rw [hUG]; exact hW.toIsStrongSolution)
  refine ⟨W + G, by simp [hW0], hb, by rw [hUG]; exact hW, fun V hV0 hV => fun t ht => ?_⟩
  have hd := hV.isStrongSolution_sub hle hb
  have h0 : (V - (W + G)) a = 0 := by simp [hV0, hW0]
  have := S.isStrongSolution_unique hd IsStrongSolution.zero continuousOn_const (by simpa using h0)
    ht
  simpa [sub_eq_zero] using this

/-- **The lifted Duhamel formula**: `U(t) = G(t) + S(t − a)(U(a) − G(a)) + ∫ₐᵗ S(t − s) f(s) ds`,
`f = F − G' + A_max G`. -/
theorem IsBoundarySolution.eq_add_mild (S : C0Semigroup 𝕜 E) (hgen : S.generator = A)
    (hle : A ≤ Amax) (hG : IsLifting Amax (Icc a b) G DG AG) {U : ℝ → E}
    (hU : IsBoundarySolution Amax A (Icc a b) F G U) (hc : ContinuousOn (F - DG + AG) (Icc a b)) :
    ∀ t ∈ Icc a b, U t = G t + mild S.S a (U a - G a) (F - DG + AG) t := by
  subst hgen
  intro t ht
  have e := ((isBoundarySolution_iff hle hG).1 hU).eq_mild hc t ht
  simp only [Pi.sub_apply] at e
  rw [← e, add_sub_cancel]

/-- **Existence and uniqueness for a skew-adjoint `A ≤ A_max`**, for a lifting `G`, admissible
`F − G' + A_max G` and `U₀ − G(a) ∈ D(A)`. [QuennevilleBelair2015], Thm 4.3 (adapted) -/
theorem existsUnique_isBoundarySolution (hA : A.IsSkewAdjoint) (hle : A ≤ Amax)
    (hG : IsLifting Amax (Icc a b) G DG AG) {U₀ : E} (hU₀ : U₀ - G a ∈ A.domain)
    (hF : ForcingClass.admissible A a b (F - DG + AG)) :
    ∃ U, U a = U₀ ∧ IsBoundarySolution Amax A (Icc a b) F G U ∧
      IsClassicalSolution A (Icc a b) (F - DG + AG) (U - G) ∧
      ∀ V, V a = U₀ → IsBoundarySolution Amax A (Icc a b) F G V → EqOn V U (Icc a b) :=
  hA.group.toC0Semigroup.existsUnique_isBoundarySolution hA.generator_group hle hG hU₀ hF

end Existence

end Feec.Evolution
