module

public import Feec.HilbertComplex.BGG.TimeDependent

/-!
# Constrained evolution: the discrete BGG system (6.3) is not solvable for arbitrary data

Discrete BGG data with the hypotheses of [QuennevilleBelair2015], Prop 6.2 for which (6.3) has no
solution from some initial data, and an instance of `Feec.BGG.exists_discreteSolution_norm_sub_le`
in which the projected algebraic datum violates the compatibility condition (C3).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.2

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped RealInnerProductSpace
open Set Filter Topology

@[expose] public noncomputable section

namespace Feec.Counterexamples.ConstrainedEvolution

open Feec.BGG

/-! ### Data without solutions of (6.3) -/

section Counterexample

/-- `e₁ = (0, 1) ∈ ℝ²`, spanning `ker S₀,ₕ` in `incompatibleSegment`. -/
def kerVector : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1

/-- Discrete BGG data on `ℝ` and `ℝ²`, with `S₀,ₕ` the first coordinate on `Ṽₕ⁰ = ℝ²`. -/
def incompatibleSegment : Segment ℝ ℝ ℝ ℝ (EuclideanSpace ℝ (Fin 2))
    (EuclideanSpace ℝ (Fin 2)) ℝ where
  d0 := LinearMap.id
  d1 := 0
  dt0 := LinearMap.id
  dt1 := 0
  S0 := (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).toLinearMap
  S1 := 0
  d1_d0 := fun _ => rfl
  dt1_dt0 := fun _ => rfl
  anticomm := fun _ => by simp

theorem incompatibleSegment_hyps :
    Function.Injective incompatibleSegment.dt0 ∧ Function.Surjective incompatibleSegment.S0 ∧
      incompatibleSegment.ExactTop ∧ incompatibleSegment.ExactBot ∧
      incompatibleSegment.S0 kerVector = 0 ∧ incompatibleSegment.dt0 kerVector ≠ 0 := by
  refine ⟨fun a b h => h, fun r => ⟨EuclideanSpace.single 0 r, by simp [incompatibleSegment]⟩,
    ?_, ?_,
    by simp [incompatibleSegment, kerVector], ?_⟩
  · simp [Segment.ExactTop, incompatibleSegment, LinearMap.range_id]
  · simp [Segment.ExactBot, incompatibleSegment, LinearMap.range_id]
  · intro h
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) h
    simp [incompatibleSegment, kerVector] at this

/-- For `incompatibleSegment`, no solution of (6.3) has `u(0) = e₁`, and none with `f = 0`
starts from the compatible data `σ₀ = 0`, `φ₀ = e₁`, `u₀ = 0`. -/
theorem not_forall_exists_discreteSolution {T : ℝ} (hT : 0 < T) :
    (∀ f : ℝ → EuclideanSpace ℝ (Fin 2),
      ¬ ∃ s : DiscreteSolution incompatibleSegment T f, s.u 0 = kerVector) ∧
    incompatibleSegment.d0 0 = incompatibleSegment.S0 kerVector ∧
    ¬ ∃ s : DiscreteSolution incompatibleSegment T 0,
      s.σ 0 = 0 ∧ s.φ 0 = kerVector ∧ s.u 0 = 0 := by
  obtain ⟨-, -, -, -, hψ, hdψ⟩ := incompatibleSegment_hyps
  refine ⟨fun f => ?_, by rw [map_zero, hψ], ?_⟩
  · have := not_exists_discreteSolution_of_ker (D := incompatibleSegment) (f := f) hT.le hψ hdψ
    simpa [incompatibleSegment] using this
  · rintro ⟨s, -, hs, -⟩
    exact not_exists_discreteSolution_phi_of_ker hT hψ hdψ ⟨s, hs⟩

end Counterexample

/-! ### An instance where the projected algebraic datum violates (C3) -/

section Counterexample

/-- The zero space, used for the blocks `σ`, `λ`, `M`, `ρ` of the instance. -/
abbrev E0 := EuclideanSpace ℝ (Fin 0)

lemma E0_eq_zero (v : E0) : v = 0 := Subsingleton.elim _ _

/-- BGG data with `Ṽ⁰ = Ṽ¹ = ℝ`, `d = id` on `Ṽ⁰` and all other spaces zero. -/
def projSegment : Segment ℝ E0 E0 E0 ℝ ℝ E0 where
  d0 := 0
  d1 := 0
  dt0 := LinearMap.id
  dt1 := 0
  S0 := 0
  S1 := 0
  d1_d0 _ := rfl
  dt1_dt0 _ := rfl
  anticomm _ := by simp

/-- `ι(σ, u, M, ρ) = u`. -/
def projι : (E0 × ℝ × E0 × E0) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (E0 × E0)).comp (ContinuousLinearMap.snd ℝ E0 (ℝ × E0 × E0))

/-- The form `Ah((x, z), (y, w)) = −x w + z y`. -/
def projAh : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => -(x.1 * y.2) + x.2 * y.1)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)

/-- For `projSegment`, every hypothesis of `exists_discreteSolution_norm_sub_le` holds, yet the
projected algebraic datum `Q(0) = −1` violates (C3). -/
theorem not_projected_compatible_phi {T : ℝ} (hT : 0 < T) :
    Function.Injective projSegment.dt0 ∧ Function.Surjective projSegment.S0 ∧
    (∀ a b, ⟪projι a, projι b⟫ = ⟪a.1, b.1⟫ + ⟪a.2.1, b.2.1⟫ + ⟪a.2.2.1, b.2.2.1⟫ +
      ⟪a.2.2.2, b.2.2.2⟫) ∧
    (∀ a φ b ψ, projAh (projι a, (LinearMap.id : ℝ →ₗ[ℝ] ℝ) φ)
        (projι b, (LinearMap.id : ℝ →ₗ[ℝ] ℝ) ψ) =
      discreteSkewForm projSegment (a, φ) (b, ψ)) ∧
    (∀ a ψ, (0 : (ℝ × ℝ) →ₗ[ℝ] E0) (projι a, (LinearMap.id : ℝ →ₗ[ℝ] ℝ) ψ) =
      projSegment.d0 a.1 - projSegment.S0 ψ) ∧
    (∀ t ∈ Ico 0 T, ∀ a, ⟪(0 : ℝ), projι a⟫ = ⟪(0 : ℝ), a.2.1⟫) ∧
    ContinuousOn (fun t : ℝ => t) (Icc 0 T) ∧ ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Icc 0 T) ∧
    (∀ t ∈ Ico 0 T, HasDerivWithinAt (fun t : ℝ => t) 1 (Ici t) t) ∧
    (∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range
        ((projι : (E0 × ℝ × E0 × E0) →ₗ[ℝ] ℝ).prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ)),
      ⟪(1 : ℝ), η.1⟫ + (0 : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) →ₗ[ℝ] ℝ) (t, 0) η -
        LinearMap.fst ℝ ℝ ℝ η = ⟪(0 : ℝ), η.1⟫) ∧
    (∀ t ∈ Icc 0 T, ((0 : ℝ →L[ℝ] ℝ) t, (-1 : ℝ)) ∈ LinearMap.range
        ((projι : (E0 × ℝ × E0 × E0) →ₗ[ℝ] ℝ).prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ))) ∧
    (∀ t ∈ Icc 0 T, (0 : (ℝ × ℝ) →ₗ[ℝ] E0) ((0 : ℝ →L[ℝ] ℝ) t, -1) = 0) ∧
    (∀ t ∈ Ico 0 T, ∀ η ∈ LinearMap.range
        ((projι : (E0 × ℝ × E0 × E0) →ₗ[ℝ] ℝ).prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ)),
      projAh ((0 : ℝ →L[ℝ] ℝ) t, -1) η - ⟪(0 : E0), (0 : (ℝ × ℝ) →ₗ[ℝ] E0) η⟫ =
        (0 : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) →ₗ[ℝ] ℝ) (t, 0) η - LinearMap.fst ℝ ℝ ℝ η) ∧
    -- the consistency term is nonzero
    (⟪(1 : ℝ), projι (0, projSegment.dt0 1, 0, 0)⟫ ≠ 0) ∧
    -- `Q(0) = −1` violates (C3)
    ¬ (∀ ψ, projSegment.S0 ψ = 0 →
      ⟪projSegment.dt0 (-1), projSegment.dt0 ψ⟫ = ⟪(0 : ℝ), projSegment.dt0 ψ⟫) ∧
    -- no solution of (6.3) starts at `φₕ(0) = Q(0)`
    (∀ s : DiscreteSolution projSegment T (fun _ => 0), s.φ 0 ≠ -1) := by
  have hrange : ∀ η : ℝ × ℝ, η ∈ LinearMap.range
      ((projι : (E0 × ℝ × E0 × E0) →ₗ[ℝ] ℝ).prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) :=
    fun η => ⟨((0, η.1, 0, 0), η.2), by simp [projι]⟩
  refine ⟨fun _ _ h => h, fun _ => ⟨0, Subsingleton.elim _ _⟩, fun a b => ?_, fun a φ b ψ => ?_,
    fun _ _ => Subsingleton.elim _ _, fun _ _ _ => by simp, continuousOn_id, continuousOn_const,
    fun _ _ => (hasDerivAt_id _).hasDerivWithinAt, fun _ _ η _ => ?_, fun _ _ => hrange _,
    fun _ _ => rfl, fun _ _ η _ => ?_, by simp [projι, projSegment], ?_, fun s h => ?_⟩
  · rw [E0_eq_zero a.1, E0_eq_zero a.2.2.1, E0_eq_zero a.2.2.2]
    simp [projι]
  · simp [projAh, projι, discreteSkewForm, projSegment]; ring
  · simp
  · simp [projAh]
  · intro h
    have := h 1 (E0_eq_zero _)
    simp [projSegment] at this
  · have := DiscreteSolution.inner_dt0_phi_eq s ⟨le_rfl, hT⟩ (ψ := 1) (E0_eq_zero _)
    simp [projSegment, h] at this

theorem exists_discreteSolution_projected_ne {T : ℝ} (hT : 0 < T) :
    ∃ s : DiscreteSolution projSegment T (fun _ => 0),
      projι (s.σ 0, s.u 0, s.M 0, s.ρ 0) = (0 : ℝ →L[ℝ] ℝ) 0 ∧
      s.φ 0 ≠ -1 ∧
      ∀ t ∈ Icc 0 T, ‖t - projι (s.σ t, s.u t, s.M t, s.ρ t)‖ ≤
        ‖t - (0 : ℝ →L[ℝ] ℝ) t‖ + ∫ _r in (0:ℝ)..t, ‖(0 : ℝ →L[ℝ] ℝ) 1 - 1‖ := by
  obtain ⟨hdinj, hS, hι, hAh, hBh, hF, hξc, hξ'c, hξd, hcont, hPmem, hPB, hproj, -, -, hno⟩ :=
    not_projected_compatible_phi hT
  obtain ⟨s, h0, -, hbd⟩ :=
    exists_discreteSolution_norm_sub_le hdinj hS projι hι LinearMap.id 0 projAh 0
      hAh hBh 0 hT continuous_const.continuousOn (fun t => t) (fun _ => 1) (fun _ => 0)
      (fun _ => LinearMap.fst ℝ ℝ ℝ) (fun _ => 0) hF hξc hξ'c hξd hcont (fun _ => -1)
      (fun _ => 0) hPmem hPB hproj
  exact ⟨s, h0, hno s, hbd⟩

end Counterexample

end Feec.Counterexamples.ConstrainedEvolution
