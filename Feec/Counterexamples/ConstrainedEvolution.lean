module

public import Feec.HilbertComplex.BGG.TimeDependent

/-!
# Constrained evolution: the discrete BGG system (6.3) is not well posed for arbitrary data

Thesis Prop 6.2 asserts that the semi-discrete differential-algebraic system (6.3) for the
Hodge wave equation of the complex with weak symmetries has a solution for every initial datum.
This is false, and so is the natural repair with projected algebraic data:

* `not_forall_exists_discreteSolution`: for concrete discrete BGG data satisfying every
  hypothesis of Prop 6.2 (exact rows, `d` injective on `Ṽₕ⁰`, `S₀,ₕ` surjective,
  anticommutation), the initial value `u₀ = e₁ ∈ ker S₀,ₕ` admits no solution for any source,
  and even compatible data with `φ₀ = e₁` admit none. The correct statement is
  `Feec.BGG.exists_discreteSolution_iff` (existence ⇔ the compatibility conditions (C1)–(C3)).
* `not_projected_compatible_phi`: in an instance of the elliptic-projection convergence theorem
  `Feec.BGG.exists_discreteSolution_norm_sub_le`, the projected algebraic datum `Q(0)` violates
  (C3), so `φₕ(0) = Q(0)` is not admissible in general; `exists_discreteSolution_projected_ne`
  exhibits the solution with the admissible datum `φₕ(0) = Φ(σₕ(0), f(0)) ≠ Q(0)`.

The `Feec.BGG.Counterexample.*` names of wave 5 are deprecated aliases.

## References

* [QuennevilleBelair2015], §6.2 ((6.3), Prop 6.2)
-/

open scoped RealInnerProductSpace
open Set Filter Topology

@[expose] public noncomputable section

namespace Feec.Counterexamples.ConstrainedEvolution

open Feec.BGG

/-! ### A concrete counterexample to Prop 6.2 as stated -/

section Counterexample

/-- `e₁ = (0, 1) ∈ ℝ²`, spanning `ker S₀,ₕ` in `incompatibleSegment`. -/
def kerVector : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1

/-- Concrete discrete BGG data refuting Prop 6.2: `Vₕ⁰ = Vₕ¹ = ℝ`, `Ṽₕ⁰ = Ṽₕ¹ = ℝ²`,
`W²ₕ = W̃²ₕ = ℝ`; `d = id` on `Vₕ⁰` and on `Ṽₕ⁰`, `S₀,ₕ` = first coordinate, all other maps
zero. Both rows are exact, `d` is injective on `Ṽₕ⁰`, `S₀,ₕ` is surjective and the
anticommutation holds, yet `ker S₀,ₕ = ℝ e₁ ≠ 0` (`incompatibleSegment_hyps`). -/
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

/-- `incompatibleSegment` satisfies every hypothesis of Prop 6.2 (and of the corrected
`exists_discreteSolution_iff`), both
rows are exact, and `e₁ ∈ ker S₀,ₕ` has `d e₁ ≠ 0`. -/
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

/-- **Thesis Prop 6.2 is false (concrete instance).** For the data `incompatibleSegment`, which
satisfy all
hypotheses of Prop 6.2 (exact rows, `d` injective on `Ṽₕ⁰`, `S₀,ₕ` surjective, anticommutation):
(a) the initial value `u₀ = e₁` admits no solution, for any source `f` and any `σ₀, φ₀, M₀, ρ₀`;
(b) even the compatible data `σ₀ = 0`, `φ₀ = e₁` (so `dσ₀ = S₀,ₕφ₀`), `u₀ = 0`, `f = 0` admit no
solution, so `φ₀` cannot be prescribed freely. This makes `not_exists_discreteSolution_of_ker` and
`not_exists_discreteSolution_phi_of_ker` non-vacuous. Refutes [QuennevilleBelair2015, Prop 6.2].
Thesis: Prop 6.2 (refuted as stated) -/
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

/-! ### A concrete instance where the projected algebraic datum is not admissible -/

section Counterexample

/-- The zero space, used for the blocks `σ`, `λ`, `M`, `ρ` of the instance. -/
abbrev E0 := EuclideanSpace ℝ (Fin 0)

lemma E0_eq_zero (v : E0) : v = 0 := Subsingleton.elim _ _

/-- BGG data with `Ṽ⁰ = Ṽ¹ = ℝ`, `d = id` on `Ṽ⁰` and all other spaces zero. `S₀,ₕ : ℝ → 0` is
surjective with kernel `ℝ`, and `d` is injective, as in the hypotheses of
`exists_discreteSolution_iff_compatible_u`. -/
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

/-- The form `Ah((x, z), (y, w)) = −x w + z y` (`discreteSkewForm` of `projSegment` through
`ι × id`). -/
def projAh : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => -(x.1 * y.2) + x.2 * y.1)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)

/-- **The projected algebraic datum `Q(0)` can violate (C3).** Instance: `projSegment`, `ι = projι`,
`j = id`, `A = 0`, `Ah = projAh`, `Bh = 0`, `P = 0`, exact solution `ξ(t) = t`, `ξ̇ = 1`,
`χ = 0`, `ℓ(t)(x, z) = x`, `F = 0`, `f = 0`, `Q = −1`, `λ_P = 0`, any `T > 0`. All hypotheses
of `exists_discreteSolution_norm_sub_le` hold (listed in the statement, plus `d` injective and
`S₀,ₕ`
surjective). But the consistency term `(ξ̇(0), ι(0, d1, 0, 0)) = 1` is nonzero, so `q = Q(0)`
violates (C3), and no solution of (6.3) has `φₕ(0) = Q(0)`. The solution supplied by
`exists_discreteSolution_norm_sub_le` starts at `Pξ(0)` with `φₕ(0) = Φ(σₕ(0), f(0)) ≠ Q(0)`.

So `φₕ(0) = Q(0)` is not admissible in general, and `projected_compatible_phi_iff` cannot be
improved to an
unconditional statement. This instance only checks the abstract hypotheses: `ℓ` is a free
functional there, and the instance uses that freedom. It is not built from the FE spaces of
§6.3. Repair of [QuennevilleBelair2015, §6.2] (initial data for (6.3)). -/
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

/-- The instance of `not_projected_compatible_phi` is a genuine instance of
`exists_discreteSolution_norm_sub_le` (its hypotheses are discharged by
`not_projected_compatible_phi`):
a solution of (6.3) with the projected dynamic data exists, satisfies the error bound, and has
`φₕ(0) ≠ Q(0) = −1`. -/
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

/-! ### Deprecated names -/

namespace Feec.BGG.Counterexample

@[deprecated (since := "2026-10-17")] alias kerVector :=
  Counterexamples.ConstrainedEvolution.kerVector
@[deprecated (since := "2026-10-17")] alias incompatibleSegment :=
  Counterexamples.ConstrainedEvolution.incompatibleSegment
@[deprecated (since := "2026-10-17")] alias incompatibleSegment_hyps :=
  Counterexamples.ConstrainedEvolution.incompatibleSegment_hyps
@[deprecated (since := "2026-10-17")] alias not_forall_exists_discreteSolution :=
  Counterexamples.ConstrainedEvolution.not_forall_exists_discreteSolution
@[deprecated (since := "2026-10-17")] alias E0 := Counterexamples.ConstrainedEvolution.E0
@[deprecated (since := "2026-10-17")] alias E0_eq_zero :=
  Counterexamples.ConstrainedEvolution.E0_eq_zero
@[deprecated (since := "2026-10-17")] alias projSegment :=
  Counterexamples.ConstrainedEvolution.projSegment
@[deprecated (since := "2026-10-17")] alias projι := Counterexamples.ConstrainedEvolution.projι
@[deprecated (since := "2026-10-17")] alias projAh := Counterexamples.ConstrainedEvolution.projAh
@[deprecated (since := "2026-10-17")] alias not_projected_compatible_phi :=
  Counterexamples.ConstrainedEvolution.not_projected_compatible_phi
@[deprecated (since := "2026-10-17")] alias exists_discreteSolution_projected_ne :=
  Counterexamples.ConstrainedEvolution.exists_discreteSolution_projected_ne

end Feec.BGG.Counterexample
