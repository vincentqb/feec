module

public import Solution.Verdicts
public import Solution.MirrorProp
public import Solution.Absorbing

/-!
# Which boundary conditions keep the TSD constraints (solution)

`FEEC.constraint_propagation`: `constraint_propagation_of` (`Solution.Engine`), Stone's group
and the Lumer–Phillips semigroup of `Feec` with their reducing-subspace criteria.
`FEEC.tsd_boundary_conditions`: the natural boundary conditions on bounded domains, on domains
star-shaped with respect to a ball, on the unit ball and on boxes (`natural_of`, `starShaped_of`,
`ball_of`, `box_of` of `Solution.Verdicts`, through the grad–curl bridge `Solution.GradCurl`, and
`tsd_not_propagates_of` of `Solution.Bounded` for the system with weak symmetry), the absorbing
boundary conditions (`absorbing_of_eq`, `Solution.Absorbing`) and the mirror boundary conditions
(`mirror_tsd_propagates_of`, `Solution.MirrorProp`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10, §6.1, §6.3
* [T. Kato, *Perturbation Theory for Linear Operators*][Kato1995], §III.5.6

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set MeasureTheory LinearPMap

@[expose] public noncomputable section

namespace FEEC

theorem constraint_propagation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] :
    (∀ L : E →ₗ.[ℝ] E, Dense (L.domain : Set E) → L† = -L →
      ∃ S, IsEvolution L.graph univ S ∧ (∀ t x, ‖S t x‖ = ‖x‖) ∧
        (∀ x ∈ L.domain, ∀ T (u : ℝ → E), u 0 = x → IsStrongSolution L.graph (Icc 0 T) u →
          EqOn u (fun t => S t x) (Icc 0 T)) ∧
        ∀ (K : Submodule ℝ E) [K.HasOrthogonalProjection],
          (IsReducing L K ↔ ∀ t, ∀ x ∈ K, S t x ∈ K) ∧
          ∃ (Ks : Submodule ℝ E) (_ : Ks.HasOrthogonalProjection),
            (Ks : Set E) = invariantCore S K ∧ IsReducing L Ks ∧
            ∀ (M : Submodule ℝ E) [M.HasOrthogonalProjection], M ≤ K → IsReducing L M → M ≤ Ks) ∧
    ∀ A : E →ₗ.[ℝ] E, (∀ x : A.domain, ⟪A x, (x : E)⟫_ℝ ≤ 0) →
      (∀ y, ∃ x : A.domain, (x : E) - A x = y) →
      ∃ S, IsEvolution A.graph (Ici 0) S ∧ (∀ t, 0 ≤ t → ∀ x, ‖S t x‖ ≤ ‖x‖) ∧
        (∀ x ∈ A.domain, ∀ T (u : ℝ → E), u 0 = x → IsStrongSolution A.graph (Icc 0 T) u →
          EqOn u (fun t => S t x) (Icc 0 T)) ∧
        ∀ (K : Submodule ℝ E) [K.HasOrthogonalProjection],
          IsReducing A K ↔ (∀ t, 0 ≤ t → ∀ x ∈ K, S t x ∈ K) ∧
            ∀ t, 0 ≤ t → ∀ x ∈ Kᗮ, S t x ∈ Kᗮ :=
  constraint_propagation_of

theorem tsd_boundary_conditions :
    (∀ Ω : Set (Fin 3 → ℝ), IsOpen Ω → Bornology.IsBounded Ω → Ω.Nonempty →
      (∃ S, IsEvolution (gradCurlWave Ω) univ S) ∧
      (∀ S, IsEvolution (gradCurlWave Ω) univ S →
        ∃ (S₁ : Submodule ℝ (L2Vec Ω 1)) (S₂ : Submodule ℝ (L2Vec Ω 2)),
          IsClosed (S₁ : Set (L2Vec Ω 1)) ∧ IsClosed (S₂ : Set (L2Vec Ω 2)) ∧
          invariantCore S (tsdConstraint Ω) = {U | U.1 = 0 ∧ U.2.1 ∈ S₁ ∧ U.2.2 ∈ S₂} ∧
          (∀ u ∈ S₁, IsTSD₀ (mat1 u)) ∧ (∀ ρ ∈ S₂, IsTSD (mat2 ρ)) ∧
          (∃ u, IsTSD (mat1 u) ∧ u ∉ S₁) ∧ (∃ ρ, IsTSD (mat2 ρ) ∧ ρ ∉ S₂) ∧
          ∃ ρ ∈ S₂, ρ ≠ 0 ∧ ((0, 0, ρ), 0) ∈ gradCurlWave Ω) ∧
      (∃ ρ : L2Vec Ω 2, (∀ a b, ⇑(mat2 ρ a b) =ᵐ[volume.restrict Ω]
          fun x => if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then x 2 else 0) ∧
        (0, 0, ρ) ∈ tsdConstraint Ω ∧ (∃ V, ((0, 0, ρ), V) ∈ gradCurlWave Ω) ∧
        ∀ u T U, 0 < T → U 0 = (0, u, ρ) → IsStrongSolution (gradCurlWave Ω) (Icc 0 T) U →
          ∃ t ∈ Icc 0 T, ¬IsTSD (mat1 (U t).2.1)) ∧
      (∃ u : L2Vec Ω 1, (∀ a b, ∃ φ, IsTestFn Ω φ ∧ ⇑(mat1 u a b) =ᵐ[volume.restrict Ω] φ) ∧
        ∀ v, IsTSD (mat1 v) → (∀ w, IsTSD (mat1 w) → ⟪u - v, w⟫_ℝ = 0) →
          v ∉ (vecOp fun _ => dMin Ω 1).domain) ∧
      closure {u : L2Vec Ω 1 | IsTSD (mat1 u) ∧ u ∈ (vecOp fun _ => dMin Ω 1).domain} ≠
        {u | IsTSD (mat1 u)} ∧
      ∃ U₀, (∃ V, (bggData Ω).IsWave U₀ V) ∧ IsTSDState U₀ ∧ ∀ T > 0,
        (∃ U, U 0 = U₀ ∧ IsStrongSolution {p | (bggData Ω).IsWave p.1 p.2} (Icc 0 T) U) ∧
        ∀ U, U 0 = U₀ → IsStrongSolution {p | (bggData Ω).IsWave p.1 p.2} (Icc 0 T) U →
          (∃ t ∈ Icc 0 T, ¬IsTSD (mat1 (U t).2.1)) ∧
          ∃ t ∈ Icc 0 T, ∃ a i, mat2 (U t).2.2.2 a i ≠ mat2 (U t).2.2.2 i a) ∧
    (∀ Ω : Set (Fin 3 → ℝ), IsOpen Ω → Bornology.IsBounded Ω → Ω.Nonempty →
      (∃ x₀ s, 0 < s ∧ ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) →
      closure {u : L2Vec Ω 1 | IsTSD (mat1 u) ∧ u ∈ (vecOp fun _ => dMin Ω 1).domain} =
        {u | IsTSD₀ (mat1 u)} ∧
      ∀ S, IsEvolution (gradCurlWave Ω) univ S →
        (invariantCore S (tsdConstraint Ω) ⊆ {U | (U, 0) ∈ gradCurlWave Ω} ↔
          ¬∃ ξ > 0, ∃ v : L2Vec Ω 1, v ≠ 0 ∧ IsTSD (mat1 v) ∧ IsEigenfield Ω ξ v ∧
            ∀ h, ¬∃ w ∈ (vecOp fun _ => dMin Ω 1).domain,
              mat1 w = mat2 ((vecOp fun _ => dMin Ω 1) ⟨v, h⟩))) ∧
    (∀ ξ ≠ 0, ∀ v : L2Vec unitBall 1, IsTSD (mat1 v) → IsEigenfield unitBall ξ v →
      (∃ O : Set (Fin 3 → ℝ), IsOpen O ∧ {x | ∑ i, x i ^ 2 ≤ 1} ⊆ O ∧
        ∃ Φ : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℝ, (∀ a b, ContDiffOn ℝ 2 (Φ a b) O) ∧
          ∀ a b, ⇑(mat1 v a b) =ᵐ[volume.restrict unitBall] Φ a b) → v = 0) ∧
    (∀ a ℓ : Fin 3 → ℝ, (∀ i, 0 < ℓ i) →
      (∀ S, IsEvolution (gradCurlWave (box a ℓ)) univ S →
        invariantCore S (tsdConstraint (box a ℓ)) =
          tsdConstraint (box a ℓ) ∩ {U | (U, 0) ∈ gradCurlWave (box a ℓ)} ∧
        ∀ U ∈ invariantCore S (tsdConstraint (box a ℓ)), U.2.1 = 0) ∧
      ∀ (S₁ : Submodule ℝ (L2Vec (box a ℓ) 1)) (S₂ : Submodule ℝ (L2Vec (box a ℓ) 2)),
        (∀ u ∈ S₁, IsTSD (mat1 u)) → (∀ ρ ∈ S₂, IsTSD (mat2 ρ)) → ∀ U,
          IsStrongSolution (gradCurlWave (box a ℓ)) (Ici 0) U →
          ((∀ t ≥ 0, (U t).1 = 0 ∧ (U t).2.1 ∈ S₁ ∧ (U t).2.2 ∈ S₂) ↔
            ((U 0).1 = 0 ∧ (U 0).2.1 ∈ S₁ ∧ (U 0).2.2 ∈ S₂) ∧ (U 0, 0) ∈ gradCurlWave (box a ℓ))) ∧
    ((∃ A : WithLp 2 (L2Mat (cube 3) × L2Mat (cube 3)) →ₗ.[ℝ]
          WithLp 2 (L2Mat (cube 3) × L2Mat (cube 3)),
        (A.graph : SetRel _ _) = absorbing ∧ (∀ x : A.domain, ⟪A x, (x : _)⟫_ℝ ≤ 0) ∧
        ∀ y, ∃ x : A.domain, (x : _) - A x = y) ∧
      (∃ p ∈ absorbing, ⟪p.2, p.1⟫_ℝ < 0) ∧
      ∀ S, IsEvolution absorbing (Ici 0) S → ∃ t ≥ 0, ∃ x ∈ tsdPair, S t x ∉ tsdPair) ∧
    (∀ T U U', IsStrongSolution {p | mirrorData.IsWave p.1 p.2} (Icc 0 T) U →
      IsStrongSolution {p | mirrorData.IsWave p.1 p.2} (Icc 0 T) U' → U 0 = U' 0 →
        EqOn U U' (Icc 0 T)) ∧
    (∀ U₀ V, mirrorData.IsWave U₀ V → IsTSDState U₀ → ∀ T,
      ∃ U, U 0 = U₀ ∧ IsStrongSolution {p | mirrorData.IsWave p.1 p.2} (Icc 0 T) U) ∧
    (∀ T U, IsStrongSolution {p | mirrorData.IsWave p.1 p.2} (Icc 0 T) U → IsTSDState (U 0) →
      ∀ t ∈ Icc 0 T, IsTSDState (U t)) ∧
    ∃ U₀ V₁ V₂ V₃, mirrorData.IsWave U₀ V₁ ∧ mirrorData.IsWave V₁ V₂ ∧
      mirrorData.IsWave V₂ V₃ ∧ IsTSDState U₀ ∧ V₁ ≠ 0 :=
  ⟨fun _ hΩ hb hne => natural_of hΩ hb hne, fun _ hΩ hb hne hstar => starShaped_of hΩ hb hne hstar,
    ball_of, fun _ _ hℓ => box_of hℓ,
    absorbing_of_eq (Feec.Models.Cube.FEM.cubeDomain_eq_Q 3) (Feec.Models.Cube.FEM.cubeDomain_eq_Q 2),
    mirror_tsd_propagates_of⟩

end FEEC
