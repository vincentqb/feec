module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Adjoints of compositions with bounded operators

* `mem_adjoint_compPMap_domain_iff`, `adjoint_compPMap_apply`: for bounded `J`,
  `(J T)† = T† J†` with domain `{y | J† y ∈ D(T†)}`.
* `exists_adjoint_apply_of_conj`: adjoints under conjugation by scaled unitaries. If
  `U V = id`, `U' V' = id`, `U`, `U'` multiply inner products by `λ`, and `V' d = a d' V` on
  `D(d)`, then `U' D(d'†) ⊆ D(d†)` with `d† U' = conj a • U d'†`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ComplexConjugate
open Set

@[expose] public noncomputable section

namespace LinearPMap

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- `D((J T)†) = {y | J† y ∈ D(T†)}` for bounded `J`. -/
theorem mem_adjoint_compPMap_domain_iff (T : E →ₗ.[𝕜] F) (J : F →L[𝕜] G) (y : G) :
    y ∈ ((J : F →ₗ[𝕜] G).compPMap T)†.domain ↔
      ContinuousLinearMap.adjoint J y ∈ T†.domain := by
  rw [mem_adjoint_domain_iff, mem_adjoint_domain_iff]
  have : ⇑((innerₛₗ 𝕜 y).comp ((J : F →ₗ[𝕜] G).compPMap T).toFun) =
      ⇑((innerₛₗ 𝕜 (ContinuousLinearMap.adjoint J y)).comp T.toFun) := by
    ext x
    change ⟪y, J (T x)⟫_𝕜 = ⟪ContinuousLinearMap.adjoint J y, T x⟫_𝕜
    rw [ContinuousLinearMap.adjoint_inner_left]
  rw [this]
  exact Iff.rfl

/-- `(J T)† y = T† (J† y)` for bounded `J` and densely defined `T`. -/
theorem adjoint_compPMap_apply (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E))
    (J : F →L[𝕜] G) (y : ((J : F →ₗ[𝕜] G).compPMap T)†.domain) :
    ((J : F →ₗ[𝕜] G).compPMap T)† y =
      T† ⟨ContinuousLinearMap.adjoint J y, (mem_adjoint_compPMap_domain_iff T J y).1 y.2⟩ := by
  refine adjoint_apply_eq (T := (J : F →ₗ[𝕜] G).compPMap T) hT y fun x => ?_
  rw [adjoint_isFormalAdjoint hT ⟨_, (mem_adjoint_compPMap_domain_iff T J y).1 y.2⟩ x]
  change ⟪ContinuousLinearMap.adjoint J y, T x⟫_𝕜 = ⟪(y : G), J (T x)⟫_𝕜
  rw [ContinuousLinearMap.adjoint_inner_left]

omit [CompleteSpace F] [CompleteSpace G] in
/-- Adjoints under conjugation by scaled unitaries: if `U V = id`, `U' V' = id`, `U`, `U'`
multiply inner products by `λ`, and `V' (d x) = a • d' (V x)` on `D(d)`, then `U'` maps
`D(d'†)` into `D(d†)` with `d† (U' y) = conj a • U (d'† y)`. -/
theorem exists_adjoint_apply_of_conj {X Y X' Y' : Type*}
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [NormedAddCommGroup X'] [InnerProductSpace 𝕜 X'] [CompleteSpace X']
    [NormedAddCommGroup Y'] [InnerProductSpace 𝕜 Y']
    {d : X →ₗ.[𝕜] Y} {d' : X' →ₗ.[𝕜] Y'} (hd : Dense (d.domain : Set X))
    (hd' : Dense (d'.domain : Set X'))
    {U : X' →L[𝕜] X} {U' : Y' →L[𝕜] Y} {V : X →L[𝕜] X'} {V' : Y →L[𝕜] Y'} {lam : 𝕜} {a : 𝕜}
    (hUV : ∀ x, U (V x) = x) (hUV' : ∀ y, U' (V' y) = y)
    (hU : ∀ p q, ⟪U p, U q⟫_𝕜 = lam * ⟪p, q⟫_𝕜) (hU' : ∀ p q, ⟪U' p, U' q⟫_𝕜 = lam * ⟪p, q⟫_𝕜)
    (hVdom : ∀ x : d.domain, V x ∈ d'.domain)
    (hV : ∀ x : d.domain, V' (d x) = a • d' ⟨V x, hVdom x⟩) (y : d'†.domain) :
    ∃ h : U' y ∈ d†.domain, d† ⟨U' y, h⟩ = conj a • U (d'† y) := by
  have key : ∀ x : d.domain, ⟪conj a • U (d'† y), (x : X)⟫_𝕜 = ⟪U' y, d x⟫_𝕜 := by
    intro x
    have e1 := adjoint_isFormalAdjoint hd' y ⟨V x, hVdom x⟩
    calc ⟪conj a • U (d'† y), (x : X)⟫_𝕜 = a * ⟪U (d'† y), U (V x)⟫_𝕜 := by
            rw [inner_smul_left, RCLike.conj_conj, hUV]
        _ = a * (lam * ⟪(d'† y : X'), V x⟫_𝕜) := by rw [hU]
        _ = lam * ⟪(y : Y'), a • d' ⟨V x, hVdom x⟩⟫_𝕜 := by
            rw [inner_smul_right]; simp only at e1; rw [e1]; ring
        _ = ⟪U' y, d x⟫_𝕜 := by
            rw [← hV, ← hU', hUV']
  have hmem := mem_adjoint_domain_of_exists _ ⟨_, key⟩
  exact ⟨hmem, adjoint_apply_eq hd ⟨_, hmem⟩ key⟩

end LinearPMap
