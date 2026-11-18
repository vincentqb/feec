module

public import Solution.Defs

/-!
# The subcomplex families of `palomar/fem`

`FEEC.fem_wave` is a consequence of the uniform stability of the finite element de Rham complexes,
the theorem `FEEC.fem` of `palomar/fem` (finite element subcomplexes with cochain projections that
extend to uniformly bounded `L²` projections and attain the rate of the Jackson estimates), and of
the inverse estimate. The notions of `FEEC.fem` that the proof uses, the shared block
`SubcomplexFamily` of `palomar/shared/vocabulary.lean.txt` without the graph norms and the rate
`Jackson.ProjRate` of `palomar/fem`, are restated here for the Hilbert complexes of the challenge
(`Solution.Fem` restates and proves the part of `FEEC.fem` that `FEEC.fem_wave` uses).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3–§3.5, §5.5

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Filter Topology Set LinearPMap

@[expose] public noncomputable section

namespace FEEC

namespace HilbertComplex
variable {𝕜 : Type*} [RCLike 𝕜] {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)] {H : HilbertComplex 𝕜 W} {κ : Type*}
/-- A **subcomplex**: subspaces `Vⁱ ⊆ D(d i j)` with `d Vⁱ ⊆ Vʲ`. -/
structure Subcomplex (H : HilbertComplex 𝕜 W) where
  V : ∀ i, Submodule 𝕜 (W i)
  le_domain : ∀ i j, V i ≤ (H.d i j).domain
  mapsTo : ∀ i j (x : W i) (hx : x ∈ V i), (H.d i j ⟨x, le_domain i j hx⟩ : W j) ∈ V j
/-- A **cochain projection** onto `S`: projections `πⁱ : D(dⁱ) → Sⁱ` of the domain complex
commuting with `d`. -/
structure Subcomplex.CochainProjection (S : H.Subcomplex) where
  π : ∀ i, (H.d i (i + 1)).domain →ₗ[𝕜] S.V i
  proj : ∀ i (x : (H.d i (i + 1)).domain), (x : W i) ∈ S.V i → (π i x : W i) = x
  comm : ∀ i (x : (H.d i (i + 1)).domain),
    H.d i (i + 1) ⟨π i x, S.le_domain i (i + 1) (π i x).2⟩ =
      π (i + 1) ⟨H.d i (i + 1) x, H.mapsTo i (i + 1) (i + 1 + 1) x⟩
/-- A **family of subcomplexes** of `H` along the filter `l` (the refinement `h → 0`):
finite-dimensional subcomplexes `Vₕ` with cochain projections `πₕ` (no bound and no
approximation property: these are hypotheses of the theorems). -/
structure SubcomplexFamily (H : HilbertComplex 𝕜 W) (κ : Type*) where
  l : Filter κ
  V : κ → H.Subcomplex
  [finiteDimensional : ∀ h i, FiniteDimensional 𝕜 ((V h).V i)]
  π : ∀ h, (V h).CochainProjection
attribute [instance] SubcomplexFamily.finiteDimensional
/-- **A Jackson estimate** for `F` ([AFW2010], §3.5): a mesh size `hₕ → 0` and, for every
regularity index `s : ρ`, classes `Reg s i L` of `s`-regular forms in `Wⁱ` with bound `L`,
approximated in `Vₕⁱ` at the order `hₕ^{ord s}`: some `v ∈ Vₕⁱ` has `‖x - v‖ ≤ B L hₕ^{ord s}`
and `‖d (x - v)‖ ≤ B L hₕ^{ord s}`. -/
structure SubcomplexFamily.Jackson (F : H.SubcomplexFamily κ) (ρ : Type*) where
  meshSize : κ → ℝ
  meshSize_nonneg : ∀ h, 0 ≤ meshSize h
  tendsto_meshSize : Tendsto meshSize F.l (𝓝 0)
  /-- `Reg s i L x`: `x ∈ Wⁱ` is `s`-regular with bound `L` -/
  Reg : ρ → ∀ i, ℝ → W i → Prop
  ord : ρ → ℝ
  B : ρ → ℤ → ℝ
  jackson : ∀ s h i {L : ℝ} (x : W i), 0 ≤ L → Reg s i L x → ∃ v, ∃ hv : v ∈ (F.V h).V i,
    ‖x - v‖ ≤ B s i * (L * meshSize h ^ ord s) ∧ ∀ j (hx : x ∈ (H.d i j).domain),
      ‖H.d i j ⟨x - v, Submodule.sub_mem _ hx ((F.V h).le_domain i j hv)⟩‖ ≤
        B s i * (L * meshSize h ^ ord s)
/-- The cochain projections of `F` **attain the rate of the Jackson estimate `J`** ([AFW2010],
§5.5): `‖x - πₕ x‖, ‖d x - d πₕ x‖ ≤ B' L hₕ^{ord s}` for every `s`-regular `x ∈ D(d i (i + 1))`
with bound `L`, `B'` independent of `h`, `L` and `x` (`J` gives this for some element of `Vₕ`). -/
def SubcomplexFamily.Jackson.ProjRate {F : H.SubcomplexFamily κ} {ρ : Type*} (J : F.Jackson ρ) :
    Prop :=
  ∃ B' : ρ → ℤ → ℝ, ∀ s h i {L : ℝ} (x : (H.d i (i + 1)).domain), 0 ≤ L → J.Reg s i L x →
    ‖(x : W i) - ((F.π h).π i x : W i)‖ ≤ B' s i * (L * J.meshSize h ^ J.ord s) ∧
      ‖H.d i (i + 1) x - H.d i (i + 1) ⟨_, (F.V h).le_domain i (i + 1) ((F.π h).π i x).2⟩‖ ≤
        B' s i * (L * J.meshSize h ^ J.ord s)
end HilbertComplex

end FEEC
