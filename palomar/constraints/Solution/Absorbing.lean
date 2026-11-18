module

public import Solution.Engine
public import Solution.Proxy
public import Feec.Models.Cube.AbsorbingTSD

/-!
# Absorbing boundary conditions: the challenge's problem is `Feec`'s

The challenge's absorbing problem is stated on the cube `cube 3` with boundary data on `cube 2`;
`absorbingOn Ω₃ Ω₂` is the same problem on any pair of sets, `absorbing` for `cube 3`, `cube 2`
(`rfl`). On `Q = Feec.Models.Cube.Geometry.Q`, the cube of `Feec`, the generators of the energy
space (triples `(E, C, β)` almost everywhere equal to `(Φ, curl Φ, Φ_τ)` for a `C¹` field `Φ`) are
the triples `C1Field.triple` of `Feec.Models.Cube.Absorbing` (`image_generators`), so the energy
spaces correspond (`mem_energySpaceOn_iff`), and the relation is the graph of `Feec`'s impedance
operator `Feec.Models.Cube.Absorbing.absorbing` (`absorbingOn_eq`). That operator is
m-dissipative (`isMDissipative_absorbing`), radiates (`exists_inner_absorbing_neg`), and its
semigroup does not keep `L²(TSD) × L²(TSD)` (`not_invariant_tsdPair`); every evolution of the
relation is its semigroup (`eq_semigroup_of_isEvolution`).

## References

* [P. Monk, *Finite Element Methods for Maxwell's Equations*][Monk2003], §1.4, §4.6

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set MeasureTheory Filter Topology

@[expose] public noncomputable section

namespace FEEC

open Feec Feec.Domain Feec.Models.BoundedDomain
open Feec.Models.Cube.Geometry (Q)
open Feec.Models.Cube.Absorbing (MQ State Amb Bdry BIx C1Field EnergySpace fieldMap curlMap
  traceMap impedanceTriple isMDissipative_absorbing absorbingSemigroup)

/-! ### The problem on any pair of sets -/

section On

variable (Ω₃ : Set (Fin 3 → ℝ)) (Ω₂ : Set (Fin 2 → ℝ))

/-- The energy space of the challenge, on `Ω₃` with boundary data on `Ω₂`. -/
def energySpaceOn : Submodule ℝ (L2F ℝ Ω₃ Ix × L2F ℝ Ω₃ Ix × L2F ℝ Ω₂ BIx) :=
  (Submodule.span ℝ {v : L2F ℝ Ω₃ Ix × L2F ℝ Ω₃ Ix × L2F ℝ Ω₂ BIx |
    ∃ Φ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ, (∀ ij, ContDiff ℝ 1 (Φ ij)) ∧
    (∀ ij, ⇑(v.1 ij) =ᵐ[volume.restrict Ω₃] Φ ij) ∧
    (∀ ij, ⇑(v.2.1 ij) =ᵐ[volume.restrict Ω₃] curlMat Φ ij) ∧
    ∀ b, ⇑(v.2.2 b) =ᵐ[volume.restrict Ω₂] fun y =>
      Φ (b.2.1, b.1.1.succAbove b.2.2) (faceMap b.1 y)}).topologicalClosure

/-- The absorbing problem of the challenge, on `Ω₃` with boundary data on `Ω₂`. -/
def absorbingOn : SetRel (WithLp 2 (L2F ℝ Ω₃ Ix × L2F ℝ Ω₃ Ix))
    (WithLp 2 (L2F ℝ Ω₃ Ix × L2F ℝ Ω₃ Ix)) :=
  {p | ∃ v ∈ energySpaceOn Ω₃ Ω₂, v.1 = p.1.fst ∧ v.2.1 = p.2.snd ∧
    ∀ v' ∈ energySpaceOn Ω₃ Ω₂, ⟪p.2.fst, v'.1⟫_ℝ = -⟪p.1.snd, v'.2.1⟫_ℝ - ⟪v.2.2, v'.2.2⟫_ℝ}

/-- The TSD constraint of the challenge, on `Ω₃`. -/
def tsdPairOn : Set (WithLp 2 (L2F ℝ Ω₃ Ix × L2F ℝ Ω₃ Ix)) :=
  {x | IsTSD (fun a b => x.fst (a, b)) ∧ IsTSD (fun a b => x.snd (a, b))}

theorem absorbing_eq : absorbing = absorbingOn (cube 3) (cube 2) := rfl

theorem tsdPair_eq : tsdPair = tsdPairOn (cube 3) := rfl

end On

/-! ### On `Feec`'s cube -/

/-- The ambient space of the energy space as `Feec`'s nested `ℓ²` sums. -/
def amb : (MQ × MQ × Bdry) ≃L[ℝ] Amb :=
  (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ MQ)
    (WithLp.prodContinuousLinearEquiv 2 ℝ MQ Bdry).symm).trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ MQ (WithLp 2 (MQ × Bdry))).symm

theorem amb_apply (v : MQ × MQ × Bdry) :
    amb v = WithLp.toLp 2 (v.1, WithLp.toLp 2 (v.2.1, v.2.2)) := rfl

/-- The generators of the energy space of the challenge on `Q`. -/
def gens : Set (MQ × MQ × Bdry) :=
  {v | ∃ Φ : Fin 3 × Fin 3 → (Fin 3 → ℝ) → ℝ, (∀ ij, ContDiff ℝ 1 (Φ ij)) ∧
    (∀ ij, ⇑(v.1 ij) =ᵐ[volume.restrict (Q (Fin 3))] Φ ij) ∧
    (∀ ij, ⇑(v.2.1 ij) =ᵐ[volume.restrict (Q (Fin 3))] curlMat Φ ij) ∧
    ∀ b, ⇑(v.2.2 b) =ᵐ[volume.restrict (Q (Fin 2))] fun y =>
      Φ (b.2.1, b.1.1.succAbove b.2.2) (faceMap b.1 y)}

/-- **The generators of the energy space are `Feec`'s triples of `C¹` fields.** -/
theorem image_generators : amb '' gens = Set.range C1Field.triple := by
  ext w
  constructor
  · rintro ⟨v, ⟨Φ, hΦ, h1, h2, h3⟩, rfl⟩
    refine ⟨⟨Φ, hΦ⟩, ?_⟩
    rw [amb_apply]
    have e1 : C1Field.l2 ⟨Φ, hΦ⟩ = v.1 := PiLp.ext fun ij => Lp.ext
      ((memLp_of_continuous Feec.Models.Cube.Geometry.measurableSet_Q
        Feec.Models.Cube.Absorbing.isBounded_Q (hΦ ij).continuous).coeFn_toLp.trans (h1 ij).symm)
    have e2 : C1Field.curlL2 ⟨Φ, hΦ⟩ = v.2.1 := PiLp.ext fun ij => Lp.ext
      ((memLp_of_continuous Feec.Models.Cube.Geometry.measurableSet_Q
        Feec.Models.Cube.Absorbing.isBounded_Q
          (Feec.Models.Cube.Absorbing.continuous_curlM hΦ ij)).coeFn_toLp.trans (h2 ij).symm)
    have e3 : C1Field.tan ⟨Φ, hΦ⟩ = v.2.2 := PiLp.ext fun b => Lp.ext
      ((memLp_of_continuous Feec.Models.Cube.Geometry.measurableSet_Q
        Feec.Models.Cube.Absorbing.isBounded_Q
          (Feec.Models.Cube.Absorbing.continuous_tanFun (fun ij => (hΦ ij).continuous)
            b)).coeFn_toLp.trans (h3 b).symm)
    rw [C1Field.triple, e1, e2, e3]
  · rintro ⟨Φ, rfl⟩
    exact ⟨(C1Field.l2 Φ, C1Field.curlL2 Φ, C1Field.tan Φ), ⟨Φ.1, Φ.2,
      fun ij => (memLp_of_continuous Feec.Models.Cube.Geometry.measurableSet_Q
        Feec.Models.Cube.Absorbing.isBounded_Q (Φ.2 ij).continuous).coeFn_toLp,
      fun ij => (memLp_of_continuous Feec.Models.Cube.Geometry.measurableSet_Q
        Feec.Models.Cube.Absorbing.isBounded_Q
          (Feec.Models.Cube.Absorbing.continuous_curlM Φ.2 ij)).coeFn_toLp,
      fun b => (memLp_of_continuous Feec.Models.Cube.Geometry.measurableSet_Q
        Feec.Models.Cube.Absorbing.isBounded_Q
          (Feec.Models.Cube.Absorbing.continuous_tanFun (fun ij => (Φ.2 ij).continuous)
            b)).coeFn_toLp⟩, rfl⟩

/-- **The energy spaces correspond.** -/
theorem mem_energySpaceOn_iff (v : MQ × MQ × Bdry) :
    v ∈ energySpaceOn (Q (Fin 3)) (Q (Fin 2)) ↔
      amb v ∈ Feec.Models.Cube.Absorbing.energySpace := by
  have hspan : ⇑amb.toHomeomorph '' (Submodule.span ℝ gens : Set (MQ × MQ × Bdry)) =
      (Submodule.span ℝ (Set.range C1Field.triple) : Set Amb) := by
    rw [← image_generators]
    exact congrArg (fun S : Submodule ℝ Amb => (S : Set Amb))
      (Submodule.map_span (amb : (MQ × MQ × Bdry) →ₗ[ℝ] Amb) gens)
  have h1 : (energySpaceOn (Q (Fin 3)) (Q (Fin 2)) : Set (MQ × MQ × Bdry)) =
      closure (Submodule.span ℝ gens : Set (MQ × MQ × Bdry)) :=
    Submodule.topologicalClosure_coe _
  have h2 : (Feec.Models.Cube.Absorbing.energySpace : Set Amb) =
      closure (Submodule.span ℝ (Set.range C1Field.triple) : Set Amb) :=
    Submodule.topologicalClosure_coe _
  rw [← SetLike.mem_coe, h1, ← SetLike.mem_coe, h2, ← hspan,
    ← amb.toHomeomorph.image_closure]
  exact (amb.toHomeomorph.injective.mem_set_image).symm

/-- **The challenge's absorbing problem on `Q` is the graph of `Feec`'s absorbing generator.** -/
theorem absorbingOn_eq : absorbingOn (Q (Fin 3)) (Q (Fin 2)) =
    (Feec.Models.Cube.Absorbing.absorbing.graph : Set (State × State)) := by
  ext p
  rw [SetLike.mem_coe, Feec.Models.Cube.Absorbing.absorbing, ImpedanceTriple.mem_graph_op_iff]
  constructor
  · rintro ⟨v, hv, h1, h2, h3⟩
    refine ⟨⟨amb v, (mem_energySpaceOn_iff v).1 hv⟩, h1, h2, fun ⟨w', hw'⟩ => ?_⟩
    obtain ⟨v', rfl⟩ : ∃ v', amb v' = w' := ⟨amb.symm w', amb.apply_symm_apply w'⟩
    exact h3 v' ((mem_energySpaceOn_iff v').2 hw')
  · rintro ⟨⟨w, hw⟩, h1, h2, h3⟩
    obtain ⟨v, rfl⟩ : ∃ v, amb v = w := ⟨amb.symm w, amb.apply_symm_apply w⟩
    exact ⟨v, (mem_energySpaceOn_iff v).2 hw, h1, h2,
      fun v' hv' => h3 ⟨amb v', (mem_energySpaceOn_iff v').1 hv'⟩⟩

theorem tsdPairOn_iff (x : State) :
    x ∈ tsdPairOn (Q (Fin 3)) ↔ x ∈ Feec.Models.Cube.Absorbing.tsdPair := by
  change IsTSD _ ∧ IsTSD _ ↔ x.fst ∈ tsd (Q (Fin 3)) ∧ x.snd ∈ tsd (Q (Fin 3))
  rw [isTSD_iff, isTSD_iff]
  rfl

/-- **The absorbing verdict on `Feec`'s cube.** -/
theorem absorbing_of_eq {Ω₃ : Set (Fin 3 → ℝ)} {Ω₂ : Set (Fin 2 → ℝ)} (h₃ : Ω₃ = Q (Fin 3))
    (h₂ : Ω₂ = Q (Fin 2)) :
    (∃ A : WithLp 2 (L2F ℝ Ω₃ Ix × L2F ℝ Ω₃ Ix) →ₗ.[ℝ] WithLp 2 (L2F ℝ Ω₃ Ix × L2F ℝ Ω₃ Ix),
        (A.graph : SetRel _ _) = absorbingOn Ω₃ Ω₂ ∧ (∀ x : A.domain, ⟪A x, (x : _)⟫_ℝ ≤ 0) ∧
        ∀ y, ∃ x : A.domain, (x : _) - A x = y) ∧
      (∃ p ∈ absorbingOn Ω₃ Ω₂, ⟪p.2, p.1⟫_ℝ < 0) ∧
      ∀ S, IsEvolution ℝ (absorbingOn Ω₃ Ω₂) (Ici 0) S →
        ∃ t ≥ 0, ∃ x ∈ tsdPairOn Ω₃, S t x ∉ tsdPairOn Ω₃ := by
  subst h₃ h₂
  rw [absorbingOn_eq]
  have hA := isMDissipative_absorbing
  refine ⟨⟨Feec.Models.Cube.Absorbing.absorbing, rfl, fun x => by simpa using hA.dissipative x,
    fun y => by simpa using hA.surjective one_pos y⟩, ?_, fun S hS => ?_⟩
  · obtain ⟨u, hu⟩ := Feec.Models.Cube.Absorbing.exists_inner_absorbing_neg
    exact ⟨((u : State), Feec.Models.Cube.Absorbing.absorbing u),
      Feec.Models.Cube.Absorbing.absorbing.mem_graph u, hu⟩
  · have hgen : absorbingSemigroup.generator = Feec.Models.Cube.Absorbing.absorbing :=
      hA.generator_semigroup
    have hS' : IsEvolution ℝ absorbingSemigroup.generator.graph (Ici 0) S := by
      rw [hgen]; exact hS
    have hD : Dense (absorbingSemigroup.generator.domain : Set State) := by
      rw [hgen]; exact hA.dense_domain
    by_contra hcon
    push Not at hcon
    refine Feec.Models.Cube.Absorbing.not_invariant_tsdPair fun t ht x hx => ?_
    have h := hcon t ht x ((tsdPairOn_iff x).2 hx)
    rw [eq_semigroup_of_isEvolution absorbingSemigroup hD hS' ht] at h
    exact (tsdPairOn_iff _).1 h

end FEEC
