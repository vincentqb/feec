module

public import Feec.FiniteElement.WeakSymmetryMaps
public import Feec.FiniteElement.PolyElementMixed
public import Feec.Models.Cube.DeRhamIdentFEM
public import Feec.Models.Cube.WeakSymmetryWave

/-!
# The mirror finite element scheme for the BGG wave system (6.5) on the cube

The scheme (6.5) of [QuennevilleBelair2015], §6.3, with the boundary conditions of the mirror
parities of `Feec.Models.Cube.MirrorBGG` instead of those of Table 6.1. In the parity model `σ` is
even, `φ_a = ∂_a σ` and the rows `u_a` (`E_{ab} = ∂_a ∂_b σ`) are odd in the direction `a`, and
the top row carries the absolute (no boundary condition) class. On the level-`(N + 1)` Freudenthal
mesh of `Q = (0, ½)³` this gives the finite element spaces

* top row (no boundary condition): `P₁Λ⁰ → P₁⁻Λ¹ → P₁⁻Λ²`;
* bottom row, componentwise: `P₂Λ⁰_{Γₐ} → P₂⁻Λ¹_{Γₐ} → P₁Λ²_{Γₐ}` (`a = 1, 2, 3`), whose
  degrees of freedom vanish on the faces lying in `{x_a = 0}` or `{x_a = ½}` (`mirrorFaces a`,
  `Feec.FiniteElement.LocalElement.globalSpacePartial`);

connected by the canonical `S₀,ₕ = Π¹S⁰`, `S₁,ₕ = Π²S¹`
(`Feec.FiniteElement.PolySeq.wsGlobalPartial`), with the discrete anticommutation
`curl S₀,ₕ = −S₁,ₕ grad` from `d Π = Π d` (`algSegment`). Glued into `L²` this is a
`Feec.BGG.Segment` of finite-dimensional inner product spaces (`mirrorSegment`), so the corrected
Prop 6.2 of `Feec.HilbertComplex.BGG.TimeDependent` applies once its two finite element hypotheses
are checked: `S₀,ₕ` is onto (`mirror_S0_surjective`) and `grad` is injective on the bottom row
(`mirror_dt0_injective`).

## Main results

* `Feec.FiniteElement.PolySeq.wsGlobalPartial_surjective`: `Π' S` maps `∏ₐ Λ_{h,Γₐ}ᵏ` onto
  `P₁⁻Λ_hᵏ⁺¹` when the faces of `Γₐ` are flat in the direction `a`.
* `top_conforming_zero`, `top_conforming_one`, `bot_conforming_zero`, `bot_conforming_one`: the
  spaces lie in `HΛ(Q)` (componentwise) and the scheme's `d` is the weak exterior derivative.
* `mirror_S0_surjective`, `mirror_dt0_injective` (`grad u = 0` and vanishing DOFs on
  `{x_a = 0}` force `u = 0`: the gluing is a constant, `harmonic_zero_mesh`, with vanishing trace
  on a facet, `exists_facet_mirrorFaces`).
* **`mirror_exists_iff`**, **`mirror_exists_iff_compatible_u`**, **`mirror_exists_unique`**: the
  mirror scheme has a solution iff (C1)–(C3), for dynamic data iff (C2), and it is unique;
  `mirror_sqrt_energy_le`: energy stability.
* **`mirror_constantMode`**: the constant `1ₕ` is a nonzero element of `ker grad` on the top row
  (`σ` has no boundary condition); `⟪σₕ(t), 1ₕ⟫` is conserved by every solution
  (`Feec.BGG.DiscreteSolution.inner_σ_eq_of_d0_eq_zero`) and `σₕ ≡ 1ₕ` is a stationary solution
  (`Feec.BGG.DiscreteSolution.stationary`): the constant mode decouples, and well-posedness does
  not need `grad` injective on the top row.
* `mirror_nonvacuous`: the bottom row is nonzero, and for `f = 0` the energy is conserved
  (`Feec.BGG.DiscreteSolution.energy_eq`), so nonzero data give solutions nonzero at every time.

## Gaps (convergence to the TSD solution of `MirrorBGG.existsUnique_memQ`)

The abstract convergence theorem `Feec.BGG.Discrete.exists_discreteSolution_norm_sub_le_rate`
needs, for the mirror conditions, three pieces that are not built:

* **The continuous mirror BGG data in the forms model**: the rows `HΛ(Q)` and `∏ₐ H_{Γₐ}Λ(Q)`
  (`L²` de Rham complexes with boundary conditions on part of `∂Q`, here on the faces normal to
  `eₐ` in component `a`) as Hilbert complexes, and their identification with
  `Feec.Models.Cube.MirrorBGG.complexQ` (complex coefficients, matrix proxies, defined by
  parity extension to the torus). The library has `HΛ(Q)` and `H̊Λ(Q)` only;
  `Feec.Models.Cube.MirrorTrace` characterizes the domains of the grad–curl mirror complex (the
  bottom row, in matrix form) by Green's formulas against trace test functions, not the BGG
  complex with its second-order operator `grad grad`.
* **Conformity with the partial boundary conditions**: the bottom-row spaces are proved
  conforming in `HΛ(Q)³` (`bot_conforming_zero`, `bot_conforming_one`), with the conditions on
  `{x_a = 0, ½}` imposed through the degrees of freedom. Their membership in the mirror domains
  needs the Green's formulas of `MirrorTrace` for piecewise polynomial fields, i.e. elementwise
  integration by parts on `Q̄` with boundary terms against test functions that do not vanish on
  `∂Q`; the conformity results of `Feec.FiniteElement.Conformity` use test functions supported in
  `Ω` (maximal domain) or a dilation (minimal domain).
* **Smoothed projections with mixed boundary conditions**, commuting with `d` and uniformly
  bounded (`Feec.Models.Cube.PolySmoothingEstimates` covers the full and the fully homogeneous
  families only), to build a `Feec.BGG.Discrete` instance with (5.4) and the approximation
  estimates; and **`Feec.BGG.Stability` modulo the constant mode**: `poinc0` fails on the top row
  (`mirror_constantMode`), so the stability constants must be taken on the orthogonal complement
  of `1ₕ`, on which the mode decouples.

**Status.** The analysis is now carried out in `Feec.Models.Cube.MirrorWeakSymmetryComplex` and
`Feec.Models.Cube.MirrorWeakSymmetryConvergence`, in the forms model with the partial-boundary
complexes `HΛ_J(Q)` of `Feec.Models.Cube.DeRhamPartialIdent` and the parity-smoothed projections of
`Feec.Models.Cube.ParitySmoothingEstimates`. The pieces are: the continuous data
`mirrorBGGSegment`; `Feec.BGG.HarmonicStability` modulo the bottom harmonic forms in place of
`Stability` (`Feec.HilbertComplex.BGG.Harmonic`), with the top-row constant mode harmless; the
curl potential (Prop 5.3) with `C_R = 1`; and a `Feec.BGG.Discrete` instance `mirrorFEM` with (5.4),
Prop 5.9(1) and regular potentials. The resulting theorems are an `O(h)` rate for `C²` states up to
`∂Q` with the mirror tangential conditions (`mirrorWave_rate`, `mirrorWave_rate_tsd`) and
convergence without rate for energy-class solutions (`mirrorWave_converges`). The identification
with the Hodge wave solution of `MirrorBGG.existsUnique_memQ` is
`Feec.Models.Cube.MirrorWeakSymmetryTSD`: for TSD data in `D(L²)` the real part of the solution is
a classical solution of (6.2) (rows of `E`, `B` as forms, compared through Fourier coefficients of
the two parity models), and the scheme converges to it with `σₕ, Mₕ → 0` and `Bₕ` asymptotically
symmetric (`mirror_waveFEM`; `O(h)` under `C²` regularity, `mirror_waveFEM_rate`). The analysed
scheme couples the rows by the parity-smoothed `S₀,ₕ = π¹S⁰`, not by the canonical `S_h = Π¹S⁰` of
`mirrorSegment` above, and its spaces are `polyPartial`, not identified with the spaces here.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.2 (Prop 6.2), §6.3 ((6.5), Table 6.1)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §5 (assembly from degrees of freedom)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §4.3 (relative and absolute boundary conditions)
* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021] (BGG construction)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open MeasureTheory Set Finset
open scoped ContDiff

@[expose] public noncomputable section

namespace Feec.FiniteElement

open ExteriorFibre Feec.Mesh Feec.Domain

variable {n : ℕ}

namespace PolySeq

/-- `exists_dof_coordWedgeC_ne_zero` with the direction of the component: the component `a`
whose source DOF reaches the target DOF `ℓ'_{g,i}` is a coordinate along which `g` is not flat
(two vertices of `g` have different `a`-th coordinates). -/
theorem exists_dof_coordWedgeC_ne_zero_of_ne (S : PolySeq) {k : ℕ} (hS : S.ConstOneTest k)
    {g : Finset (Fin n → ℝ)} (i : lowestOrder.DofIdx g (k + 1)) :
    ∃ (a : Fin n) (j : S.DofIdx g k), (∃ x ∈ g, ∃ y ∈ g, x a ≠ y a) ∧
      ∀ v : Fin n → contForms n,
        (∀ a' j', S.dof g k j' (v a') = if a' = a ∧ j' = j then 1 else 0) →
          lowestOrder.dof g (k + 1) i (coordWedgeC v) ≠ 0 := by
  classical
  have hne : g.Nonempty := i.2
  have hg : #g = #g - 1 + 1 := by have := card_pos.2 hne; omega
  set q := lexEnum g (#g - 1)
  set b' := lowestOrder.testBasis (k + 1) (#g - 1)
  set η := (b' i.1 : FormField (#g - 1))
  have hη : η ∈ lowestOrder.test (k + 1) (#g - 1) := (b' i.1).2
  have hηc : Continuous η := lowestOrder.continuous_testBasis (k + 1) (#g - 1) i.1
  have hη0 : η ≠ 0 := fun h => b'.ne_zero i.1 (Subtype.ext h)
  obtain h0 | ⟨hm, c, hc⟩ := lowestOrder_test_succ hη
  · exact absurd h0 hη0
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hη0 (funext fun y => by rw [hc y, zero_smul]; rfl)
  have h01 : q ⟨1, by omega⟩ ≠ q 0 := fun h =>
    absurd ((strictMono_lexEnum hg).injective h) (by simp [Fin.ext_iff])
  obtain ⟨a, ha⟩ : ∃ a, simplexMatrix q a ⟨0, by omega⟩ ≠ 0 := by
    by_contra! hcon
    exact h01 (funext fun a => by
      have := hcon a
      simp only [simplexMatrix, Fin.succ_mk, sub_eq_zero] at this
      exact this)
  have hdir : ∃ x ∈ g, ∃ y ∈ g, x a ≠ y a := by
    refine ⟨q ⟨1, by omega⟩, lexEnum_mem hg _, q 0, lexEnum_mem hg _, fun h => ha ?_⟩
    simp only [simplexMatrix, Fin.succ_mk, h, sub_self]
  set ζ : Fin n → FormField (#g - 1) := fun a' y => wedge (simplexMatrix q a') (η y)
  have hζeq : ∀ a', ζ a' = c • fun _ => oneForm (simplexMatrix q a') := fun a' => by
    funext y; simp only [ζ]; rw [hc y, wedge_smul, Pi.smul_apply, oneForm]
  have hζ : ∀ a', ζ a' ∈ S.test k (#g - 1) := fun a' => by
    rw [hζeq]; exact Submodule.smul_mem _ c (hS _ hm _)
  set b := S.testBasis k (#g - 1)
  have hζ0 : (⟨ζ a, hζ a⟩ : S.test k (#g - 1)) ≠ 0 := by
    intro h
    have h1 : ζ a 0 {⟨0, by omega⟩} = 0 := by
      have := congrArg (fun z : S.test k (#g - 1) => (z : FormField (#g - 1)) 0 {⟨0, by omega⟩}) h
      simpa using this
    rw [hζeq] at h1
    simp only [Pi.smul_apply, oneForm_singleton, smul_eq_mul] at h1
    exact mul_ne_zero hc0 ha h1
  obtain ⟨j, hj⟩ : ∃ j, b.repr ⟨ζ a, hζ a⟩ j ≠ 0 := by
    by_contra! hcon
    exact hζ0 (b.repr.injective (Finsupp.ext fun j => by simp [hcon j]))
  refine ⟨a, ⟨j, hne⟩, hdir, fun v hv => ?_⟩
  have key : lowestOrder.dof g (k + 1) i (coordWedgeC v) =
      (-1 : ℝ) ^ k * ∑ a', vertexMoment q (ζ a') (degField k (v a')) := by
    rw [dof_apply, coe_coordWedgeC]
    exact vertexMoment_degField_coordWedgeField q hηc k fun a' => (v a').2
  have hexp : ∀ a', vertexMoment q (ζ a') (degField k (v a')) =
      ∑ l, b.repr ⟨ζ a', hζ a'⟩ l * S.dof g k ⟨l, hne⟩ (v a') := fun a' => by
    have e : ζ a' = ∑ l, b.repr ⟨ζ a', hζ a'⟩ l • (b l : FormField (#g - 1)) := by
      have := congrArg (Subtype.val : S.test k (#g - 1) → FormField (#g - 1))
        (b.sum_repr ⟨ζ a', hζ a'⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    conv_lhs => rw [e]
    rw [vertexMoment_sum_smul_right q _ _ (fun l => S.continuous_testBasis k _ l)
      (continuous_degField k (v a').2)]
    rfl
  rw [key]
  simp only [hexp, hv, Subtype.mk.injEq, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single a (fun a' _ ha' => by simp [ha']) (by simp)]
  simp only [true_and, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hj


section Partial

variable (S : PolySeq) {M : SimplicialMesh n} {k : ℕ}

/-- **`S_h = Π' S` on fields with componentwise boundary conditions**: the restriction of
`PolySeq.wsGlobal` to `∏ₐ Λ_{h,Γₐ}ᵏ` (component `a` with vanishing DOFs on the faces of `Γₐ`),
into the full space `P₁⁻Λ_hᵏ⁺¹`. -/
def wsGlobalPartial (hS : S.ConstOneTest k) (Γ : Fin n → Set (Finset (Fin n → ℝ))) :
    (∀ a, (polyElement n S).globalSpacePartial M (Γ a) k) →ₗ[ℝ]
      (polyElement n lowestOrder).globalSpace M (k + 1) :=
  S.wsGlobal hS ∘ₗ LinearMap.pi fun a =>
    Submodule.inclusion ((polyElement n S).globalSpacePartial_le M (Γ a) k) ∘ₗ LinearMap.proj a

@[simp] theorem coe_wsGlobalPartial (hS : S.ConstOneTest k) (Γ : Fin n → Set (Finset (Fin n → ℝ)))
    (u : ∀ a, (polyElement n S).globalSpacePartial M (Γ a) k) :
    (S.wsGlobalPartial hS Γ u : (polyElement n lowestOrder).Piecewise M (k + 1)) =
      S.wsPiecewise M k fun a => ((u a : (polyElement n S).globalSpacePartial M (Γ a) k) :
        (polyElement n S).Piecewise M k) := rfl

variable {S}

/-- **`S_h = Π' S` maps `∏ₐ Λ_{h,Γₐ}ᵏ` onto `P₁⁻Λ_hᵏ⁺¹`** when every face of `Γₐ` is flat in the
direction `a` (all its vertices have the same `a`-th coordinate), for a source family whose test
forms on `(k+1)`-faces contain the constant `1`-forms. Each target DOF on a face `g` is reached
from a source DOF of `g` in a component `a` along which `g` is not flat
(`exists_dof_coordWedgeC_ne_zero_of_ne`), and such a source DOF is free. This is the boundary
condition pattern of the mirror parities (component `a` odd in the direction `a`). -/
theorem wsGlobalPartial_surjective (hS : S.ConstOneTest k) {Γ : Fin n → Set (Finset (Fin n → ℝ))}
    (hΓ : ∀ a, ∀ F ∈ Γ a, ∀ x ∈ F, ∀ y ∈ F, x a = y a) :
    Function.Surjective (S.wsGlobalPartial (M := M) hS Γ) := by
  classical
  set Φ := ((polyElement n lowestOrder).globalDofEquiv M (k + 1)).toLinearMap ∘ₗ
    S.wsGlobalPartial (M := M) hS Γ
  suffices hΦ : Function.Surjective Φ by
    intro u
    obtain ⟨x, hx⟩ := hΦ ((polyElement n lowestOrder).globalDofEquiv M (k + 1) u)
    exact ⟨x, ((polyElement n lowestOrder).globalDofEquiv M (k + 1)).injective hx⟩
  have hit : ∀ p : (polyElement n lowestOrder).GlobalDofIdx M (k + 1),
      ∃ x, Φ x = (Φ x p) • Pi.single p 1 ∧ Φ x p ≠ 0 := by
    intro p
    obtain ⟨g, i⟩ := p
    obtain ⟨a, j, ⟨y₁, hy₁, y₂, hy₂, hy⟩, hval⟩ := S.exists_dof_coordWedgeC_ne_zero_of_ne hS i
    set p' : (polyElement n S).GlobalDofIdx M k := ⟨g, j⟩
    set c : (polyElement n S).GlobalDofIdx M k → ℝ := Pi.single p' 1
    have hc0 : ∀ q : (polyElement n S).GlobalDofIdx M k,
        (polyElement n S).IsDofOn M (Γ a) q → c q = 0 := by
      intro q hq
      have : q ≠ p' := by
        rintro rfl
        obtain ⟨F, hF, hgF⟩ := hq
        exact hy (hΓ a F hF y₁ (hgF hy₁) y₂ (hgF hy₂))
      simp [c, this]
    have hmem : (polyElement n S).ofGlobalDof M k c ∈
        (polyElement n S).globalSpacePartial M (Γ a) k :=
      ((polyElement n S).mem_globalSpacePartial_iff M (Γ a)
        ⟨_, (polyElement n S).ofGlobalDof_mem M k c⟩).2 fun q hq => by
        have : (polyElement n S).globalDof M k ⟨_, (polyElement n S).ofGlobalDof_mem M k c⟩ q =
            c q := by
          rw [(polyElement n S).globalDof_apply M k _ q (LocalElement.faceSimplex M q.1)
            (LocalElement.subset_faceSimplex M q.1)]
          exact (polyElement n S).localDof_ofGlobalDof M k c _ _
            (LocalElement.subset_faceSimplex M q.1) _
        rw [this, hc0 q hq]
    set x : ∀ a', (polyElement n S).globalSpacePartial M (Γ a') k := Pi.single a ⟨_, hmem⟩
    have hxdof : ∀ (T : M.simplices) (g' : Finset (Fin n → ℝ))
        (hg' : g' ⊆ vertexSet (T : Affine.Simplex ℝ (Fin n → ℝ) n)) (a' : Fin n)
        (j' : S.DofIdx g' k),
        S.dof g' k j' (S.toCont k (((x a' : (polyElement n S).globalSpacePartial M (Γ a') k) :
          (polyElement n S).Piecewise M k) T)) =
          if a' = a then c ⟨⟨g', (LocalElement.mem_meshFaces M).2 ⟨T, T.2, hg'⟩⟩, j'⟩ else 0 := by
      intro T g' hg' a' j'
      by_cases ha' : a' = a
      · subst ha'
        simp only [x, Pi.single_eq_same, ↓reduceIte]
        exact (polyElement n S).localDof_ofGlobalDof M k c T g' hg' j'
      · simp only [x, Pi.single_eq_of_ne ha', ha', ↓reduceIte, ZeroMemClass.coe_zero,
          Pi.zero_apply]
        exact map_zero _
    refine ⟨x, funext fun p'' => ?_, ?_⟩
    · obtain ⟨g'', i''⟩ := p''
      by_cases hgg : g'' = g
      · subst hgg
        obtain rfl : i'' = i := (lowestOrder_dofIdx_subsingleton _ k).elim _ _
        simp
      · rw [Pi.smul_apply, Pi.single_eq_of_ne (by
          intro h; apply hgg; have := congrArg (fun q => q.1) h; exact this), smul_zero]
        change (polyElement n lowestOrder).localDof (LocalElement.faceSimplex M g'') (k + 1) g''
          i'' (S.wsPiecewise M k (fun a => ((x a : (polyElement n S).globalSpacePartial M (Γ a) k) :
            (polyElement n S).Piecewise M k)) (LocalElement.faceSimplex M g'')) = 0
        rw [localDof_wsPiecewise _ _ _ _ _ (LocalElement.subset_faceSimplex M g'')]
        refine (S.dof_coordWedgeC_eq hS i'' (w := 0) fun a' j' => ?_).trans (by
          rw [map_zero, map_zero])
        rw [hxdof _ _ (LocalElement.subset_faceSimplex M g''), Pi.zero_apply, map_zero]
        split_ifs
        · simp only [c, Pi.single_apply]
          split_ifs with h
          · exact absurd (Subtype.ext (congrArg Subtype.val (congrArg Sigma.fst h))) hgg
          · rfl
        · rfl
    · change (polyElement n lowestOrder).localDof (LocalElement.faceSimplex M g) (k + 1) g i
          (S.wsPiecewise M k (fun a => ((x a : (polyElement n S).globalSpacePartial M (Γ a) k) :
            (polyElement n S).Piecewise M k)) (LocalElement.faceSimplex M g)) ≠ 0
      rw [localDof_wsPiecewise _ _ _ _ _ (LocalElement.subset_faceSimplex M g)]
      refine hval _ fun a' j' => ?_
      rw [hxdof _ _ (LocalElement.subset_faceSimplex M g)]
      by_cases ha' : a' = a
      · simp only [ha', ↓reduceIte, true_and, c, Pi.single_apply]
        congr 1
        exact propext ⟨fun h => eq_of_heq (Sigma.mk.inj_iff.1 h).2, fun h => by subst h; rfl⟩
      · simp [ha']
  intro y
  have hy : y = ∑ p, y p • Pi.single p (1 : ℝ) := by
    funext p; simp [Finset.sum_apply, Pi.single_apply]
  choose x hx hx0 using hit
  refine ⟨∑ p, (y p / Φ (x p) p) • x p, ?_⟩
  rw [map_sum]
  conv_rhs => rw [hy]
  refine Finset.sum_congr rfl fun p _ => ?_
  have e := hx p
  rw [map_smul, e, smul_smul]
  congr 1
  rw [← e]
  exact div_mul_cancel₀ _ (hx0 p)

end Partial

end PolySeq

end Feec.FiniteElement

namespace Feec.FiniteElement.PolySeq

open Feec.Mesh

variable {n : ℕ}

/-- `d ∘ d = 0` on piecewise polynomial fields. -/
theorem dPiecewise_dPiecewise (S : PolySeq) (M : SimplicialMesh n) (k : ℕ)
    (u : (polyElement n S).Piecewise M k) :
    (polyElement n S).dPiecewise M (k + 1) ((polyElement n S).dPiecewise M k u) = 0 :=
  funext fun T => Subtype.ext (by
    simp only [LocalElement.dPiecewise_apply, LocalElement.coe_localD]
    exact extDeriv_extDeriv ((PolyKind.contDiff_of_mem_space (u T).2).of_le (by simp)))

end Feec.FiniteElement.PolySeq

namespace Feec.BGG.Segment

variable {R : Type*} [Ring R] {V0 V1 V2 Vt0 Vt1 Vt2 W0 W1 W2 Wt0 Wt1 Wt2 : Type*}
  [AddCommGroup V0] [Module R V0] [AddCommGroup V1] [Module R V1]
  [AddCommGroup V2] [Module R V2] [AddCommGroup Vt0] [Module R Vt0]
  [AddCommGroup Vt1] [Module R Vt1] [AddCommGroup Vt2] [Module R Vt2]
  [AddCommGroup W0] [Module R W0] [AddCommGroup W1] [Module R W1]
  [AddCommGroup W2] [Module R W2] [AddCommGroup Wt0] [Module R Wt0]
  [AddCommGroup Wt1] [Module R Wt1] [AddCommGroup Wt2] [Module R Wt2]

/-- **Transport of BGG data along linear isomorphisms** of the six spaces. -/
def congr (D : Segment R V0 V1 V2 Vt0 Vt1 Vt2) (e0 : V0 ≃ₗ[R] W0) (e1 : V1 ≃ₗ[R] W1)
    (e2 : V2 ≃ₗ[R] W2) (f0 : Vt0 ≃ₗ[R] Wt0) (f1 : Vt1 ≃ₗ[R] Wt1) (f2 : Vt2 ≃ₗ[R] Wt2) :
    Segment R W0 W1 W2 Wt0 Wt1 Wt2 where
  d0 := e1.toLinearMap ∘ₗ D.d0 ∘ₗ e0.symm.toLinearMap
  d1 := e2.toLinearMap ∘ₗ D.d1 ∘ₗ e1.symm.toLinearMap
  dt0 := f1.toLinearMap ∘ₗ D.dt0 ∘ₗ f0.symm.toLinearMap
  dt1 := f2.toLinearMap ∘ₗ D.dt1 ∘ₗ f1.symm.toLinearMap
  S0 := e1.toLinearMap ∘ₗ D.S0 ∘ₗ f0.symm.toLinearMap
  S1 := e2.toLinearMap ∘ₗ D.S1 ∘ₗ f1.symm.toLinearMap
  d1_d0 σ := by simp [D.d1_d0]
  dt1_dt0 φ := by simp [D.dt1_dt0]
  anticomm φ := by simp [D.anticomm]

end Feec.BGG.Segment

namespace Feec.Models.Cube.MirrorWeakSymmetry

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.Models.Cube.FEM

/-- **The mirror faces normal to `e_a`**: the vertex sets lying in one of the two faces
`{x_a = 0}`, `{x_a = ½}` of `Q̄ = [0, ½]³`. The component `a` of the vector-valued (bottom row)
fields is odd in the direction `a` (`Feec.Models.Cube.MirrorBGG`: `φ_a = ∂_a σ`,
`E_{ab} = ∂_a ∂_b σ`), so its degrees of freedom vanish on these faces. -/
def mirrorFaces (a : Fin 3) : Set (Finset (Fin 3 → ℝ)) :=
  {F | (∀ v ∈ F, v a = 0) ∨ ∀ v ∈ F, v a = 1 / 2}

theorem mirrorFaces_flat (a : Fin 3) : ∀ F ∈ mirrorFaces a, ∀ x ∈ F, ∀ y ∈ F, x a = y a := by
  rintro F (h | h) x hx y hy <;> rw [h x hx, h y hy]

/-- The scalar element family of the top row (`P₁Λ⁰ → P₁⁻Λ¹ → P₁⁻Λ²`). -/
abbrev Etop : LocalElement 3 := polyElement 3 PolySeq.lowestOrder

/-- The element family of each component of the bottom row (`P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ²`). -/
abbrev Ebot : LocalElement 3 := polyElement 3 PolySeq.lagrangeP2

variable (N : ℕ)

/-! ### The algebraic mirror segment -/

/-- The bottom-row algebraic spaces `∏ₐ Λ_{h,Γₐ}ᵏ`, `Γₐ = mirrorFaces a`. -/
abbrev BotAlg (k : ℕ) : Type := ∀ a : Fin 3, Ebot.globalSpacePartial (mesh 3 N) (mirrorFaces a) k

/-- The componentwise exterior derivative on the bottom row. -/
def dBot (k : ℕ) : BotAlg N k →ₗ[ℝ] BotAlg N (k + 1) :=
  LinearMap.pi fun a => Ebot.dGlobalPartial (mesh 3 N) (mirrorFaces a) k ∘ₗ LinearMap.proj a

/-- **The mirror discrete BGG data on the global finite element spaces** (before gluing):
top row `P₁Λ⁰ → P₁⁻Λ¹ → P₁⁻Λ²` with no boundary condition, bottom row
`∏ₐ P₂Λ⁰_{Γₐ} → ∏ₐ P₂⁻Λ¹_{Γₐ} → ∏ₐ P₁Λ²_{Γₐ}`, connected by the canonical
`S₀,ₕ = Π¹S⁰`, `S₁,ₕ = Π²S¹` (`PolySeq.wsGlobalPartial`). -/
def algSegment : Feec.BGG.Segment ℝ (Etop.globalSpace (mesh 3 N) 0) (Etop.globalSpace (mesh 3 N) 1)
    (Etop.globalSpace (mesh 3 N) 2) (BotAlg N 0) (BotAlg N 1) (BotAlg N 2) where
  d0 := Etop.dGlobal (mesh 3 N) 0
  d1 := Etop.dGlobal (mesh 3 N) 1
  dt0 := dBot N 0
  dt1 := dBot N 1
  S0 := PolySeq.lagrangeP2.wsGlobalPartial PolySeq.lagrangeP2_constOneTest_zero mirrorFaces
  S1 := PolySeq.lagrangeP2.wsGlobalPartial PolySeq.lagrangeP2_constOneTest_one mirrorFaces
  d1_d0 _ := Subtype.ext (PolySeq.dPiecewise_dPiecewise _ _ 0 _)
  dt1_dt0 _ := funext fun _ => Subtype.ext (PolySeq.dPiecewise_dPiecewise _ _ 0 _)
  anticomm _ := Subtype.ext (PolySeq.dPiecewise_wsPiecewise _)


/-! ### The glued (`L²`) spaces and the mirror segment -/

/-- The top-row spaces `Vₕᵏ ⊆ L²(Q; Λᵏ)` (no boundary condition). -/
abbrev Top (k : ℕ) : Type := Etop.V (mesh 3 N) (k : ℤ)

/-- The component spaces `V_{h,Γₐ}ᵏ ⊆ L²(Q; Λᵏ)` of the bottom row. -/
abbrev BotComp (a : Fin 3) (k : ℕ) : Type := Ebot.VPartial (mesh 3 N) (mirrorFaces a) (k : ℤ)

/-- The bottom-row spaces `∏ₐ V_{h,Γₐ}ᵏ ⊆ L²(Q; Λᵏ)³` (with the `ℓ²` sum inner product). -/
abbrev Bot (k : ℕ) : Type := PiLp 2 fun a : Fin 3 => BotComp N a k

instance (a : Fin 3) (k : ℕ) : FiniteDimensional ℝ (BotComp N a k) :=
  Submodule.finiteDimensional_of_le (Ebot.VPartial_le_V (mesh 3 N) (mirrorFaces a) (k : ℤ))

instance (k : ℕ) : FiniteDimensional ℝ (Bot N k) :=
  LinearEquiv.finiteDimensional (WithLp.linearEquiv 2 ℝ (∀ a : Fin 3, BotComp N a k)).symm

/-- Gluing `Λ_hᵏ ≃ Vₕᵏ` on the top row. -/
def topEquiv (k : ℕ) : Etop.globalSpace (mesh 3 N) k ≃ₗ[ℝ] Top N k :=
  LinearEquiv.ofInjective (Etop.glue (mesh 3 N) (k : ℤ) ∘ₗ (Etop.globalSpace (mesh 3 N) k).subtype)
    ((Etop.glue_injective _ (isOpen_mesh_domain 3 N) k).comp Subtype.val_injective)

/-- Gluing `Λ_{h,Γₐ}ᵏ ≃ V_{h,Γₐ}ᵏ` on a component of the bottom row. -/
def botCompEquiv (a : Fin 3) (k : ℕ) :
    Ebot.globalSpacePartial (mesh 3 N) (mirrorFaces a) k ≃ₗ[ℝ] BotComp N a k :=
  LinearEquiv.ofInjective
    (Ebot.glue (mesh 3 N) (k : ℤ) ∘ₗ (Ebot.globalSpacePartial (mesh 3 N) (mirrorFaces a) k).subtype)
    ((Ebot.glue_injective _ (isOpen_mesh_domain 3 N) k).comp Subtype.val_injective)

/-- Gluing on the bottom row. -/
def botEquiv (k : ℕ) : BotAlg N k ≃ₗ[ℝ] Bot N k :=
  (LinearEquiv.piCongrRight fun a => botCompEquiv N a k).trans
    (WithLp.linearEquiv 2 ℝ (∀ a : Fin 3, BotComp N a k)).symm

@[simp] theorem coe_topEquiv (k : ℕ) (u : Etop.globalSpace (mesh 3 N) k) :
    (topEquiv N k u : L2F ℝ (mesh 3 N).domain (formIdx 3 k)) =
      Etop.glue (mesh 3 N) (k : ℤ) (u : Etop.Piecewise (mesh 3 N) k) := rfl

@[simp] theorem coe_botEquiv_apply (k : ℕ) (u : BotAlg N k) (a : Fin 3) :
    (botEquiv N k u a : L2F ℝ (mesh 3 N).domain (formIdx 3 k)) =
      Ebot.glue (mesh 3 N) (k : ℤ) (u a : Ebot.Piecewise (mesh 3 N) k) := rfl

/-- **The mirror semi-discrete BGG data (Table 6.1 with the mirror parities)** on the
level-`(N + 1)` Freudenthal mesh of `Q = (0, ½)³`, as a `Feec.BGG.Segment` of finite-dimensional
`L²` spaces: `P₁Λ⁰ → P₁⁻Λ¹ → P₁⁻Λ²` without boundary condition and
`∏ₐ P₂Λ⁰_{Γₐ} → ∏ₐ P₂⁻Λ¹_{Γₐ} → ∏ₐ P₁Λ²_{Γₐ}`, component `a` with vanishing degrees of freedom on
the faces `{x_a = 0}`, `{x_a = ½}` (`mirrorFaces a`), linked by the canonical `S₀,ₕ = Π¹S⁰`,
`S₁,ₕ = Π²S¹`, with the discrete anticommutation `curl S₀,ₕ = −S₁,ₕ grad`. -/
def mirrorSegment :
    Feec.BGG.Segment ℝ (Top N 0) (Top N 1) (Top N 2) (Bot N 0) (Bot N 1) (Bot N 2) :=
  (algSegment N).congr (topEquiv N 0) (topEquiv N 1) (topEquiv N 2) (botEquiv N 0) (botEquiv N 1)
    (botEquiv N 2)


theorem mirrorSegment_S0_apply (φ : Bot N 0) :
    (mirrorSegment N).S0 φ = topEquiv N 1 (PolySeq.lagrangeP2.wsGlobalPartial
      PolySeq.lagrangeP2_constOneTest_zero mirrorFaces ((botEquiv N 0).symm φ)) := rfl

theorem mirrorSegment_dt0_apply (φ : Bot N 0) :
    (mirrorSegment N).dt0 φ = botEquiv N 1 (dBot N 0 ((botEquiv N 0).symm φ)) := rfl

/-! ### Conformity in `HΛ(Q)` -/

/-- **Conformity of the top row**: `Vₕ⁰ ⊆ H¹(Q)`, `Vₕ¹ ⊆ H(curl, Q)` (no boundary condition) and
`d₀ = grad`, `d₁ = curl` of the scheme are the weak exterior derivatives `d_max`. -/
theorem top_conforming_zero (σ : Top N 0) :
    ∃ h : (σ : L2F ℝ (mesh 3 N).domain (formIdx 3 0)) ∈
        ((extDerivOp ℝ 3 0).maximal (mesh 3 N).domain).domain,
      (extDerivOp ℝ 3 0).maximal (mesh 3 N).domain ⟨_, h⟩ =
        ((mirrorSegment N).d0 σ : L2F ℝ (mesh 3 N).domain (formIdx 3 1)) := by
  obtain ⟨h, e⟩ := Etop.glue_mem_maximal (mesh 3 N) (isOpen_mesh_domain 3 N) 0
    ((topEquiv N 0).symm σ)
  have hσ : (σ : L2F ℝ (mesh 3 N).domain (formIdx 3 0)) =
      Etop.glue (mesh 3 N) ((0 : ℕ) : ℤ) (((topEquiv N 0).symm σ : Etop.globalSpace _ 0) :
        Etop.Piecewise (mesh 3 N) 0) := by
    conv_lhs => rw [← (topEquiv N 0).apply_symm_apply σ]
    rfl
  rw [hσ]
  exact ⟨h, e⟩

theorem top_conforming_one (μ : Top N 1) :
    ∃ h : (μ : L2F ℝ (mesh 3 N).domain (formIdx 3 1)) ∈
        ((extDerivOp ℝ 3 1).maximal (mesh 3 N).domain).domain,
      (extDerivOp ℝ 3 1).maximal (mesh 3 N).domain ⟨_, h⟩ =
        ((mirrorSegment N).d1 μ : L2F ℝ (mesh 3 N).domain (formIdx 3 2)) := by
  obtain ⟨h, e⟩ := Etop.glue_mem_maximal (mesh 3 N) (isOpen_mesh_domain 3 N) 1
    ((topEquiv N 1).symm μ)
  have hμ : (μ : L2F ℝ (mesh 3 N).domain (formIdx 3 1)) =
      Etop.glue (mesh 3 N) ((1 : ℕ) : ℤ) (((topEquiv N 1).symm μ : Etop.globalSpace _ 1) :
        Etop.Piecewise (mesh 3 N) 1) := by
    conv_lhs => rw [← (topEquiv N 1).apply_symm_apply μ]
    rfl
  rw [hμ]
  exact ⟨h, e⟩

/-- **Conformity of the bottom row** (componentwise): `V_{h,Γₐ}⁰ ⊆ H¹(Q)`,
`V_{h,Γₐ}¹ ⊆ H(curl, Q)`, and `d̃₀ = grad`, `d̃₁ = curl` (row-wise) of the scheme are the weak
exterior derivatives. The boundary conditions on the faces `{x_a = 0, ½}` are imposed through the
degrees of freedom. -/
theorem bot_conforming_zero (φ : Bot N 0) (a : Fin 3) :
    ∃ h : (φ a : L2F ℝ (mesh 3 N).domain (formIdx 3 0)) ∈
        ((extDerivOp ℝ 3 0).maximal (mesh 3 N).domain).domain,
      (extDerivOp ℝ 3 0).maximal (mesh 3 N).domain ⟨_, h⟩ =
        ((mirrorSegment N).dt0 φ a : L2F ℝ (mesh 3 N).domain (formIdx 3 1)) := by
  set u := (botEquiv N 0).symm φ
  obtain ⟨h, e⟩ := Ebot.glue_mem_maximal (mesh 3 N) (isOpen_mesh_domain 3 N) 0
    ⟨u a, Ebot.globalSpacePartial_le (mesh 3 N) (mirrorFaces a) 0 (u a).2⟩
  have hφ : (φ a : L2F ℝ (mesh 3 N).domain (formIdx 3 0)) =
      Ebot.glue (mesh 3 N) ((0 : ℕ) : ℤ) ((u a : Ebot.globalSpacePartial _ _ 0) :
        Ebot.Piecewise (mesh 3 N) 0) := by
    conv_lhs => rw [← (botEquiv N 0).apply_symm_apply φ]
    rfl
  rw [hφ]
  exact ⟨h, e⟩

theorem bot_conforming_one (v : Bot N 1) (a : Fin 3) :
    ∃ h : (v a : L2F ℝ (mesh 3 N).domain (formIdx 3 1)) ∈
        ((extDerivOp ℝ 3 1).maximal (mesh 3 N).domain).domain,
      (extDerivOp ℝ 3 1).maximal (mesh 3 N).domain ⟨_, h⟩ =
        ((mirrorSegment N).dt1 v a : L2F ℝ (mesh 3 N).domain (formIdx 3 2)) := by
  set u := (botEquiv N 1).symm v
  obtain ⟨h, e⟩ := Ebot.glue_mem_maximal (mesh 3 N) (isOpen_mesh_domain 3 N) 1
    ⟨u a, Ebot.globalSpacePartial_le (mesh 3 N) (mirrorFaces a) 1 (u a).2⟩
  have hv : (v a : L2F ℝ (mesh 3 N).domain (formIdx 3 1)) =
      Ebot.glue (mesh 3 N) ((1 : ℕ) : ℤ) ((u a : Ebot.globalSpacePartial _ _ 1) :
        Ebot.Piecewise (mesh 3 N) 1) := by
    conv_lhs => rw [← (botEquiv N 1).apply_symm_apply v]
    rfl
  rw [hv]
  exact ⟨h, e⟩

/-! ### `S₀,ₕ` is onto -/

/-- **`S₀,ₕ = Π¹S⁰ : ∏ₐ P₂Λ⁰_{Γₐ} → P₁⁻Λ¹` is onto** (the hypothesis (5.4) of corrected
Prop 6.2 for the mirror scheme): the edge DOF `∫_e ψ · τ_e` is reached through a component `a`
with `τ_e · eₐ ≠ 0`, and an edge with `τ_e · eₐ ≠ 0` does not lie in a face `{x_a = c}`
(`PolySeq.wsGlobalPartial_surjective`). -/
theorem mirror_S0_surjective : Function.Surjective (mirrorSegment N).S0 := by
  intro μ
  obtain ⟨x, hx⟩ := PolySeq.wsGlobalPartial_surjective (M := mesh 3 N)
    PolySeq.lagrangeP2_constOneTest_zero mirrorFaces_flat ((topEquiv N 1).symm μ)
  refine ⟨botEquiv N 0 x, ?_⟩
  rw [mirrorSegment_S0_apply, LinearEquiv.symm_apply_apply, hx, LinearEquiv.apply_symm_apply]


/-! ### `grad` is injective on the bottom row -/

/-- **A facet of the mesh in the mirror face `{x_a = 0}`**: on the corner Freudenthal simplex
`h K_σ`, `σ = (a 2)`, the vertices `v₀ = 0, v₁, v₂` have `a`-th coordinate `0`. -/
theorem exists_facet_mirrorFaces (a : Fin 3) :
    ∃ T ∈ (mesh 3 N).simplices, ∃ F : Finset (Fin 3 → ℝ),
      F ⊆ vertexSet T ∧ #F = 3 ∧ F ∈ mirrorFaces a := by
  classical
  set σ : Equiv.Perm (Fin 3) := Equiv.swap a 2
  set T₀ := mapEquiv (boxMap 0 (1 / 2 / ((N + 1 : ℕ) : ℝ))
      (freudenthalScale_ne_zero (by norm_num : (0 : ℝ) < 1 / 2) (N + 1)))
    (freudenthalSimplex (finLattice (0 : Fin 3 → Fin (N + 1))) σ)
  have hT₀ : T₀ ∈ (mesh 3 N).simplices := mem_freudenthalMesh_simplices.2 ⟨0, σ, rfl⟩
  have hpts : ∀ j, T₀.points j = 0 + (1 / 2 / ((N + 1 : ℕ) : ℝ)) • kuhnVertex σ j := fun j => by
    have : latticePoint (finLattice (0 : Fin 3 → Fin (N + 1))) = 0 := by
      funext i; simp [finLattice]
    simp [T₀, this]
  refine ⟨T₀, hT₀, (univ.filter fun j : Fin 4 => j ≠ Fin.last 3).image T₀.points, ?_, ?_,
    Or.inl ?_⟩
  · intro x hx
    obtain ⟨j, -, rfl⟩ := mem_image.1 hx
    exact points_mem_vertexSet T₀ j
  · rw [card_image_of_injective _ T₀.independent.injective]; decide
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hx
    have hj3 : (j : ℕ) ≠ 3 := fun h => (mem_filter.1 hj).2 (Fin.ext h)
    have hσ : σ.symm a = 2 := by simp [σ]
    rw [hpts]
    simp only [zero_add, Pi.smul_apply, kuhnVertex, hσ, smul_eq_mul]
    have h2 : ((2 : Fin 3) : ℕ) = 2 := rfl
    rw [ite_eq_right_iff.2 (fun h => absurd h (by rw [h2]; have := j.isLt; omega)), mul_zero]

/-- `HΛ(Q)` on the mesh domain. -/
abbrev Hmesh : HilbertComplex ℝ (ComplexShape.up ℤ) fun k =>
    L2F ℝ (mesh 3 N).domain (formIdx 3 k) :=
  (deRham ℝ 3).maximalComplex (isOpen_mesh_domain 3 N)

/-- The harmonic `0`-forms of `HΛ(Q)` on the mesh domain are the constants. -/
theorem harmonic_zero_mesh (hb : Bornology.IsBounded (mesh 3 N).domain) :
    (Hmesh N).harmonic 0 =
      ℝ ∙ DeRhamIdent.constForm (isOpen_mesh_domain 3 N).measurableSet hb
        (⟨∅, by simp⟩ : formIdx 3 0) := by
  have key : ∀ (Ω : Set (Fin 3 → ℝ)) (_ : Ω = Geometry.Q (Fin 3)) (hΩ : IsOpen Ω)
      (hm : MeasurableSet Ω) (hb : Bornology.IsBounded Ω),
      ((deRham ℝ 3).maximalComplex hΩ).harmonic 0 =
        ℝ ∙ DeRhamIdent.constForm hm hb (⟨∅, by simp⟩ : formIdx 3 0) := by
    rintro Ω rfl hΩ hm hb
    exact DeRhamIdent.Hmax_harmonic_zero
  exact key _ ((mesh_domain 3 N).trans (cubeDomain_eq_Q 3)) _ _ _

/-- **`grad` is injective on `P₂Λ⁰_{Γₐ}`**: a field with vanishing DOFs on the faces
`{x_a = 0, ½}` and `grad u = 0` vanishes. Its gluing is a harmonic `0`-form of `HΛ(Q)`, hence a
constant `c` (`harmonic_zero_mesh`), and its trace on a facet in `{x_a = 0}`
(`exists_facet_mirrorFaces`) vanishes, so `c = 0`. -/
theorem eq_zero_of_dPiecewise_eq_zero (a : Fin 3)
    (u : Ebot.globalSpacePartial (mesh 3 N) (mirrorFaces a) 0)
    (hu : Ebot.dPiecewise (mesh 3 N) 0 (u : Ebot.Piecewise (mesh 3 N) 0) = 0) : u = 0 := by
  classical
  have hΩ := isOpen_mesh_domain 3 N
  have hb : Bornology.IsBounded (mesh 3 N).domain := (mesh_domain 3 N) ▸ isBounded_cubeDomain 3
  obtain ⟨h, e⟩ := Ebot.glue_mem_maximal (mesh 3 N) hΩ 0
    ⟨u, Ebot.globalSpacePartial_le (mesh 3 N) (mirrorFaces a) 0 u.2⟩
  have hd : (extDerivOp ℝ 3 0).maximal (mesh 3 N).domain ⟨_, h⟩ = 0 := by
    refine e.trans ?_
    change Ebot.glue (mesh 3 N) ((0 : ℤ) + 1) (Ebot.dPiecewise (mesh 3 N) 0
      (u : Ebot.Piecewise (mesh 3 N) 0)) = 0
    rw [hu, map_zero]
  have hharm : Ebot.glue (mesh 3 N) (0 : ℤ) (u : Ebot.Piecewise (mesh 3 N) 0) ∈
      (Hmesh N).harmonic 0 := by
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rw [(Hmesh N).cycles_eq (show (ComplexShape.up ℤ).Rel (0 : ℤ) (0 + 1) from rfl),
        deRham_maximalComplex_d hΩ 0]
      exact LinearPMap.mem_ker_iff.2 ⟨⟨_, h⟩, rfl, hd⟩
    · rw [HilbertComplex.mem_ker_adjoint_prev_iff (Hmesh N)
        (show (ComplexShape.up ℤ).Rel (-1 : ℤ) 0 from rfl)]
      have : Subsingleton (L2F ℝ (mesh 3 N).domain (formIdx 3 (-1))) :=
        DeRhamIdent.hlow _ (-1) (by norm_num)
      exact DeRhamIdent.mem_ker_adjoint_of_subsingleton _ _
  rw [harmonic_zero_mesh N hb] at hharm
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hharm
  obtain ⟨T, hT, F, hFT, hF3, hFa⟩ := exists_facet_mirrorFaces N a
  set uT : FormField 3 := ((u : Ebot.Piecewise (mesh 3 N) 0) ⟨T, hT⟩ : FormField 3) with huT_def
  have huT : uT ∈ Ebot.space T 0 := ((u : Ebot.Piecewise (mesh 3 N) 0) ⟨T, hT⟩).2
  set f : (Fin 3 → ℝ) → ℝ := fun x => uT x ∅
  have hfc : Continuous f := (continuous_apply ∅).comp (Ebot.contDiff_of_mem huT).continuous
  -- the trace of `u_T` on the facet `F ⊆ {x_a = 0}` vanishes
  have htr : ∀ x ∈ convexHull ℝ (F : Set (Fin 3 → ℝ)), f x = 0 := by
    intro x hx
    have key := Ebot.trace (T := T) (T' := T) (k := 0) (w := uT) (η := 0) hFT hFT hF3 huT
      (Submodule.zero_mem _) (fun g hg i => by
        have h0 := u.2.2 ⟨T, hT⟩ g (hg.trans hFT) ⟨F, hFa, hg⟩ i
        rw [LocalElement.localDof_apply] at h0
        refine h0.trans ?_
        exact (map_zero _).symm) x hx
    have h0 := key 0 (fun l => l.elim0)
    rw [ExteriorFibre.pullback_apply, ExteriorFibre.pullback_apply] at h0
    have hdeg := Ebot.isDeg_of_mem huT x
    rw [Finset.sum_eq_single ∅ (fun s _ hs => by
      rw [hdeg s (by simpa [Finset.card_eq_zero] using hs), zero_mul]) (by simp)] at h0
    simpa using h0
  -- `u_T = c` on `T`
  have hm := hΩ.measurableSet
  set s0 : formIdx 3 0 := ⟨∅, by simp⟩
  have h1 : ∀ᵐ x ∂volume.restrict (mesh 3 N).domain,
      ((Ebot.glue (mesh 3 N) (0 : ℤ) (u : Ebot.Piecewise (mesh 3 N) 0) s0 :
        Lp ℝ 2 (volume.restrict (mesh 3 N).domain)) : (Fin 3 → ℝ) → ℝ) x = c := by
    rw [← hc]
    filter_upwards [Lp.coeFn_smul c (DeRhamIdent.constForm hm hb s0 s0),
      MemLp.coeFn_toLp (DeRhamIdent.memLp_constFun hm hb s0 s0)] with x hx1 hx2
    rw [PiLp.smul_apply, hx1, Pi.smul_apply]
    change c • ((DeRhamIdent.memLp_constFun hm hb s0 s0).toLp _ : (Fin 3 → ℝ) → ℝ) x = c
    rw [hx2]
    simp [DeRhamIdent.constFun]
  have h2 := coeFn_pieceL2 (mesh 3 N) (mesh 3 N).domain
    (fun T => formComp (k := (0 : ℤ))
      (Ebot.extendPW (mesh 3 N) (u : Ebot.Piecewise (mesh 3 N) 0) T))
    (fun T hT s => continuous_formComp
      (Ebot.contDiff_extendPW (mesh 3 N) (u : Ebot.Piecewise (mesh 3 N) 0) hT).continuous s) s0
  set U := interior T.closedInterior ∩ (mesh 3 N).domain
  have hU : IsOpen U := isOpen_interior.inter hΩ
  have h3 : f =ᵐ[volume.restrict U] fun _ => c := by
    have hsub : U ⊆ (mesh 3 N).domain := inter_subset_right
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub h1,
      ae_restrict_of_ae_restrict_of_subset hsub h2, ae_restrict_mem hU.measurableSet]
      with x hx1 hx2 hxU
    rw [← hx1]
    refine (hx2.trans ?_).symm
    rw [pieceFun_of_mem_interior _ _ hT hxU.1]
    simp [formComp, Ebot.extendPW_of_mem _ _ hT, f, uT, s0]
  have h4 : EqOn f (fun _ => c) U :=
    Measure.eqOn_open_of_ae_eq h3 hU hfc.continuousOn continuousOn_const
  have h5 : ∀ x ∈ T.closedInterior, f x = c := by
    have hsub : T.closedInterior ⊆ closure U := by
      rw [← SimplicialMesh.closure_interior_closedInterior T]
      refine closure_minimal (fun x hx => isOpen_interior.inter_closure
        ⟨hx, (interior_subset.trans ((mesh 3 N).closedInterior_subset_closure hT)) hx⟩)
        isClosed_closure
    intro x hx
    exact closure_minimal h4 (isClosed_eq hfc continuous_const) (hsub hx)
  obtain ⟨v, hv⟩ : F.Nonempty := Finset.card_pos.1 (by omega)
  have hvc : v ∈ convexHull ℝ (F : Set (Fin 3 → ℝ)) := subset_convexHull ℝ _ (mem_coe.2 hv)
  have hvT : v ∈ T.closedInterior := by
    rw [← convexHull_vertexSet T]
    exact convexHull_mono (coe_subset.2 hFT) hvc
  have hc0 : c = 0 := by rw [← h5 v hvT, htr v hvc]
  rw [hc0, zero_smul] at hc
  refine Subtype.ext (Ebot.glue_injective (mesh 3 N) hΩ 0 ?_)
  exact hc.symm.trans (map_zero _).symm


/-- **`grad` is injective on the bottom row `∏ₐ P₂Λ⁰_{Γₐ}`** of the mirror scheme (the
hypothesis `hdinj` of corrected Prop 6.2). -/
theorem mirror_dt0_injective : Function.Injective (mirrorSegment N).dt0 := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hφ
  rw [mirrorSegment_dt0_apply, LinearEquiv.map_eq_zero_iff] at hφ
  have h0 : (botEquiv N 0).symm φ = 0 := funext fun a => by
    refine eq_zero_of_dPiecewise_eq_zero N a _ ?_
    have := congrArg (fun x : BotAlg N 1 => ((x a : Ebot.globalSpacePartial _ _ 1) :
      Ebot.Piecewise (mesh 3 N) 1)) hφ
    exact this
  rw [← (botEquiv N 0).apply_symm_apply φ, h0, LinearEquiv.map_zero]

/-! ### The constant mode -/

/-- The constant `0`-form `1` on every element. -/
def onePiecewise : Etop.Piecewise (mesh 3 N) 0 := fun _ =>
  ⟨fun _ => Pi.single ∅ 1, by
    show (fun _ => Pi.single ∅ 1) ∈ polySpace 3 1 0
    exact mem_polySpace_of_eq_const (fun _ => rfl) fun _ s hs =>
      Pi.single_eq_of_ne (fun h => hs (by rw [h]; rfl)) _⟩

theorem onePiecewise_mem : onePiecewise N ∈ Etop.globalSpace (mesh 3 N) 0 :=
  fun _ _ _ _ _ _ => rfl

/-- **The constant mode of `σ`**: the constant `1 ∈ P₁Λ⁰` (no boundary condition on the top row,
the even parity of `σ`) is a nonzero element of `ker grad`. The thesis' boundary conditions
(`P₁Λ̊⁰`) have no such mode. -/
def oneTop : Top N 0 := topEquiv N 0 ⟨onePiecewise N, onePiecewise_mem N⟩

theorem oneTop_ne_zero : oneTop N ≠ 0 := by
  obtain ⟨T, hT, -⟩ := exists_facet_mirrorFaces N 0
  rw [oneTop, Ne, LinearEquiv.map_eq_zero_iff]
  intro h
  have := congrArg (fun u : Etop.globalSpace (mesh 3 N) 0 =>
    ((u : Etop.Piecewise (mesh 3 N) 0) ⟨T, hT⟩ : FormField 3) 0 ∅) h
  simp [onePiecewise] at this

theorem d0_oneTop : (mirrorSegment N).d0 (oneTop N) = 0 := by
  change topEquiv N 1 (Etop.dGlobal (mesh 3 N) 0 ((topEquiv N 0).symm (oneTop N))) = 0
  rw [oneTop, LinearEquiv.symm_apply_apply, LinearEquiv.map_eq_zero_iff]
  refine Subtype.ext (funext fun T => Subtype.ext ?_)
  change extDeriv (fun _ => Pi.single ∅ 1) = (0 : FormField 3)
  exact extDeriv_const _

end Feec.Models.Cube.MirrorWeakSymmetry

namespace Feec.BGG

variable {P0 P1 P2 Pt0 Pt1 Pt2 : Type*}
  [NormedAddCommGroup P0] [InnerProductSpace ℝ P0]
  [NormedAddCommGroup P1] [InnerProductSpace ℝ P1]
  [NormedAddCommGroup P2] [InnerProductSpace ℝ P2]
  [NormedAddCommGroup Pt0] [InnerProductSpace ℝ Pt0]
  [NormedAddCommGroup Pt1] [InnerProductSpace ℝ Pt1]
  [NormedAddCommGroup Pt2] [InnerProductSpace ℝ Pt2]
  {D : Segment ℝ P0 P1 P2 Pt0 Pt1 Pt2}

open scoped RealInnerProductSpace

/-- **Harmonic modes of `σ` are conserved** by (6.3): for `τ ∈ ker d₀`, `⟪σₕ(t), τ⟫` is constant
on `[0,T]` (test (6.3a) with `(τ, 0)`). -/
theorem DiscreteSolution.inner_σ_eq_of_d0_eq_zero {T : ℝ} {f : ℝ → Pt1}
    (s : DiscreteSolution D T f) {τ : P0} (hτ : D.d0 τ = 0) :
    ∀ t ∈ Icc 0 T, ⟪s.σ t, τ⟫ = ⟪s.σ 0, τ⟫ := by
  refine constant_of_has_deriv_right_zero (s.cσ.inner continuousOn_const) fun t ht => ?_
  have hd := (s.dσ t ht).inner ℝ (hasDerivWithinAt_const t (Ici t) τ)
  have ha := s.ea t (Ico_subset_Icc_self ht) τ 0
  simp only [map_zero, inner_zero_right, sub_zero, hτ] at ha
  simp only [inner_zero_right, zero_add] at hd
  rw [show ⟪s.σ' t, τ⟫ = 0 by linarith] at hd
  exact hd

/-- **The stationary harmonic solutions of (6.3)**: for `σ₀ ∈ ker d₀` and `f = 0`,
`(σ, φ, u, M, ρ, λ) = (σ₀, 0, 0, 0, 0, 0)` solves (6.3). -/
def DiscreteSolution.stationary (T : ℝ) {σ₀ : P0} (hσ₀ : D.d0 σ₀ = 0) :
    DiscreteSolution D T (0 : ℝ → Pt1) where
  σ _ := σ₀
  φ _ := 0
  u _ := 0
  M _ := 0
  ρ _ := 0
  lam _ := 0
  σ' _ := 0
  u' _ := 0
  M' _ := 0
  ρ' _ := 0
  cσ := continuousOn_const
  cu := continuousOn_const
  cM := continuousOn_const
  cρ := continuousOn_const
  dσ _ _ := hasDerivWithinAt_const _ _ _
  du _ _ := hasDerivWithinAt_const _ _ _
  dM _ _ := hasDerivWithinAt_const _ _ _
  dρ _ _ := hasDerivWithinAt_const _ _ _
  ea _ _ τ ψ := by simp
  eb _ _ v := by simp
  ec _ _ N := by simp
  ed _ _ μ := by simp
  ee _ _ ζ := by simp [hσ₀]

end Feec.BGG

namespace Feec.BGG

variable {P0 P1 P2 Pt0 Pt1 Pt2 : Type*}
  [NormedAddCommGroup P0] [InnerProductSpace ℝ P0]
  [NormedAddCommGroup P1] [InnerProductSpace ℝ P1]
  [NormedAddCommGroup P2] [InnerProductSpace ℝ P2]
  [NormedAddCommGroup Pt0] [InnerProductSpace ℝ Pt0]
  [NormedAddCommGroup Pt1] [InnerProductSpace ℝ Pt1]
  [NormedAddCommGroup Pt2] [InnerProductSpace ℝ Pt2]
  {D : Segment ℝ P0 P1 P2 Pt0 Pt1 Pt2}

open scoped RealInnerProductSpace

/-- **Energy conservation** of (6.3) without source: `‖σₕ‖² + ‖uₕ‖² + ‖Mₕ‖² + ‖ρₕ‖²` is
constant on `[0,T]`. -/
theorem DiscreteSolution.energy_eq {T : ℝ} (s : DiscreteSolution D T (0 : ℝ → Pt1)) :
    ∀ t ∈ Icc 0 T, ‖s.σ t‖ ^ 2 + ‖s.u t‖ ^ 2 + ‖s.M t‖ ^ 2 + ‖s.ρ t‖ ^ 2 =
      ‖s.σ 0‖ ^ 2 + ‖s.u 0‖ ^ 2 + ‖s.M 0‖ ^ 2 + ‖s.ρ 0‖ ^ 2 := by
  refine constant_of_has_deriv_right_zero ((((s.cσ.norm.pow 2).add (s.cu.norm.pow 2)).add
    (s.cM.norm.pow 2)).add (s.cρ.norm.pow 2)) fun t ht => ?_
  simpa using s.hasDerivWithinAt_energy ht

end Feec.BGG

namespace Feec.Models.Cube.MirrorWeakSymmetry

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.Models.Cube.FEM
open scoped RealInnerProductSpace

variable (N : ℕ)

/-! ### Well-posedness of the mirror scheme (corrected Prop 6.2) -/

/-- **Corrected Prop 6.2 for the mirror scheme**: for `T > 0` and a source continuous on `[0,T]`,
(6.5) with the mirror spaces has a solution with data `(σ₀, φ₀, u₀, M₀, ρ₀)` iff (C1)
`grad σ₀ = S₀,ₕφ₀`, (C2) `u₀ ⊥ grad (ker S₀,ₕ)` and (C3) `(grad φ₀ − f(0), grad ψ) = 0` on
`ker S₀,ₕ`. -/
theorem mirror_exists_iff {T : ℝ} (hT0 : 0 < T) {f : ℝ → Bot N 1} (hf : ContinuousOn f (Icc 0 T))
    (σ₀ : Top N 0) (φ₀ : Bot N 0) (u₀ : Bot N 1) (M₀ : Top N 2) (ρ₀ : Bot N 2) :
    (∃ s : Feec.BGG.DiscreteSolution (mirrorSegment N) T f, s.σ 0 = σ₀ ∧ s.φ 0 = φ₀ ∧
      s.u 0 = u₀ ∧ s.M 0 = M₀ ∧ s.ρ 0 = ρ₀) ↔
      (mirrorSegment N).d0 σ₀ = (mirrorSegment N).S0 φ₀ ∧
        (∀ ψ, (mirrorSegment N).S0 ψ = 0 → ⟪u₀, (mirrorSegment N).dt0 ψ⟫ = 0) ∧
        (∀ ψ, (mirrorSegment N).S0 ψ = 0 →
          ⟪(mirrorSegment N).dt0 φ₀, (mirrorSegment N).dt0 ψ⟫ =
            ⟪f 0, (mirrorSegment N).dt0 ψ⟫) := by
  constructor
  · rintro ⟨s, rfl, rfl, rfl, -, -⟩
    exact Feec.BGG.DiscreteSolution.compatible hT0 s
  · rintro ⟨h1, h2, h3⟩
    exact Feec.BGG.exists_discreteSolution_of_continuousOn (mirror_dt0_injective N)
      (mirror_S0_surjective N) hT0.le hf h1 h2 h3

/-- **Corrected Prop 6.2 for the mirror scheme, dynamic data**: existence ⇔ (C2). -/
theorem mirror_exists_iff_compatible_u {T : ℝ} (hT0 : 0 < T) {f : ℝ → Bot N 1}
    (hf : ContinuousOn f (Icc 0 T)) (σ₀ : Top N 0) (u₀ : Bot N 1) (M₀ : Top N 2)
    (ρ₀ : Bot N 2) :
    (∃ s : Feec.BGG.DiscreteSolution (mirrorSegment N) T f, s.σ 0 = σ₀ ∧ s.u 0 = u₀ ∧
      s.M 0 = M₀ ∧ s.ρ 0 = ρ₀) ↔
      ∀ ψ, (mirrorSegment N).S0 ψ = 0 → ⟪u₀, (mirrorSegment N).dt0 ψ⟫ = 0 :=
  Feec.BGG.exists_discreteSolution_iff_compatible_u hT0 (mirror_dt0_injective N)
    (mirror_S0_surjective N) hf σ₀ u₀ M₀ ρ₀

/-- **Well-posedness of the mirror scheme** for dynamic data satisfying (C2): existence, the
forced `φₕ(0)`, and uniqueness (`σₕ, uₕ, Mₕ, ρₕ, λₕ` on `[0,T]`, `φₕ` on `[0,T)`). -/
theorem mirror_exists_unique {T : ℝ} (hT0 : 0 < T) {f : ℝ → Bot N 1}
    (hf : ContinuousOn f (Icc 0 T)) (σ₀ : Top N 0) (u₀ : Bot N 1) (M₀ : Top N 2)
    (ρ₀ : Bot N 2) (hC2 : ∀ ψ, (mirrorSegment N).S0 ψ = 0 → ⟪u₀, (mirrorSegment N).dt0 ψ⟫ = 0) :
    ∃ s : Feec.BGG.DiscreteSolution (mirrorSegment N) T f,
      (s.σ 0 = σ₀ ∧ s.u 0 = u₀ ∧ s.M 0 = M₀ ∧ s.ρ 0 = ρ₀) ∧
      s.φ 0 = Feec.BGG.phiMap (mirrorSegment N) (mirror_dt0_injective N) (mirror_S0_surjective N)
        (σ₀, f 0) ∧
      ∀ s' : Feec.BGG.DiscreteSolution (mirrorSegment N) T f,
        (s'.σ 0 = σ₀ ∧ s'.u 0 = u₀ ∧ s'.M 0 = M₀ ∧ s'.ρ 0 = ρ₀) →
          (∀ t ∈ Icc 0 T, s'.σ t = s.σ t ∧ s'.u t = s.u t ∧ s'.M t = s.M t ∧ s'.ρ t = s.ρ t ∧
            s'.lam t = s.lam t) ∧ (∀ t ∈ Ico 0 T, s'.φ t = s.φ t) :=
  Feec.BGG.exists_discreteSolution_unique hT0 (mirror_dt0_injective N) (mirror_S0_surjective N)
    hf σ₀ u₀ M₀ ρ₀ hC2

/-- **Energy stability of the mirror scheme**: `E(t)^{1/2} ≤ E(0)^{1/2} + ∫₀ᵗ ‖f‖`. -/
theorem mirror_sqrt_energy_le {T : ℝ} {f : ℝ → Bot N 1}
    (s : Feec.BGG.DiscreteSolution (mirrorSegment N) T f) (hf : ContinuousOn f (Icc 0 T)) :
    ∀ t ∈ Icc 0 T, √(‖s.σ t‖ ^ 2 + ‖s.u t‖ ^ 2 + ‖s.M t‖ ^ 2 + ‖s.ρ t‖ ^ 2) ≤
      √(‖s.σ 0‖ ^ 2 + ‖s.u 0‖ ^ 2 + ‖s.M 0‖ ^ 2 + ‖s.ρ 0‖ ^ 2) + ∫ r in (0:ℝ)..t, ‖f r‖ :=
  Feec.BGG.DiscreteSolution.sqrt_energy_le s hf

/-- **The constant mode of `σ` decouples**: the constant `1ₕ ∈ P₁Λ⁰` is a nonzero element of
`ker grad` (absent for the thesis' boundary conditions), its coefficient `⟪σₕ(t), 1ₕ⟫` is
conserved by every solution of the mirror scheme, and `σₕ ≡ 1ₕ` (all other fields `0`) is a
stationary solution. The well-posedness above does not need `grad` injective on the top row. -/
theorem mirror_constantMode :
    oneTop N ≠ 0 ∧ (mirrorSegment N).d0 (oneTop N) = 0 ∧
      (∀ (T : ℝ) (f : ℝ → Bot N 1) (s : Feec.BGG.DiscreteSolution (mirrorSegment N) T f),
        ∀ t ∈ Icc 0 T, ⟪s.σ t, oneTop N⟫ = ⟪s.σ 0, oneTop N⟫) ∧
      ∀ T : ℝ, ∃ s : Feec.BGG.DiscreteSolution (mirrorSegment N) T 0, ∀ t, s.σ t = oneTop N :=
  ⟨oneTop_ne_zero N, d0_oneTop N, fun _ _ s => s.inner_σ_eq_of_d0_eq_zero (d0_oneTop N),
    fun T => ⟨Feec.BGG.DiscreteSolution.stationary T (d0_oneTop N), fun _ => rfl⟩⟩

/-- `P₁⁻Λ¹ ≠ 0` on the top row. -/
theorem exists_top_one_ne_zero : ∃ μ : Top N 1, μ ≠ 0 := by
  have hpos : 0 < Module.finrank ℝ (Etop.V₀ (mesh 3 N) ((1 : ℕ) : ℤ)) :=
    PolySeq.lowestOrder.finrank_V₀_freudenthalMesh_pos_of_one_le (n := 3) (b := 0)
      (s := 1 / 2) (by norm_num) (N := N + 1) (k := 1) le_rfl (by norm_num)
  obtain ⟨x, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := Etop.V₀ (mesh 3 N) ((1 : ℕ) : ℤ))
    (fun h => by
    rw [h, finrank_bot] at hpos; exact lt_irrefl 0 hpos)
  obtain ⟨⟨u, hu⟩, rfl⟩ := hx.1
  exact ⟨⟨_, ⟨⟨u, Etop.globalSpace₀_le (mesh 3 N) 1 hu⟩, rfl⟩⟩,
    fun h => hx.2 (congrArg Subtype.val h)⟩

/-- **Non-vacuity of the mirror scheme**: the bottom row `∏ₐ P₂Λ⁰_{Γₐ}` is nonzero (it maps onto
`P₁⁻Λ¹ ≠ 0`), the constant mode is a nonzero solution, and for `f = 0` every solution conserves
the energy, so nonzero data give solutions that are nonzero at every time. -/
theorem mirror_nonvacuous :
    (∃ φ : Bot N 0, φ ≠ 0) ∧
      ∀ {T : ℝ} (s : Feec.BGG.DiscreteSolution (mirrorSegment N) T 0),
        (s.σ 0, s.u 0, s.M 0, s.ρ 0) ≠ 0 → ∀ t ∈ Icc 0 T, (s.σ t, s.u t, s.M t, s.ρ t) ≠ 0 := by
  refine ⟨?_, fun s h0 t ht ht0 => h0 ?_⟩
  · obtain ⟨μ, hμ⟩ := exists_top_one_ne_zero N
    obtain ⟨φ, hφ⟩ := mirror_S0_surjective N μ
    exact ⟨φ, fun h => hμ (by rw [← hφ, h, map_zero])⟩
  · have he := s.energy_eq t ht
    simp only [Prod.mk_eq_zero] at ht0
    rw [ht0.1, ht0.2.1, ht0.2.2.1, ht0.2.2.2] at he
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
      at he
    have h1 := sq_nonneg ‖s.σ 0‖
    have h2 := sq_nonneg ‖s.u 0‖
    have h3 := sq_nonneg ‖s.M 0‖
    have h4 := sq_nonneg ‖s.ρ 0‖
    simp only [Prod.mk_eq_zero]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> refine norm_eq_zero.1 (pow_eq_zero_iff (n := 2) two_ne_zero |>.1 ?_)
      <;> linarith

end Feec.Models.Cube.MirrorWeakSymmetry
