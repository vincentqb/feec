module

public import Feec.Foundation.BGG
public import Feec.HilbertComplex.BGG.WeakSymmetry

/-!
# The abstract BGG framework (thesis §5.1): Props 5.1 and 5.2 (compatibility layer)

The content of this file moved to

* `Feec.HilbertComplex.BGG.Basic` (algebra of the complex (5.1), any ring, BGG data of any
  length and the twisted complex),
* `Feec.HilbertComplex.BGG.ToComplex` (analytic BGG data `Feec.BGG.Hilb 𝕜` over `ℝ` or `ℂ`,
  Prop 5.1, and (5.1) as a `Feec.HilbertComplex` on `ComplexShape.fin3`),
* `Feec.HilbertComplex.BGG.WeakSymmetry` (the saddle point problem (5.3), Prop 5.2).

`BGGHilb` is the real case `Feec.BGG.Hilb ℝ`; the main statements below keep their old form and
are thin shims over the new results.

## References

* [QuennevilleBelair2015], §5.1 (Props 5.1, 5.2, (5.1)–(5.3))
* [ArnoldHu2021] (the general BGG construction of complexes from complexes)
-/

open scoped RealInnerProductSpace
open Set Filter Topology

@[expose] public noncomputable section

namespace Feec.Ch5.BGG

section Algebra

variable {V0 V1 W2 Vt0 Vt1 Wt2 : Type*}
  [AddCommGroup V0] [Module ℝ V0] [AddCommGroup V1] [Module ℝ V1]
  [AddCommGroup W2] [Module ℝ W2] [AddCommGroup Vt0] [Module ℝ Vt0]
  [AddCommGroup Vt1] [Module ℝ Vt1] [AddCommGroup Wt2] [Module ℝ Wt2]
  (D : BGGData V0 V1 W2 Vt0 Vt1 Wt2)

lemma D0_apply (x : D.Γ) : D.D0 x = D.dt0 (x : V0 × Vt0).2 := rfl
lemma D1_apply (u : Vt1) : D.D1 u = (D.S1 u, D.dt1 u) := rfl

lemma S1_dt0_of_mem {x : V0 × Vt0} (hx : x ∈ D.Γ) : D.S1 (D.dt0 x.2) = 0 :=
  Feec.BGG.Segment.S1_dt0_of_mem D hx

/-- **Thesis Prop 5.1** (closed range of `(0 d)`, algebraic part): `R(0 d) = R(d̃⁰) ∩ N(S₁)`.
See [QuennevilleBelair2015, Prop 5.1]. -/
theorem range_D0 (hT : D.ExactTop) :
    LinearMap.range D.D0 = LinearMap.range D.dt0 ⊓ LinearMap.ker D.S1 :=
  Feec.BGG.Segment.range_D0 D hT

/-- **Exactness of (5.1) at `Ṽ¹`** (missing in the thesis). Cf. [QuennevilleBelair2015, §5.1]. -/
theorem exact_mid (hT : D.ExactTop) (hB : D.ExactBot) :
    LinearMap.ker D.D1 = LinearMap.range D.D0 :=
  Feec.BGG.Segment.ker_D1_eq_range_D0 D hT hB

theorem D0_injective (hd0 : Function.Injective D.d0) (hdt0 : Function.Injective D.dt0) :
    Function.Injective D.D0 :=
  Feec.BGG.Segment.D0_injective D hd0 hdt0

theorem range_D1 (hreg : LinearMap.range D.d1 ≤ LinearMap.range (D.d1 ∘ₗ D.S0)) :
    (LinearMap.range D.D1 : Set (W2 × Wt2)) =
      {p | ∃ w, D.dt1 w = p.2 ∧ p.1 - D.S1 w ∈ LinearMap.range D.d1} :=
  Feec.BGG.Segment.range_D1 D hreg

theorem D1_surjective (hreg : LinearMap.range D.d1 ≤ LinearMap.range (D.d1 ∘ₗ D.S0))
    (h1 : Function.Surjective D.d1) (h2 : Function.Surjective D.dt1) :
    Function.Surjective D.D1 :=
  Feec.BGG.Segment.D1_surjective D hreg h1 h2

end Algebra

/-- Thesis Prop 5.1, third paragraph (closed range of `(S, d)`), for bounded operators.
See [QuennevilleBelair2015, Prop 5.1 (proof)]. -/
theorem isClosed_range_prod {V1 W2 Vt0 Vt1 Wt2 : Type*}
    [NormedAddCommGroup V1] [NormedSpace ℝ V1]
    [NormedAddCommGroup W2] [NormedSpace ℝ W2]
    [NormedAddCommGroup Vt0] [NormedSpace ℝ Vt0]
    [NormedAddCommGroup Vt1] [NormedSpace ℝ Vt1] [CompleteSpace Vt1]
    [NormedAddCommGroup Wt2] [NormedSpace ℝ Wt2] [CompleteSpace Wt2]
    (d1 : V1 →L[ℝ] W2) (dt0 : Vt0 →L[ℝ] Vt1) (dt1 : Vt1 →L[ℝ] Wt2)
    (S0 : Vt0 →L[ℝ] V1) (S1 : Vt1 →L[ℝ] W2)
    (anticomm : ∀ φ, d1 (S0 φ) = -S1 (dt0 φ)) (hdd : ∀ φ, dt1 (dt0 φ) = 0)
    (exact_bot : ∀ z, dt1 z = 0 → ∃ φ, dt0 φ = z)
    (hd1 : IsClosed (Set.range d1)) (hdt1 : IsClosed (Set.range dt1))
    (hreg : Set.range d1 ⊆ Set.range (d1 ∘ S0)) :
    IsClosed (Set.range (S1.prod dt1)) :=
  Feec.BGG.isClosed_range_prod d1 dt0 dt1 S0 S1 anticomm hdd exact_bot hd1 hdt1 hreg

/-- **Standing hypotheses of thesis §5.1**, the real case of `Feec.BGG.Hilb`.
See [QuennevilleBelair2015, §5.1]. -/
abbrev BGGHilb (W0 W1 Wt0 Wt1 W2 Wt2 V0 V1 Vt0 Vt1 : Type*)
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0] [CompleteSpace Wt0]
    [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1] [CompleteSpace Wt1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
    [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2] [CompleteSpace Wt2]
    [NormedAddCommGroup V0] [InnerProductSpace ℝ V0] [CompleteSpace V0]
    [NormedAddCommGroup V1] [InnerProductSpace ℝ V1] [CompleteSpace V1]
    [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0] [CompleteSpace Vt0]
    [NormedAddCommGroup Vt1] [InnerProductSpace ℝ Vt1] [CompleteSpace Vt1] :=
  Feec.BGG.Hilb ℝ W0 W1 Wt0 Wt1 W2 Wt2 V0 V1 Vt0 Vt1

namespace BGGHilb

open Feec.BGG (Psp Xsp pu)

variable {W0 W1 Wt0 Wt1 W2 Wt2 V0 V1 Vt0 Vt1 : Type*}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0] [CompleteSpace Wt0]
    [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1] [CompleteSpace Wt1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
    [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2] [CompleteSpace Wt2]
    [NormedAddCommGroup V0] [InnerProductSpace ℝ V0] [CompleteSpace V0]
    [NormedAddCommGroup V1] [InnerProductSpace ℝ V1] [CompleteSpace V1]
    [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0] [CompleteSpace Vt0]
    [NormedAddCommGroup Vt1] [InnerProductSpace ℝ Vt1] [CompleteSpace Vt1]
    (D : BGGHilb W0 W1 Wt0 Wt1 W2 Wt2 V0 V1 Vt0 Vt1)

/-- Exactness of (5.1) at `Ṽ¹`: `N(S₁) ∩ N(d̃¹) = d̃(π₂ Γ)`. Cf. [QuennevilleBelair2015, §5.1]. -/
theorem mem_Z1_iff (h : D.Hyps) {u : Vt1} : u ∈ D.Z1 ↔ ∃ x ∈ D.Γ, D.dt0 x.2 = u :=
  Feec.BGG.Hilb.mem_Z1_iff D h

/-- **Thesis Prop 5.1**: the complex with weak symmetries (5.1) is a closed Hilbert complex,
exact at `Γ̄` and at `W̃¹`. See [QuennevilleBelair2015, Prop 5.1]. -/
theorem prop_5_1 (h : D.Hyps) (hS0 : Function.Injective D.S0) :
    D.D0op.IsClosed ∧ D.D0op.domain.topologicalClosure = D.Γbar ∧
    IsClosed (LinearMap.range D.D0op.toFun : Set Wt1) ∧
    D.D1op.IsClosed ∧ Dense (D.D1op.domain : Set Wt1) ∧
    IsClosed (LinearMap.range D.D1op.toFun : Set (W2 × Wt2)) ∧
    LinearMap.range D.D0op.toFun ≤ D.D1op.ker ∧
    D.D1op.ker = LinearMap.range D.D0op.toFun ∧ D.D0op.ker = ⊥ :=
  Feec.BGG.Hilb.isClosed_closedRange_exact D h hS0

/-- **Thesis Prop 5.2** (corrected), general form: (5.3) is well posed on `X × W̌¹`.
See [QuennevilleBelair2015, Prop 5.2]. -/
theorem prop_5_2_wellPosed (h : D.Hyps) :
    (∀ (F : Xsp V0 Vt0 Vt1) (G : D.Wcheck), ∃! xl : Xsp V0 Vt0 Vt1 × D.Wcheck,
      (∀ y, D.aForm xl.1 y + D.bForm y xl.2 = ⟪F, y⟫) ∧ ∀ μ, D.bForm xl.1 μ = ⟪G, μ⟫) ∧
    ∃ C, ∀ (F : Xsp V0 Vt0 Vt1) (G : D.Wcheck) (x : Xsp V0 Vt0 Vt1) (l : D.Wcheck),
      (∀ y, D.aForm x y + D.bForm y l = ⟪F, y⟫) → (∀ μ, D.bForm x μ = ⟪G, μ⟫) →
        ‖x‖ + ‖l‖ ≤ C * (‖F‖ + ‖G‖) :=
  Feec.BGG.Hilb.saddle_wellPosed D h

/-- The system (5.3) with right-hand side `f ∈ W̃¹` and multiplier `λ ∈ W̌¹`. -/
abbrev Saddle (f : Wt1) (x : Xsp V0 Vt0 Vt1) (l : D.Wcheck) : Prop :=
  Feec.BGG.Hilb.IsSaddle D f x l

/-- **Thesis Prop 5.2**: (5.3) is well posed over `V⁰ × Ṽ⁰ × Ṽ¹ × W̌¹`.
See [QuennevilleBelair2015, Prop 5.2]. -/
theorem prop_5_2 (h : D.Hyps) :
    (∀ f : Wt1, ∃! xl : Xsp V0 Vt0 Vt1 × D.Wcheck, D.Saddle f xl.1 xl.2) ∧
    ∃ C, ∀ (f : Wt1) (x : Xsp V0 Vt0 Vt1) (l : D.Wcheck), D.Saddle f x l →
      ‖x‖ + ‖l‖ ≤ C * ‖f‖ :=
  Feec.BGG.Hilb.existsUnique_isSaddle D h

end BGGHilb

/-- A nontrivial BGG datum on `ℝ` (`Feec.BGG.Hilb.scalarExample`). -/
abbrev exampleBGG : BGGHilb ℝ ℝ ℝ ℝ ℝ ℝ ℝ ℝ ℝ ℝ := Feec.BGG.Hilb.scalarExample

/-- Non-vacuity of the hypotheses of thesis Props 5.1 and 5.2. -/
theorem exampleBGG_hyps :
    exampleBGG.Hyps ∧ Function.Injective exampleBGG.S0 ∧ ((1 : ℝ), (4 / 5 : ℝ)) ∈ exampleBGG.Γ :=
  Feec.BGG.Hilb.scalarExample_hyps

end Feec.Ch5.BGG
