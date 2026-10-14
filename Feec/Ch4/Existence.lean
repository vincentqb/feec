import Feec.Foundation

/-!
# Non-vacuity of the existence hypotheses (Thesis Thm 4.3, Hille–Yosida / Stone)

Mathlib has no Hille–Yosida or Stone theorem, so the project states existence of time evolutions
as the explicit hypotheses `Feec.WellPosedExistence` / `Feec.WellPosedHom` (Foundation §B).
This module shows that these hypotheses are satisfiable and that they follow from a recognisable
stand-in for Stone's theorem.

* `Feec.bddOp A`: an everywhere-defined bounded operator `A : E →L[ℝ] E` as a `LinearPMap`.
* `Feec.wellPosedHom_bddOp`, `Feec.wellPosedExistence_bddOp`: for **every** bounded `A`,
  `U t = exp(tA) U₀ + ∫₀ᵗ exp((t-s)A) F s ds` (Duhamel) is a strong solution, for all
  `F ∈ C([0,T]; E)`. This is the thesis' admissible class: for `D(L) = E` the class
  `C([0,T];X) ∩ (W^{1,1}(0,T;X) ∪ L¹(0,T;D(L)))` is exactly `C([0,T];X)`.
* `Feec.isSkewAdjoint_bddOp`: a bounded skew-symmetric `A` is skew-adjoint in the
  `LinearPMap` sense, with dense (full) domain. So the hypotheses of the Ch. 4 theorems
  (`IsSkewAdjoint L`, dense domain, `WellPosedExistence L T Adm`) hold simultaneously.
* `Feec.UnitaryGroupGenerator L`: the conclusion of Stone's theorem (`L` generates a strongly
  continuous orthogonal group), as a hypothesis structure. We prove it yields `WellPosedHom L T`
  (`UnitaryGroupGenerator.wellPosedHom`), that its generator is skew-symmetric
  (`UnitaryGroupGenerator.isSkewSymm`), and that it is inhabited for bounded skew `A` via
  `NormedSpace.exp` (`Feec.expGroup`).
* `Feec.exists_classical_solution_bddOp`: the bounded-case solutions are classical
  (`C¹` on `ℝ`, with `t ↦ A (U t)` continuous), not merely `IsStrongSolution`.
* `Feec.bddOp_standing_hypotheses`: all of the above at once for a bounded skew `A`;
  `Feec.rotGen_standing_hypotheses`: a concrete nonzero instance (rotation generator on `ℝ²`).

Scope: `IsStrongSolution` only asks for a pointwise derivative within `[0,T]`; the bounded
witnesses are shown to be `C¹` separately.
The unbounded case (e.g. the Hodge wave operator) still needs Stone's theorem, i.e. a
`UnitaryGroupGenerator` hypothesis.
-/

open scoped RealInnerProductSpace
open Set NormedSpace

noncomputable section

namespace Feec

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `ℚ`-algebra structure on operators, needed by `NormedSpace.exp_add_of_commute` and
`NormedSpace.exp_mem_unitary_of_mem_skewAdjoint`. (`exp` itself does not depend on it.) -/
local instance instNormedAlgebraRatOp : NormedAlgebra ℚ (E →L[ℝ] E) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

/-! ### Bounded operators as everywhere-defined `LinearPMap`s -/

/-- An everywhere-defined bounded operator, viewed as a (trivially densely defined) unbounded
operator with domain `⊤`. -/
def bddOp (A : E →L[ℝ] E) : E →ₗ.[ℝ] E := (A : E →ₗ[ℝ] E).toPMap ⊤

/-- `D(bddOp A) = E`. -/
@[simp] theorem bddOp_domain (A : E →L[ℝ] E) : (bddOp A).domain = ⊤ := rfl

/-- `bddOp A` acts as `A`. -/
@[simp] theorem bddOp_apply (A : E →L[ℝ] E) (x : (bddOp A).domain) : bddOp A x = A x := rfl

/-- `bddOp A` is densely defined (Thesis §4.2 standing hypothesis `D(L)` dense). -/
theorem dense_bddOp_domain (A : E →L[ℝ] E) : Dense ((bddOp A).domain : Set E) := by
  simp [dense_univ]

/-- Skew-symmetric bounded operators satisfy `A† = -A`. -/
theorem adjoint_eq_neg_of_skew [CompleteSpace E] {A : E →L[ℝ] E}
    (hA : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫) : ContinuousLinearMap.adjoint A = -A := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp [hA]

/-- A bounded operator with `⟪A x, y⟫ = -⟪x, A y⟫` is skew-adjoint as an unbounded operator:
`(bddOp A)† = -bddOp A` (equal domains). Thesis §4.2: the bounded case of the skew-adjoint
operators to which Thm 4.3 applies. -/
theorem isSkewAdjoint_bddOp [CompleteSpace E] (A : E →L[ℝ] E)
    (hA : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫) : IsSkewAdjoint (bddOp A) := by
  unfold IsSkewAdjoint bddOp
  rw [ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense A (by simp [dense_univ]),
    adjoint_eq_neg_of_skew hA]
  exact LinearPMap.ext (by simp) fun x _ _ => rfl

/-! ### The exponential flow -/

section Exp

variable [CompleteSpace E]

/-- `(d/dt) exp(tA) x = A exp(tA) x`. -/
theorem hasDerivAt_exp_smul_apply (A : E →L[ℝ] E) (x : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (s • A) x) (A (exp (t • A) x)) t := by
  have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t)
  have := (ContinuousLinearMap.apply ℝ E x).hasFDerivAt.comp_hasDerivAt t h
  simpa [Function.comp_def] using this

/-- `t ↦ exp(tA)` is norm-continuous. -/
theorem continuous_exp_smul (A : E →L[ℝ] E) : Continuous fun s : ℝ => exp (s • A) :=
  exp_continuous.comp (continuous_id.smul continuous_const)

/-- `exp(tA) exp(-tA) = 1`. -/
theorem exp_smul_mul_exp_neg_smul (A : E →L[ℝ] E) (t : ℝ) :
    exp (t • A) * exp ((-t) • A) = 1 := by
  rw [← exp_add_of_commute ((Commute.refl A).smul_left t |>.smul_right (-t)), neg_smul,
    add_neg_cancel, exp_zero]

/-- Duhamel's formula `U t = exp(tA) (U₀ + ∫₀ᵗ exp(-sA) G s ds)` for a forcing `G` on `ℝ`. -/
def duhamel (A : E →L[ℝ] E) (U₀ : E) (G : ℝ → E) (t : ℝ) : E :=
  exp (t • A) (U₀ + ∫ s in (0:ℝ)..t, exp ((-s) • A) (G s))

omit [CompleteSpace E] in
@[simp] theorem duhamel_zero (A : E →L[ℝ] E) (U₀ : E) (G : ℝ → E) : duhamel A U₀ G 0 = U₀ := by
  simp [duhamel]

/-- For continuous `G`, Duhamel's formula solves `U' = A U + G` on all of `ℝ`. -/
theorem hasDerivAt_duhamel (A : E →L[ℝ] E) (U₀ : E) {G : ℝ → E} (hG : Continuous G) (t : ℝ) :
    HasDerivAt (duhamel A U₀ G) (A (duhamel A U₀ G t) + G t) t := by
  have hgc : Continuous fun s : ℝ => exp ((-s) • A) (G s) :=
    ((continuous_exp_smul A).comp continuous_neg).clm_apply hG
  have hv := (hgc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add U₀
  have hc : HasDerivAt (fun s : ℝ => exp (s • A)) (A * exp (t • A)) t :=
    hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t
  refine HasDerivAt.congr_deriv (f := duhamel A U₀ G) (hc.clm_apply hv) ?_
  change (A * exp (t • A)) _ + exp (t • A) (exp ((-t) • A) (G t)) = A (duhamel A U₀ G t) + G t
  rw [mul_apply_eq_comp, ← mul_apply_eq_comp (exp (t • A)), exp_smul_mul_exp_neg_smul,
    one_apply_eq_self]
  rfl

/-- For continuous `G`, the Duhamel solution is `C¹` on `ℝ`. -/
theorem contDiff_duhamel (A : E →L[ℝ] E) (U₀ : E) {G : ℝ → E} (hG : Continuous G) :
    ContDiff ℝ 1 (duhamel A U₀ G) := by
  have hd := hasDerivAt_duhamel A U₀ hG
  have hc : Continuous (duhamel A U₀ G) := continuous_iff_continuousAt.2 fun t =>
    (hd t).continuousAt
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hd t).differentiableAt, ?_⟩
  rw [show deriv (duhamel A U₀ G) = fun t => A (duhamel A U₀ G t) + G t from
    funext fun t => (hd t).deriv]
  exact (A.continuous.comp hc).add hG

/-- **Classical solutions for bounded `L`** (Thesis Thm 4.3, bounded case, with the
regularity of critic item 5). For every bounded `A`, `U₀ ∈ E` and `F ∈ C([0,T]; E)`, `T ≥ 0`,
there is a strong solution `U` of `U' = A U + F`, `U 0 = U₀`, which is moreover the restriction
of a `C¹` function on `ℝ`, with `t ↦ A (U t)` continuous: `U ∈ C¹([0,T]; E) ∩ C([0,T]; D(L))`.

Thesis gap: the thesis' notion of solution is classical, while `IsStrongSolution` only asks for
a pointwise derivative; this shows the bounded witnesses are classical. -/
theorem exists_classical_solution_bddOp (A : E →L[ℝ] E) {T : ℝ} (hT : 0 ≤ T) (U₀ : E)
    {F : ℝ → E} (hF : ContinuousOn F (Icc 0 T)) :
    ∃ U : ℝ → E, IsStrongSolution (bddOp A) T U₀ F U ∧ ContDiff ℝ 1 U ∧
      Continuous fun t => A (U t) := by
  -- continuous extension of `F` from `[0,T]` to `ℝ`
  set G : ℝ → E := fun s => F (projIcc 0 T hT s) with hGdef
  have hGc : Continuous G := hF.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    (fun s => (projIcc 0 T hT s).2)
  have hGF : ∀ t ∈ Icc 0 T, G t = F t := fun t ht => by
    simp [hGdef, projIcc_of_mem hT ht]
  have hU := contDiff_duhamel A U₀ hGc
  refine ⟨duhamel A U₀ G, ⟨fun _ _ => trivial, fun t ht => ?_, duhamel_zero A U₀ G⟩, hU,
    A.continuous.comp hU.continuous⟩
  have := (hasDerivAt_duhamel A U₀ hGc t).hasDerivWithinAt (s := Icc 0 T)
  rwa [hGF t ht] at this

/-- **Non-vacuity of `WellPosedExistence` (Thesis Thm 4.3, bounded case).**
For every everywhere-defined bounded `A` and every `F ∈ C([0,T]; E)`, Duhamel's formula
`U t = exp(tA) (U₀ + ∫₀ᵗ exp(-sA) F s ds)` is a strong solution of `U' = A U + F`, `U 0 = U₀`.
No skewness is needed for existence; it is needed for uniqueness/energy (proved elsewhere).

Thesis gap: Thm 4.3 is only cited (Hille–Yosida/Stone); the project replaces it by the
hypothesis `WellPosedExistence`. This theorem shows that hypothesis is satisfiable, with the
thesis' admissible class (which is `C([0,T];E)` when `D(L) = E`). -/
theorem wellPosedExistence_bddOp (A : E →L[ℝ] E) (T : ℝ) :
    WellPosedExistence (bddOp A) T (fun F => ContinuousOn F (Icc 0 T)) := by
  intro U₀ _ F hF
  by_cases hT : 0 ≤ T
  · obtain ⟨U, hU, -⟩ := exists_classical_solution_bddOp A hT U₀ hF
    exact ⟨U, hU⟩
  · refine ⟨fun _ => U₀, fun _ _ => trivial, fun t ht => ?_, rfl⟩
    exact absurd (ht.1.trans ht.2) hT

/-- **Non-vacuity of `WellPosedHom`** (Thesis Thm 4.3/4.6 hypothesis, bounded case):
`U t = exp(tA) U₀` is a strong solution of `U' = A U`. -/
theorem wellPosedHom_bddOp (A : E →L[ℝ] E) (T : ℝ) : WellPosedHom (bddOp A) T := by
  intro U₀ _
  refine ⟨fun t => exp (t • A) U₀, fun _ _ => trivial, fun t _ => ?_, by simp⟩
  simp only [Pi.zero_apply, add_zero]
  exact (hasDerivAt_exp_smul_apply A U₀ t).hasDerivWithinAt

end Exp

/-! ### A Stone-theorem stand-in -/

/-- `L` generates a strongly continuous orthogonal ("unitary") group `S`.
This is the conclusion of Stone's theorem for a skew-adjoint `L` (Thesis Thm 4.3 cites
Hille–Yosida/Stone; Mathlib has neither), packaged as a hypothesis structure:
`S` is a group of isometries, strongly continuous, and `L` is its generator, i.e.
`D(L) = {x | t ↦ S t x differentiable at 0}` with `L x = (d/dt) S t x |_{t=0}`. -/
structure UnitaryGroupGenerator (L : E →ₗ.[ℝ] E) where
  /-- the group `t ↦ S t = e^{tL}` -/
  S : ℝ → E →L[ℝ] E
  map_zero : S 0 = 1
  map_add : ∀ s t, S (s + t) = S s * S t
  norm_map : ∀ t x, ‖S t x‖ = ‖x‖
  continuous_apply : ∀ x, Continuous fun t => S t x
  mem_domain_iff : ∀ x, x ∈ L.domain ↔ DifferentiableAt ℝ (fun t => S t x) 0
  hasDerivAt_zero : ∀ x : L.domain, HasDerivAt (fun t => S t x) (L x) 0

namespace UnitaryGroupGenerator

variable {L : E →ₗ.[ℝ] E} (G : UnitaryGroupGenerator L)

/-- The group is commutative. -/
theorem comm (s t : ℝ) : G.S s * G.S t = G.S t * G.S s := by
  rw [← G.map_add, ← G.map_add, add_comm]

/-- Orbits of domain points are differentiable everywhere: `(d/dt) S t x = S t (L x)`. -/
theorem hasDerivAt_apply (x : L.domain) (t : ℝ) :
    HasDerivAt (fun s => G.S s x) (G.S t (L x)) t := by
  have h0 := (G.S t).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (G.hasDerivAt_zero x)
  rw [show (0 : ℝ) = t - t from (sub_self t).symm] at h0
  have h1 := h0.comp_sub_const t t
  convert h1 using 1
  funext s
  simp only [Function.comp_apply, ← mul_apply_eq_comp, ← G.map_add]
  congr 2; ring

/-- `S t` preserves `D(L)`. -/
theorem mem_domain_apply (x : L.domain) (t : ℝ) : G.S t x ∈ L.domain := by
  rw [G.mem_domain_iff]
  have h := ((G.S t).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (G.hasDerivAt_zero x))
  refine h.differentiableAt.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp only [Function.comp_apply, ← mul_apply_eq_comp, G.comm]

/-- `L (S t x) = S t (L x)` on `D(L)`. -/
theorem apply_comm (x : L.domain) (t : ℝ) :
    L ⟨G.S t x, G.mem_domain_apply x t⟩ = G.S t (L x) := by
  have h := ((G.S t).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (G.hasDerivAt_zero x))
  refine (G.hasDerivAt_zero ⟨_, G.mem_domain_apply x t⟩).unique (h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => ?_))
  simp only [Function.comp_apply, ← mul_apply_eq_comp, G.comm]

/-- **`WellPosedHom` from the Stone stand-in.** If `L` generates an orthogonal group `S`, then
`U t = S t U₀` is a strong solution of `U' = L U`, `U 0 = U₀`, for every `U₀ ∈ D(L)`.
Thesis Thm 4.3/4.6: this is the existence half of Thm 4.3 (homogeneous case) derived from
the conclusion of Stone's theorem, so the existence conclusions of Ch. 4 rest on that. -/
theorem wellPosedHom (G : UnitaryGroupGenerator L) (T : ℝ) : WellPosedHom L T := by
  intro U₀ hU₀
  refine ⟨fun t => G.S t U₀, fun t _ => G.mem_domain_apply ⟨U₀, hU₀⟩ t, fun t _ => ?_, ?_⟩
  · simp only [Pi.zero_apply, add_zero]
    rw [G.apply_comm ⟨U₀, hU₀⟩ t]
    exact (G.hasDerivAt_apply ⟨U₀, hU₀⟩ t).hasDerivWithinAt
  · simp [G.map_zero]

/-- The generator of an orthogonal group is skew-symmetric (easy half of Stone's theorem):
differentiate `⟪S t x, S t y⟫ = ⟪x, y⟫` at `t = 0`. Sanity check that the structure
`UnitaryGroupGenerator` is consistent with the skew-adjointness hypotheses of Ch. 4. -/
theorem isSkewSymm (G : UnitaryGroupGenerator L) : IsSkewSymm L := by
  intro x y
  have hconst : (fun t => ⟪G.S t x, G.S t y⟫) = fun _ => ⟪(x : E), (y : E)⟫ := by
    funext t
    exact (LinearMap.norm_map_iff_inner_map_map (G.S t)).mp (G.norm_map t) x y
  have hd := (G.hasDerivAt_zero x).inner ℝ (G.hasDerivAt_zero y)
  rw [hconst] at hd
  have h0 := hd.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [G.map_zero, one_apply_eq_self] at h0
  linarith

end UnitaryGroupGenerator

/-- Group law `exp((s+t)A) = exp(sA) exp(tA)`. -/
theorem exp_smul_add [CompleteSpace E] (A : E →L[ℝ] E) (s t : ℝ) :
    exp ((s + t) • A) = exp (s • A) * exp (t • A) := by
  rw [add_smul, exp_add_of_commute ((Commute.refl A).smul_left s |>.smul_right t)]

/-- For skew `A`, `exp(tA)` is an isometry (it is unitary since `tA` is skew-adjoint). -/
theorem norm_exp_smul_apply [CompleteSpace E] {A : E →L[ℝ] E}
    (hA : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫) (t : ℝ) (x : E) : ‖exp (t • A) x‖ = ‖x‖ := by
  have hskew : t • A ∈ skewAdjoint (E →L[ℝ] E) := by
    rw [skewAdjoint.mem_iff, star_smul, star_trivial, ContinuousLinearMap.star_eq_adjoint,
      adjoint_eq_neg_of_skew hA, smul_neg]
  exact ContinuousLinearMap.norm_map_of_mem_unitary (exp_mem_unitary_of_mem_skewAdjoint hskew) x

/-- `(d/dt) exp(tA) x |_{t=0} = A x`. -/
theorem hasDerivAt_exp_smul_apply_zero [CompleteSpace E] (A : E →L[ℝ] E) (x : E) :
    HasDerivAt (fun s : ℝ => exp (s • A) x) (A x) 0 := by
  have := hasDerivAt_exp_smul_apply A x 0
  rwa [zero_smul, exp_zero, one_apply_eq_self] at this

/-- **The Stone stand-in is inhabited:** a bounded skew-symmetric `A` generates the orthogonal
group `t ↦ exp(tA)` (`NormedSpace.exp` in the C*-algebra `E →L[ℝ] E`; `tA` is skew-adjoint,
so `exp(tA)` is unitary). -/
def expGroup [CompleteSpace E] (A : E →L[ℝ] E) (hA : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫) :
    UnitaryGroupGenerator (bddOp A) where
  S t := exp (t • A)
  map_zero := by rw [zero_smul, exp_zero]
  map_add := exp_smul_add A
  norm_map := norm_exp_smul_apply hA
  continuous_apply x := (continuous_exp_smul A).clm_apply continuous_const
  mem_domain_iff x := iff_of_true trivial (hasDerivAt_exp_smul_apply_zero A x).differentiableAt
  hasDerivAt_zero x := hasDerivAt_exp_smul_apply_zero A (x : E)

/-- **Joint non-vacuity of the Ch. 4 standing hypotheses** (Thesis §4.2, Thm 4.3, Cor 4.5):
for every bounded skew-symmetric `A`, the operator `L = bddOp A` is densely defined,
skew-adjoint, satisfies `WellPosedExistence` with the thesis' admissible forcings
`C([0,T];E)`, and `WellPosedHom` follows from its Stone group `expGroup A hA`. -/
theorem bddOp_standing_hypotheses [CompleteSpace E] (A : E →L[ℝ] E)
    (hA : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫) (T : ℝ) :
    Dense ((bddOp A).domain : Set E) ∧ IsSkewAdjoint (bddOp A) ∧
      WellPosedExistence (bddOp A) T (fun F => ContinuousOn F (Icc 0 T)) ∧
      WellPosedHom (bddOp A) T :=
  ⟨dense_bddOp_domain A, isSkewAdjoint_bddOp A hA, wellPosedExistence_bddOp A T,
    (expGroup A hA).wellPosedHom T⟩

/-! ### A concrete nonzero example: the rotation generator on `ℝ²` -/

/-- The rotation generator `J (x₀, x₁) = (-x₁, x₀)` on `EuclideanSpace ℝ (Fin 2)`. -/
def rotGen : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.proj (0 : Fin 2)).smulRight (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) -
    (EuclideanSpace.proj (1 : Fin 2)).smulRight (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))

theorem rotGen_apply (x : EuclideanSpace ℝ (Fin 2)) :
    rotGen x = x 0 • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) -
      x 1 • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) := by
  simp [rotGen]

/-- `J` is skew-symmetric. -/
theorem rotGen_skew (x y : EuclideanSpace ℝ (Fin 2)) : ⟪rotGen x, y⟫ = -⟪x, rotGen y⟫ := by
  simp only [rotGen_apply, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right]
  simp
  ring

/-- `J ≠ 0`, so the witness below is not the trivial operator. -/
theorem rotGen_ne_zero : rotGen ≠ 0 := by
  intro h
  have := congrArg (fun f : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) =>
    f (EuclideanSpace.single 0 1) 1) h
  simp [rotGen_apply] at this

/-- **A concrete nonzero witness** for the Ch. 4 standing hypotheses (Thesis §4.2, Thm 4.3,
Cor 4.5): the rotation generator `J ≠ 0` on `ℝ²` satisfies all of them. -/
theorem rotGen_standing_hypotheses (T : ℝ) :
    rotGen ≠ 0 ∧ Dense ((bddOp rotGen).domain : Set (EuclideanSpace ℝ (Fin 2))) ∧
      IsSkewAdjoint (bddOp rotGen) ∧
      WellPosedExistence (bddOp rotGen) T (fun F => ContinuousOn F (Icc 0 T)) ∧
      WellPosedHom (bddOp rotGen) T :=
  ⟨rotGen_ne_zero, bddOp_standing_hypotheses rotGen rotGen_skew T⟩

end Feec
