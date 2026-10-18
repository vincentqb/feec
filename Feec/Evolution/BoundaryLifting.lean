module

public import Feec.Evolution.WellPosed
public import Feec.Evolution.Energy

/-!
# Inhomogeneous boundary data by lifting

An evolution problem with boundary conditions is given by two operators `A ≤ A_max` on a
Hilbert space `E`: `A_max` acts without boundary condition (e.g. `d_max − d_min†` for a Hodge
wave equation, or `curl_max` for Maxwell), and `A` is its restriction to the fields with
**homogeneous** boundary values, `D(A) = {x ∈ D(A_max) | γ x = 0}` for a trace `γ`
(`sub_mem_domain_iff_trace_eq`). Inhomogeneous boundary data are prescribed through a field `G(t)`
with the desired traces (a **lifting**): `U` solves the problem with data `γ G` when

`U' = A_max U + F`,  `U(t) − G(t) ∈ D(A)` (`IsBoundarySolution A_max A I F G U`).

For a lifting with `G ∈ C¹(I; E)`, `G(t) ∈ D(A_max)`, the substitution `W = U − G` reduces it to
the homogeneous problem with the extra forcing `A_max G − G'` (`isBoundarySolution_iff`):

`W' = A W + (F − G' + A_max G)`,

i.e. the forcing `F − (G' + L G)` for `L = −A_max`. This gives existence and uniqueness of the
inhomogeneous problem from Duhamel's formula for the homogeneous one, for every forcing class of
`Feec.Evolution.ForcingClass` (`existsUnique_isBoundarySolution`,
`C0Semigroup.existsUnique_isBoundarySolution`), and the energy estimate
`‖U(t) − G(t)‖ ≤ ‖U(a) − G(a)‖ + ∫ₐᵗ ‖F − G' + A_max G‖` (`IsBoundarySolution.norm_sub_le`).

## Main results

* `isBoundarySolution_iff`: the reduction to homogeneous boundary values.
* `IsBoundarySolution.unique`: uniqueness for dissipative `A` (no regularity of the lifting).
* `isBoundarySolution_congr`: the solution depends on `G` only through its traces.
* `existsUnique_isBoundarySolution` (skew-adjoint `A`, Stone's group),
  `C0Semigroup.existsUnique_isBoundarySolution` (any semigroup generator): a classical solution
  `W = U − G` exists for `U(a) − G(a) ∈ D(A)` and admissible `F − G' + A_max G`, and it is unique.
* `IsBoundarySolution.norm_sub_le`, `IsBoundarySolution.norm_le`,
  `IsBoundarySolution.norm_sub_sub_le`: energy estimates and continuous dependence on the initial
  value, the forcing and the boundary data.
* `IsBoundarySolution.hasDerivWithinAt_norm_sq`: the energy identity
  `d/dt ‖U‖² = 2 re ⟪A_max U + F, U⟫`; the boundary flux `re ⟪A_max U, U⟫` vanishes when `U(t)`
  has homogeneous boundary values and `A` is skew-symmetric (`re_inner_eq_zero_of_mem_domain`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 7 (the experiments prescribe the traces of the exact solution), §4.3 (Thm 4.3)
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §4.1–4.2 (inhomogeneous problems)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 8 (Hodge evolution problems)
-/

open Set Filter

@[expose] public noncomputable section

namespace Feec.Evolution

section General

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] {Amax A : E →ₗ.[𝕜] E} {I : Set ℝ} {F G U V : ℝ → E}

omit [NormedSpace ℝ E] in
/-- The graph of a linear partial map is functional. -/
theorem _root_.LinearPMap.eq_of_mem_graph {f : E →ₗ.[𝕜] E} {x y₁ y₂ : E}
    (h₁ : (x, y₁) ∈ f.graph) (h₂ : (x, y₂) ∈ f.graph) : y₁ = y₂ := by
  have h := f.graph.sub_mem h₁ h₂
  rw [Prod.mk_sub_mk, sub_self] at h
  exact sub_eq_zero.1 (f.graph_fst_eq_zero_snd h rfl)

omit [NormedSpace ℝ E] in
/-- For `A ≤ A_max`, a point of the graph of `A_max` whose first component lies in `D(A)` lies
in the graph of `A`. -/
theorem _root_.LinearPMap.mem_graph_of_le {f g : E →ₗ.[𝕜] E} (hle : f ≤ g) {x y : E}
    (hx : x ∈ f.domain) (h : (x, y) ∈ g.graph) : (x, y) ∈ f.graph := by
  have h₁ : (x, f ⟨x, hx⟩) ∈ f.graph := f.mem_graph ⟨x, hx⟩
  rwa [LinearPMap.eq_of_mem_graph h (LinearPMap.le_graph_iff.2 hle h₁)]

/-- `U` solves the evolution problem `U' = A_max U + F` on `I` **with the boundary values of
`G`**: `U` is a strong solution for the operator `A_max` without boundary conditions, and
`U(t) − G(t)` has homogeneous boundary values, `U(t) − G(t) ∈ D(A)`. For `G = 0` this is a
strong solution of `U' = A U + F` (`isBoundarySolution_zero_iff`). -/
structure IsBoundarySolution (Amax A : E →ₗ.[𝕜] E) (I : Set ℝ) (F G U : ℝ → E) : Prop where
  toIsStrongSolution : IsStrongSolution Amax I F U
  sub_mem : ∀ t ∈ I, U t - G t ∈ A.domain

/-- `G` is a **lifting** on `I` with time derivative `DG` and `A_max G = AG`: `G(t) ∈ D(A_max)`
with `A_max G(t) = AG(t)`, and `G' = DG` within `I`. -/
structure IsLifting (Amax : E →ₗ.[𝕜] E) (I : Set ℝ) (G DG AG : ℝ → E) : Prop where
  mem_graph : ∀ t ∈ I, (G t, AG t) ∈ Amax.graph
  hasDerivWithinAt : ∀ t ∈ I, HasDerivWithinAt G (DG t) I t

/-- **Reduction to homogeneous boundary values**: for `A ≤ A_max` and a lifting `G`, `U` solves
`U' = A_max U + F` with the boundary values of `G` iff `W = U − G` is a strong solution of the
homogeneous problem `W' = A W + (F − G' + A_max G)`. -/
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

/-- With homogeneous boundary data (`G = 0`), boundary solutions are the strong solutions of
`U' = A U + F`. -/
theorem isBoundarySolution_zero_iff (hle : A ≤ Amax) :
    IsBoundarySolution Amax A I F 0 U ↔ IsStrongSolution A I F U := by
  have hG : IsLifting Amax I 0 0 0 :=
    ⟨fun _ _ => Amax.graph.zero_mem, fun t _ => hasDerivWithinAt_const t I (0 : E)⟩
  rw [isBoundarySolution_iff hle hG, sub_zero, add_zero, sub_zero]

/-- **The solution depends on the lifting only through its traces**: if `G₁(t) − G₂(t)` has
homogeneous boundary values for every `t`, the problems with the boundary values of `G₁` and of
`G₂` have the same solutions. -/
theorem isBoundarySolution_congr {G₁ G₂ : ℝ → E} (h : ∀ t ∈ I, G₁ t - G₂ t ∈ A.domain) :
    IsBoundarySolution Amax A I F G₁ U ↔ IsBoundarySolution Amax A I F G₂ U := by
  constructor
  · rintro ⟨hU, hs⟩
    refine ⟨hU, fun t ht => ?_⟩
    have := A.domain.add_mem (hs t ht) (h t ht)
    rwa [sub_add_sub_cancel] at this
  · rintro ⟨hU, hs⟩
    refine ⟨hU, fun t ht => ?_⟩
    have := A.domain.sub_mem (hs t ht) (h t ht)
    rwa [sub_sub_sub_cancel_right] at this

omit [NormedSpace ℝ E] in
/-- **Boundary values as traces**: if `D(A)` is the kernel of a trace map `γ` on `D(A_max)`,
then `x − y ∈ D(A)` iff `γ x = γ y`, for `x, y ∈ D(A_max)`. -/
theorem sub_mem_domain_iff_trace_eq {B : Type*} [AddCommGroup B] [Module 𝕜 B]
    (γ : Amax.domain →ₗ[𝕜] B) (hγ : ∀ x : Amax.domain, γ x = 0 ↔ (x : E) ∈ A.domain)
    (x y : Amax.domain) : (x : E) - y ∈ A.domain ↔ γ x = γ y := by
  rw [← sub_eq_zero, ← map_sub, hγ]
  rfl

/-- Linearity: the difference of two boundary solutions solves the problem with the difference
of the data. -/
theorem IsBoundarySolution.sub {F₂ G₂ : ℝ → E} (hU : IsBoundarySolution Amax A I F G U)
    (hV : IsBoundarySolution Amax A I F₂ G₂ V) :
    IsBoundarySolution Amax A I (F - F₂) (G - G₂) (U - V) := by
  refine ⟨hU.toIsStrongSolution.sub hV.toIsStrongSolution, fun t ht => ?_⟩
  have := A.domain.sub_mem (hU.sub_mem t ht) (hV.sub_mem t ht)
  convert this using 1
  simp only [Pi.sub_apply]
  abel

/-- The difference of two solutions with the same boundary data and forcing is a strong solution
of the homogeneous problem `W' = A W`. -/
theorem IsBoundarySolution.isStrongSolution_sub (hle : A ≤ Amax)
    (hU : IsBoundarySolution Amax A I F G U) (hV : IsBoundarySolution Amax A I F G V) :
    IsStrongSolution A I 0 (U - V) := by
  have h := hU.sub hV
  rw [sub_self, sub_self] at h
  have := (isBoundarySolution_zero_iff (I := I) (F := 0) (U := U - V) hle).1 h
  exact this

/-- **Uniqueness** for a dissipative `A`: two solutions on `[a, b]` with the same boundary data,
forcing and initial value agree. No regularity of `G` is needed. -/
theorem IsBoundarySolution.unique (hle : A ≤ Amax) (hA : A.IsDissipative) {a b : ℝ}
    (hU : IsBoundarySolution Amax A (Icc a b) F G U)
    (hV : IsBoundarySolution Amax A (Icc a b) F G V) (h0 : U a = V a) : EqOn U V (Icc a b) := by
  have hW := hU.isStrongSolution_sub hle hV
  intro t ht
  have := hW.unique hA (IsStrongSolution.zero (A := A) (I := Icc a b)) (by simp [h0]) ht
  simpa [sub_eq_zero] using this

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- **Energy estimate**: for dissipative `A`, a lifting `G` and continuous
`F − G' + A_max G`, `‖U(t) − G(t)‖ ≤ ‖U(a) − G(a)‖ + ∫ₐᵗ ‖F − G' + A_max G‖` on `[a, b]`. -/
theorem IsBoundarySolution.norm_sub_le (hle : A ≤ Amax) (hA : A.IsDissipative) {a b : ℝ}
    {DG AG : ℝ → E} (hG : IsLifting Amax (Icc a b) G DG AG)
    (hU : IsBoundarySolution Amax A (Icc a b) F G U)
    (hc : ContinuousOn (F - DG + AG) (Icc a b)) :
    ∀ t ∈ Icc a b, ‖U t - G t‖ ≤ ‖U a - G a‖ + ∫ s in a..t, ‖F s - DG s + AG s‖ := by
  have hW := (isBoundarySolution_iff hle hG).1 hU
  intro t ht
  simpa using hW.norm_le_add_integral hA hc t ht

/-- **A priori bound**: `‖U(t)‖ ≤ ‖G(t)‖ + ‖U(a) − G(a)‖ + ∫ₐᵗ ‖F − G' + A_max G‖`. -/
theorem IsBoundarySolution.norm_le (hle : A ≤ Amax) (hA : A.IsDissipative) {a b : ℝ}
    {DG AG : ℝ → E} (hG : IsLifting Amax (Icc a b) G DG AG)
    (hU : IsBoundarySolution Amax A (Icc a b) F G U)
    (hc : ContinuousOn (F - DG + AG) (Icc a b)) :
    ∀ t ∈ Icc a b, ‖U t‖ ≤ ‖G t‖ + (‖U a - G a‖ + ∫ s in a..t, ‖F s - DG s + AG s‖) := by
  intro t ht
  calc ‖U t‖ = ‖G t + (U t - G t)‖ := by rw [add_sub_cancel]
    _ ≤ ‖G t‖ + ‖U t - G t‖ := norm_add_le _ _
    _ ≤ _ := by gcongr; exact hU.norm_sub_le hle hA hG hc t ht

/-- **Continuous dependence on the initial value, the forcing and the boundary data**: for two
solutions with liftings `G₁`, `G₂` and forcings `F₁`, `F₂`,
`‖(U₁ − G₁)(t) − (U₂ − G₂)(t)‖ ≤ ‖(U₁ − G₁)(a) − (U₂ − G₂)(a)‖ + ∫ₐᵗ ‖Φ₁ − Φ₂‖` with
`Φᵢ = Fᵢ − Gᵢ' + A_max Gᵢ`. -/
theorem IsBoundarySolution.norm_sub_sub_le (hle : A ≤ Amax) (hA : A.IsDissipative) {a b : ℝ}
    {F₁ F₂ G₁ G₂ DG₁ DG₂ AG₁ AG₂ U₁ U₂ : ℝ → E}
    (hG₁ : IsLifting Amax (Icc a b) G₁ DG₁ AG₁) (hG₂ : IsLifting Amax (Icc a b) G₂ DG₂ AG₂)
    (hU₁ : IsBoundarySolution Amax A (Icc a b) F₁ G₁ U₁)
    (hU₂ : IsBoundarySolution Amax A (Icc a b) F₂ G₂ U₂)
    (hc : ContinuousOn ((F₁ - DG₁ + AG₁) - (F₂ - DG₂ + AG₂)) (Icc a b)) :
    ∀ t ∈ Icc a b, ‖(U₁ t - G₁ t) - (U₂ t - G₂ t)‖ ≤ ‖(U₁ a - G₁ a) - (U₂ a - G₂ a)‖ +
      ∫ s in a..t, ‖(F₁ s - DG₁ s + AG₁ s) - (F₂ s - DG₂ s + AG₂ s)‖ := by
  have hW₁ := (isBoundarySolution_iff hle hG₁).1 hU₁
  have hW₂ := (isBoundarySolution_iff hle hG₂).1 hU₂
  exact hW₁.norm_sub_le_add_integral hA hW₂ hc

/-- **Energy identity with boundary flux**: `d/dt ‖U‖² = 2 re ⟪A_max U + F, U⟫` within `I`. The
term `re ⟪A_max U, U⟫` is the boundary flux: it vanishes for skew-symmetric `A` when `U(t)` has
homogeneous boundary values (`re_inner_eq_zero_of_mem_domain`). -/
theorem IsBoundarySolution.hasDerivWithinAt_norm_sq (hU : IsBoundarySolution Amax A I F G U)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivWithinAt (fun s => ‖U s‖ ^ 2)
      (2 * RCLike.re ⟪Amax ⟨U t, hU.toIsStrongSolution.mem_domain ht⟩ + F t, U t⟫) I t :=
  hU.toIsStrongSolution.hasDerivWithinAt_norm_sq ht

omit [NormedSpace ℝ E] in
/-- For skew-symmetric `A ≤ A_max`, the flux `re ⟪A_max x, x⟫` vanishes on `D(A)`. -/
theorem re_inner_eq_zero_of_mem_domain (hle : A ≤ Amax) (hA : A.IsSkewSymmetric)
    (x : Amax.domain) (hx : (x : E) ∈ A.domain) : RCLike.re ⟪Amax x, (x : E)⟫ = 0 := by
  have e : Amax x = A ⟨x, hx⟩ := (hle.2 (x := ⟨x, hx⟩) (y := x) rfl).symm
  rw [e]
  exact hA.re_inner_self ⟨x, hx⟩

/-- **Exact liftings**: if the lifting `G` itself solves `G' = A_max G + F` (e.g. the exact
solution of a test problem, whose traces are prescribed), the solution with the boundary values
of `G` and initial value `G(a)` is `G` itself, and it is the only one. -/
theorem isBoundarySolution_self_unique {a b : ℝ} (hle : A ≤ Amax) (hA : A.IsDissipative)
    (hG : IsStrongSolution Amax (Icc a b) F G) {V : ℝ → E} (hV0 : V a = G a)
    (hV : IsBoundarySolution Amax A (Icc a b) F G V) : EqOn V G (Icc a b) :=
  hV.unique hle hA ⟨hG, fun t _ => by rw [sub_self]; exact A.domain.zero_mem⟩ hV0

/-- The exact lifting is a boundary solution with its own boundary values. -/
theorem isBoundarySolution_self (hG : IsStrongSolution Amax I F G) :
    IsBoundarySolution Amax A I F G G :=
  ⟨hG, fun t _ => by rw [sub_self]; exact A.domain.zero_mem⟩

end General

section Existence

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] {Amax A : E →ₗ.[𝕜] E}
  {F G DG AG : ℝ → E} {a b : ℝ}

/-- **Existence and uniqueness for a semigroup generator** `A ≤ A_max`: for a lifting `G`, an
initial value with `U₀ − G(a) ∈ D(A)` and admissible `F − G' + A_max G`
(`C([a,b]; E) ∩ (W^{1,1} ∪ L¹(D(A)))`), there is a solution `U` of `U' = A_max U + F` with the
boundary values of `G` and `U(a) = U₀`, with `U − G` a classical solution of the homogeneous
problem (Duhamel's formula), and every solution with the same data agrees with it on `[a, b]`.
No dissipativity is needed. -/
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

/-- **Existence and uniqueness for a skew-adjoint `A ≤ A_max`** (Stone's group): the
inhomogeneous boundary value problem `U' = A_max U + F`, `U(t) − G(t) ∈ D(A)`, `U(a) = U₀` with
`U₀ − G(a) ∈ D(A)` and admissible `F − G' + A_max G` has a solution, `U − G` is a classical
solution of the homogeneous problem, and the solution is unique. [QuennevilleBelair2015], Thm 4.3,
extended to inhomogeneous boundary data. -/
theorem existsUnique_isBoundarySolution (hA : A.IsSkewAdjoint) (hle : A ≤ Amax)
    (hG : IsLifting Amax (Icc a b) G DG AG) {U₀ : E} (hU₀ : U₀ - G a ∈ A.domain)
    (hF : ForcingClass.admissible A a b (F - DG + AG)) :
    ∃ U, U a = U₀ ∧ IsBoundarySolution Amax A (Icc a b) F G U ∧
      IsClassicalSolution A (Icc a b) (F - DG + AG) (U - G) ∧
      ∀ V, V a = U₀ → IsBoundarySolution Amax A (Icc a b) F G V → EqOn V U (Icc a b) :=
  hA.group.toC0Semigroup.existsUnique_isBoundarySolution hA.generator_group hle hG hU₀ hF

end Existence

end Feec.Evolution
