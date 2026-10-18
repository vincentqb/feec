module

public import Feec.Domain.Constrained
public import Feec.Domain.Operators
public import Feec.ForMathlib.LinearPMap.Skew

/-!
# Complexes of constrained realizations

A **constrained complex** (`Feec.Domain.ConstrainedComplex`) on an open `Ω ⊆ E` is a complex of
constant-coefficient operators `A k : 𝕜^{ι k} → 𝕜^{ι (k+1)}` (`A (k+1) ∘ A k = 0` on smooth
fields, `Feec.Domain.ConstCoeffComplex`) together with closed subspaces
`V k ⊆ L²(Ω; 𝕜^{ι k})` (symmetric, trace-free, or unconstrained matrix fields, …) such that
the constrained test fields are dense in each `V k` and both `A k` and its formal adjoint map
constrained test fields to constrained test fields. It gives two Hilbert complexes on
`ComplexShape.up ℤ`, mirroring `Feec.Domain.ConstCoeffComplex`:

* the **minimal complex** (`ConstrainedComplex.minimalComplex`), `d k = (A k)_via`, the closure
  of `A k` on the constrained test fields (`Feec.Domain.ConstCoeffOp.minimalVia`), the `H̊`
  boundary conditions;
* the **maximal complex** (`ConstrainedComplex.maximalComplex`), `d k = (A k)_max,via`, the
  adjoint of the minimal realization of the formal adjoint
  (`Feec.Domain.ConstCoeffOp.maximalVia`): the weak realization tested against constrained test
  fields, with no boundary condition (`ConstCoeffOp.mem_maximalVia_domain_iff`);

and the **duality** of the two families: the dual of the minimal complex is the maximal complex
of the formal adjoints and vice versa (`dual_minimalComplex_d`, `dual_maximalComplex_d`). The
minimal operators are restrictions of the maximal ones (`minimalComplex_d_le_maximalComplex_d`).

The constraints of the elasticity, Hessian and div-div complexes are ranges of pointwise
self-adjoint projections `M` (`L2F.matSubmodule`, with density `L2F.denseVia_matSubmodule`): the
symmetric part `symMat` (`L2F.symSubmodule`), the deviatoric part `devMat`
(`L2F.traceFreeSubmodule`) and the identity (`⊤`). The operators of these complexes are built
from those of `Feec.Domain.Operators` by composition (`ConstCoeffOp.comp`) and by pre- and
post-composition with constant matrices (`ConstCoeffOp.preComp`, `ConstCoeffOp.postComp`), with
`(postComp M A)ᵗ = preComp Mᴴ Aᵗ` (`formalAdj_postComp`) and `(B ∘ A)ᵗ = Aᵗ ∘ Bᵗ`
(`formalAdj_comp_apply`).

## Main definitions

* `ConstCoeffOp.preComp`, `ConstCoeffOp.comp`: operator algebra.
* `ConstCoeffOp.maximalVia`: the maximal constrained realization.
* `L2F.matSubmodule`, `L2F.symSubmodule`, `L2F.traceFreeSubmodule`: pointwise constraints.
* `ConstrainedComplex`, `ConstrainedComplex.minimalComplex`, `ConstrainedComplex.maximalComplex`.

No closed-range statement is made: on a general open `Ω` the ranges need not be closed.

## References

* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], §6.2 (the two boundary-condition
  families and their duality)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.1 (dual complexes)
* [D. N. Arnold, K. Hu, *Complexes from complexes*][ArnoldHu2021] (complexes with values in
  subspaces of matrices)
* [J. Brüning, M. Lesch, *Hilbert complexes*][BruningLesch1992] (minimal and maximal ideal boundary
  conditions)
-/

open scoped InnerProductSpace ContDiff ENNReal ComplexConjugate LinearPMap
open MeasureTheory Set Filter Topology

@[expose] public noncomputable section

namespace Feec.Domain

namespace ConstCoeffOp

/-! ## Operator algebra -/

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {𝕜 : Type*} [RCLike 𝕜]
  {ι ι' κ κ' μ : Type*}

theorem applyEntry_fun_sum {α : Type*} (s : Finset α) (c : α → 𝕜) {g : α → E → 𝕜}
    (hg : ∀ a, ContDiff ℝ ∞ (g a)) (P : List (List E × 𝕜)) (x : E) :
    applyEntry P (fun y => ∑ a ∈ s, c a * g a y) x = ∑ a ∈ s, c a * applyEntry P (g a) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact congrFun (applyEntry_zero P) x
  | insert a s ha ih =>
    rw [show (fun y => ∑ b ∈ insert a s, c b * g b y) = c a • g a + fun y => ∑ b ∈ s, c b * g b y
      from funext fun y => by simp [Finset.sum_insert ha],
      applyEntry_add (f := c a • g a) _ ((hg a).const_smul (c a))
        (ContDiff.sum fun b _ => contDiff_const.mul (hg b)),
      applyEntry_smul _ _ (hg a)]
    simp [Finset.sum_insert ha, ih]

/-- `A ∘ M` for a constant matrix `M : 𝕜^{ι'} → 𝕜^ι`, `(M f)ₗ = Σᵢ M l i fᵢ`. -/
def preComp [Fintype ι] (M : ι → ι' → 𝕜) (A : ConstCoeffOp E 𝕜 ι κ) : ConstCoeffOp E 𝕜 ι' κ where
  coeff j i := Finset.univ.toList.flatMap fun l => (A.coeff j l).map fun t => (t.1, M l i * t.2)

theorem preComp_apply [Fintype ι] [Fintype ι'] (M : ι → ι' → 𝕜) (A : ConstCoeffOp E 𝕜 ι κ)
    {f : ι' → E → 𝕜} (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    (A.preComp M).apply f = A.apply fun l x => ∑ i, M l i * f i x := by
  funext j x
  simp only [apply, preComp, applyEntry_flatMap, applyEntry_map_smul]
  simp only [Finset.sum_map_toList, applyEntry_fun_sum _ _ hf]
  exact Finset.sum_comm

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem IsOrderLE.preComp [Fintype ι] {A : ConstCoeffOp E 𝕜 ι κ} {N : ℕ} (h : A.IsOrderLE N)
    (M : ι → ι' → 𝕜) : (A.preComp M).IsOrderLE N := by
  intro j i t ht
  simp only [ConstCoeffOp.preComp, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨l, -, t', ht', rfl⟩ := ht
  exact h j l t' ht'

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem adjEntry_map_mul (c : 𝕜) (P : List (List E × 𝕜)) :
    adjEntry (P.map fun t => (t.1, c * t.2)) = (adjEntry P).map fun t => (t.1, conj c * t.2) := by
  simp only [adjEntry, List.map_map]
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply, map_mul, Prod.mk.injEq, true_and]
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem adjEntry_flatMap {α : Type*} (l : List α) (P : α → List (List E × 𝕜)) :
    adjEntry (l.flatMap P) = l.flatMap fun a => adjEntry (P a) := by
  simp only [adjEntry, List.map_flatMap]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- `(M ∘ A)ᵗ = Aᵗ ∘ Mᴴ`. -/
theorem formalAdj_postComp [Fintype κ] (M : κ' → κ → 𝕜) (A : ConstCoeffOp E 𝕜 ι κ) :
    (A.postComp M).formalAdj = A.formalAdj.preComp fun j j' => conj (M j' j) := by
  simp only [formalAdj, postComp, preComp, adjEntry_flatMap, adjEntry_map_mul]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- `(A ∘ M)ᵗ = Mᴴ ∘ Aᵗ`. -/
theorem formalAdj_preComp [Fintype ι] (M : ι → ι' → 𝕜) (A : ConstCoeffOp E 𝕜 ι κ) :
    (A.preComp M).formalAdj = A.formalAdj.postComp fun i l => conj (M l i) := by
  simp only [formalAdj, postComp, preComp, adjEntry_flatMap, adjEntry_map_mul]

/-- The negative `-A` of a constant-coefficient operator. -/
def negOp (A : ConstCoeffOp E 𝕜 ι κ) : ConstCoeffOp E 𝕜 ι κ where
  coeff j i := (A.coeff j i).map fun t => (t.1, (-1) * t.2)

theorem negOp_apply [Fintype ι] (A : ConstCoeffOp E 𝕜 ι κ) (f : ι → E → 𝕜) :
    A.negOp.apply f = -A.apply f := by
  funext j x
  simp only [apply, negOp, applyEntry_map_smul, Pi.neg_apply, ← Finset.sum_neg_distrib]
  simp

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem formalAdj_negOp (A : ConstCoeffOp E 𝕜 ι κ) : A.negOp.formalAdj = A.formalAdj.negOp := by
  simp only [formalAdj, negOp, adjEntry_map_mul, map_neg, map_one]

/-- The composition `B ∘ A` of constant-coefficient operators. -/
def comp [Fintype κ] (B : ConstCoeffOp E 𝕜 κ μ) (A : ConstCoeffOp E 𝕜 ι κ) :
    ConstCoeffOp E 𝕜 ι μ where
  coeff m i := Finset.univ.toList.flatMap fun j =>
    (B.coeff m j).flatMap fun s => (A.coeff j i).map fun t => (s.1 ++ t.1, s.2 * t.2)

theorem iterDeriv_applyEntry (vs : List E) (P : List (List E × 𝕜)) {g : E → 𝕜}
    (hg : ContDiff ℝ ∞ g) (x : E) :
    iterDeriv vs (applyEntry P g) x = (P.map fun t => t.2 * iterDeriv (vs ++ t.1) g x).sum := by
  induction P with
  | nil => simp [iterDeriv_zero]
  | cons t P ih =>
    have e : applyEntry (t :: P) g = t.2 • iterDeriv t.1 g + applyEntry P g := by
      rw [applyEntry_cons]; rfl
    rw [e, iterDeriv_add (f := t.2 • iterDeriv t.1 g) ((contDiff_iterDeriv hg t.1).const_smul t.2)
        (contDiff_applyEntry _ hg),
      iterDeriv_smul _ (contDiff_iterDeriv hg _), Pi.add_apply, ih]
    simp [iterDeriv_append]

theorem applyEntry_applyEntry (Q P : List (List E × 𝕜)) {g : E → 𝕜} (hg : ContDiff ℝ ∞ g)
    (x : E) : applyEntry Q (applyEntry P g) x =
      applyEntry (Q.flatMap fun s => P.map fun t => (s.1 ++ t.1, s.2 * t.2)) g x := by
  rw [applyEntry_flatMap]
  change (Q.map fun s => s.2 * iterDeriv s.1 (applyEntry P g) x).sum = _
  congr 1
  refine List.map_congr_left fun s _ => ?_
  rw [iterDeriv_applyEntry _ _ hg, ← List.sum_map_mul_left]
  simp only [applyEntry, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply]
  ring

theorem comp_apply [Fintype ι] [Fintype κ] (B : ConstCoeffOp E 𝕜 κ μ) (A : ConstCoeffOp E 𝕜 ι κ)
    {f : ι → E → 𝕜} (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    (B.comp A).apply f = B.apply (A.apply f) := by
  funext m x
  simp only [apply, comp, applyEntry_flatMap, Finset.sum_map_toList]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show A.apply f j = fun y => ∑ i, 1 * applyEntry (A.coeff j i) (f i) y from
      funext fun y => by simp [apply],
    applyEntry_fun_sum _ _ fun i => contDiff_applyEntry _ (hf i)]
  simp [applyEntry_applyEntry _ _ (hf _), applyEntry_flatMap]

theorem _root_.List.sum_map_sum_map_comm {α β M : Type*} [AddCommMonoid M] (l₁ : List α)
    (l₂ : List β) (f : α → β → M) :
    (l₁.map fun a => (l₂.map fun b => f a b).sum).sum =
      (l₂.map fun b => (l₁.map fun a => f a b).sum).sum := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp [ih, List.sum_map_add]

theorem applyEntry_map {α : Type*} (P : List α) (g : α → List E × 𝕜) (f : E → 𝕜) (x : E) :
    applyEntry (P.map g) f x = (P.map fun t => (g t).2 * iterDeriv (g t).1 f x).sum := by
  simp only [applyEntry, List.map_map]
  rfl

/-- **`(B ∘ A)ᵗ = Aᵗ ∘ Bᵗ`** on smooth fields. -/
theorem formalAdj_comp_apply [Fintype ι] [Fintype κ] [Fintype μ] (B : ConstCoeffOp E 𝕜 κ μ)
    (A : ConstCoeffOp E 𝕜 ι κ) {f : μ → E → 𝕜} (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    (B.comp A).formalAdj.apply f = A.formalAdj.apply (B.formalAdj.apply f) := by
  rw [← comp_apply _ _ hf]
  funext i x
  simp only [apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [formalAdj, comp, adjEntry_flatMap, applyEntry_flatMap]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [adjEntry, applyEntry_map, List.map_map, Function.comp_apply]
  rw [List.sum_map_sum_map_comm]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  congr 1
  refine List.map_congr_left fun s _ => ?_
  simp only [List.reverse_append, List.length_append, map_mul, pow_add]
  ring

end Algebra

/-! ## Maximal constrained realizations -/

section Realization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure]
  {𝕜 : Type*} [RCLike 𝕜] {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ] {Ω : Set E}
  {X Y Z : Type*} [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [NormedAddCommGroup Z] [InnerProductSpace 𝕜 Z]
  (A : ConstCoeffOp E 𝕜 ι κ) (Jx : X →ₗᵢ[𝕜] L2F 𝕜 Ω ι) (Jy : Y →ₗᵢ[𝕜] L2F 𝕜 Ω κ)

/-- `A` maps the `X`-valued test fields to `Y`-valued test fields. -/
def MapsToVia : Prop :=
  ∀ (φ : ι → E → 𝕜) (hφ : IsTestField Ω φ) (x : X), Jx x = testField hφ →
    ∃ y : Y, Jy y = testField (A.isTestField_apply hφ)

/-- The **maximal constrained realization** `A_max,via : X → Y`, the adjoint of the constrained
minimal realization of the formal adjoint: `u ∈ D(A_max,via)` iff `A u ∈ Y` weakly, tested
against the `Y`-valued test fields (`mem_maximalVia_domain_iff`), with no boundary condition. -/
def maximalVia [CompleteSpace Y] : X →ₗ.[𝕜] Y := (A.formalAdj.minimalVia Jy Jx)†

variable [CompleteSpace X] [CompleteSpace Y]

omit [FiniteDimensional ℝ E] [CompleteSpace Y] in
/-- **`(A_via)† = (Aᵗ)_max,via`.** -/
theorem adjoint_minimalVia : (A.minimalVia Jx Jy)† = A.formalAdj.maximalVia Jy Jx := by
  rw [maximalVia, formalAdj_formalAdj]

omit [CompleteSpace X] in
theorem isClosed_maximalVia (hX : DenseVia Jx) (hY : DenseVia Jy)
    (hA : A.formalAdj.MapsToVia Jy Jx) : (A.maximalVia Jx Jy).IsClosed :=
  LinearPMap.adjoint_isClosed (A.formalAdj.dense_minimalVia_domain_of Jy Jx hX hY hA)

theorem dense_maximalVia_domain (hX : DenseVia Jx) (hY : DenseVia Jy)
    (hA : A.formalAdj.MapsToVia Jy Jx) : Dense ((A.maximalVia Jx Jy).domain : Set X) :=
  LinearPMap.dense_adjoint_domain _ (A.formalAdj.dense_minimalVia_domain_of Jy Jx hX hY hA)
    (A.formalAdj.isClosed_minimalVia Jy Jx hX)

/-- **`(A_max,via)† = (Aᵗ)_via`** (von Neumann). -/
theorem adjoint_maximalVia (hX : DenseVia Jx) (hY : DenseVia Jy)
    (hA : A.formalAdj.MapsToVia Jy Jx) :
    (A.maximalVia Jx Jy)† = A.formalAdj.minimalVia Jy Jx :=
  LinearPMap.adjoint_adjoint _ (A.formalAdj.dense_minimalVia_domain_of Jy Jx hX hY hA)
    (A.formalAdj.isClosed_minimalVia Jy Jx hX)

omit [CompleteSpace X] in
/-- **The maximal constrained realization is weak**: `u ∈ D(A_max,via)` iff there is `w ∈ Y`
with `⟪w, y⟫ = ⟪u, x⟫` for every pair `(y, x)` with `Jy y = ψ ∈ C_c^∞`, `Jx x = Aᵗ ψ`. -/
theorem mem_maximalVia_domain_iff (hX : DenseVia Jx) (hY : DenseVia Jy)
    (hA : A.formalAdj.MapsToVia Jy Jx) {u : X} :
    u ∈ (A.maximalVia Jx Jy).domain ↔
      ∃ w : Y, ∀ p ∈ A.formalAdj.testGraphVia Jy Jx, ⟪w, p.1⟫_𝕜 = ⟪u, p.2⟫_𝕜 :=
  A.formalAdj.mem_adjoint_minimalVia_domain_iff Jy Jx hX
    (A.formalAdj.dense_minimalVia_domain_of Jy Jx hX hY hA)

omit [CompleteSpace X] in
/-- The value of `A_max,via` is the weak one. -/
theorem maximalVia_apply_eq (hX : DenseVia Jx) (hY : DenseVia Jy)
    (hA : A.formalAdj.MapsToVia Jy Jx) (u : (A.maximalVia Jx Jy).domain) {w : Y}
    (hw : ∀ p ∈ A.formalAdj.testGraphVia Jy Jx, ⟪w, p.1⟫_𝕜 = ⟪(u : X), p.2⟫_𝕜) :
    A.maximalVia Jx Jy u = w :=
  A.formalAdj.adjoint_minimalVia_apply_eq Jy Jx hX
    (A.formalAdj.dense_minimalVia_domain_of Jy Jx hX hY hA) u hw

omit [CompleteSpace X] [CompleteSpace Y] in
/-- Green's formula between the two constrained test graphs. -/
theorem inner_testGraphVia {p : X × Y} (hp : p ∈ A.testGraphVia Jx Jy) {q : Y × X}
    (hq : q ∈ A.formalAdj.testGraphVia Jy Jx) : ⟪p.2, q.1⟫_𝕜 = ⟪p.1, q.2⟫_𝕜 := by
  obtain ⟨φ, hφ, h1, h2⟩ := hp
  obtain ⟨ψ, hψ, h1', h2'⟩ := hq
  rw [← Jy.inner_map_map, ← Jx.inner_map_map, h2, h1', h1, h2']
  exact A.inner_testField_apply_testField hφ hψ

omit [CompleteSpace X] [CompleteSpace Y] in
/-- `A_via` and `(Aᵗ)_via` are formal adjoints. -/
theorem isFormalAdjoint_minimalVia (hX : DenseVia Jx) (hY : DenseVia Jy) :
    (A.minimalVia Jx Jy).IsFormalAdjoint (A.formalAdj.minimalVia Jy Jx) := by
  intro x y
  let S : Set (X × Y) := {p | ⟪p.2, (y : Y)⟫_𝕜 = ⟪p.1, A.formalAdj.minimalVia Jy Jx y⟫_𝕜}
  have hS : IsClosed S := isClosed_eq (continuous_snd.inner continuous_const)
    (continuous_fst.inner continuous_const)
  refine closure_minimal (fun p hp => ?_) hS (A.mem_closure_minimalVia Jx Jy hY x)
  let T : Set (Y × X) := {q | ⟪p.2, q.1⟫_𝕜 = ⟪p.1, q.2⟫_𝕜}
  have hT : IsClosed T := isClosed_eq (continuous_const.inner continuous_fst)
    (continuous_const.inner continuous_snd)
  exact closure_minimal (fun q hq => A.inner_testGraphVia Jx Jy hp hq) hT
    (A.formalAdj.mem_closure_minimalVia Jy Jx hX y)

omit [CompleteSpace X] in
/-- **`A_via ≤ A_max,via`** (`H̊ ⊆ H`). -/
theorem minimalVia_le_maximalVia (hX : DenseVia Jx) (hY : DenseVia Jy)
    (hA : A.formalAdj.MapsToVia Jy Jx) : A.minimalVia Jx Jy ≤ A.maximalVia Jx Jy :=
  (A.isFormalAdjoint_minimalVia Jx Jy hX hY).symm.le_adjoint
    (A.formalAdj.dense_minimalVia_domain_of Jy Jx hX hY hA)

/-! ### Complexes on constrained test fields -/

section Complex

variable {B : ConstCoeffOp E 𝕜 κ μ} (Jz : Z →ₗᵢ[𝕜] L2F 𝕜 Ω μ)

/-- `B A = 0` on the `X`-valued test fields. -/
def IsComplexPairVia (A : ConstCoeffOp E 𝕜 ι κ) (B : ConstCoeffOp E 𝕜 κ μ)
    (Jx : X →ₗᵢ[𝕜] L2F 𝕜 Ω ι) : Prop :=
  ∀ (φ : ι → E → 𝕜) (hφ : IsTestField Ω φ) (x : X), Jx x = testField hφ →
    testField (B.isTestField_apply (A.isTestField_apply hφ)) = 0

omit [FiniteDimensional ℝ E] [Fintype μ] [CompleteSpace X] in
theorem IsComplexPair.isComplexPairVia (hAB : A.IsComplexPair B) : A.IsComplexPairVia B Jx :=
  fun φ hφ _ _ => by
    rw [testField_congr _ IsTestField.zero (hAB φ fun i => (hφ i).contDiff), testField_zero]

omit [CompleteSpace X] [CompleteSpace Y] in
/-- The formal adjoints of a complex pair form a complex pair on test fields. -/
theorem IsComplexPair.isComplexPairVia_formalAdj (hΩ : IsOpen Ω) (hAB : A.IsComplexPair B) :
    B.formalAdj.IsComplexPairVia A.formalAdj Jz :=
  fun _ hψ _ _ => formalAdj_comp_testField hΩ hAB hψ

omit [CompleteSpace X] [CompleteSpace Y] in
/-- `R(A_via) ⊆ D(B_via)` and `B_via A_via = 0` when `B A = 0` on the `X`-valued test fields. -/
theorem minimalVia_graph_mem_of_isComplexPairVia (hAB : A.IsComplexPairVia B Jx)
    (hY : DenseVia Jy) (hZ : DenseVia Jz) (x : (A.minimalVia Jx Jy).domain) :
    (A.minimalVia Jx Jy x, (0 : Z)) ∈ (B.minimalVia Jy Jz).graph := by
  let S : Set (X × Y) := {p | (p.2, (0 : Z)) ∈ (B.minimalVia Jy Jz).graph}
  have hS : IsClosed S :=
    (B.isClosed_minimalVia Jy Jz hZ).preimage (continuous_snd.prodMk continuous_const)
  have hsub : (A.testGraphVia Jx Jy : Set (X × Y)) ⊆ S := by
    rintro ⟨x', y'⟩ ⟨φ, hφ, h1, h2⟩
    refine B.mem_graph_minimalVia Jy Jz hZ ⟨A.apply φ, A.isTestField_apply hφ, h2, ?_⟩
    rw [map_zero, hAB φ hφ x' h1]
  exact closure_minimal hsub hS (A.mem_closure_minimalVia Jx Jy hY x)

omit [CompleteSpace X] [CompleteSpace Y] in
theorem minimalVia_mapsTo_of_isComplexPairVia (hAB : A.IsComplexPairVia B Jx)
    (hY : DenseVia Jy) (hZ : DenseVia Jz) (x : (A.minimalVia Jx Jy).domain) :
    (A.minimalVia Jx Jy x : Y) ∈ (B.minimalVia Jy Jz).domain :=
  LinearPMap.mem_domain_of_mem_graph (minimalVia_graph_mem_of_isComplexPairVia A Jx Jy Jz hAB hY hZ x)

omit [CompleteSpace X] [CompleteSpace Y] in
theorem minimalVia_comp_of_isComplexPairVia (hAB : A.IsComplexPairVia B Jx)
    (hY : DenseVia Jy) (hZ : DenseVia Jz) (x : (A.minimalVia Jx Jy).domain) :
    B.minimalVia Jy Jz ⟨_, minimalVia_mapsTo_of_isComplexPairVia A Jx Jy Jz hAB hY hZ x⟩ = 0 :=
  ((LinearPMap.image_iff _).2 (minimalVia_graph_mem_of_isComplexPairVia A Jx Jy Jz hAB hY hZ x)).symm

end Complex

/-! ### Congruence -/

omit [FiniteDimensional ℝ E] [CompleteSpace X] [CompleteSpace Y] in
/-- Operators agreeing on the `X`-valued test fields have the same constrained test graph. -/
theorem testGraphVia_congr {A' : ConstCoeffOp E 𝕜 ι κ}
    (h : ∀ (φ : ι → E → 𝕜) (hφ : IsTestField Ω φ) (x : X), Jx x = testField hφ →
      testField (A'.isTestField_apply hφ) = testField (A.isTestField_apply hφ)) :
    A'.testGraphVia Jx Jy = A.testGraphVia Jx Jy := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨φ, hφ, h1, h2⟩
    exact ⟨φ, hφ, h1, by rw [h2, h φ hφ x h1]⟩
  · rintro ⟨φ, hφ, h1, h2⟩
    exact ⟨φ, hφ, h1, by rw [h2, h φ hφ x h1]⟩

omit [FiniteDimensional ℝ E] [CompleteSpace X] [CompleteSpace Y] in
/-- Operators agreeing on the `X`-valued test fields have the same constrained realization. -/
theorem minimalVia_congr {A' : ConstCoeffOp E 𝕜 ι κ}
    (h : ∀ (φ : ι → E → 𝕜) (hφ : IsTestField Ω φ) (x : X), Jx x = testField hφ →
      testField (A'.isTestField_apply hφ) = testField (A.isTestField_apply hφ)) :
    A'.minimalVia Jx Jy = A.minimalVia Jx Jy := by
  rw [minimalVia, minimalVia, testGraphVia_congr A Jx Jy h]

omit [FiniteDimensional ℝ E] [CompleteSpace X] in
/-- Operators whose formal adjoints agree on the `Y`-valued test fields have the same maximal
constrained realization. -/
theorem maximalVia_congr {A' : ConstCoeffOp E 𝕜 ι κ}
    (h : ∀ (ψ : κ → E → 𝕜) (hψ : IsTestField Ω ψ) (y : Y), Jy y = testField hψ →
      testField (A'.formalAdj.isTestField_apply hψ) = testField (A.formalAdj.isTestField_apply hψ)) :
    A'.maximalVia Jx Jy = A.maximalVia Jx Jy := by
  rw [maximalVia, maximalVia, minimalVia_congr A.formalAdj Jy Jx h]

omit [CompleteSpace X] [CompleteSpace Y] in
/-- An operator acting as `-A` on the `X`-valued test fields has the realization `-A_via`. -/
theorem minimalVia_eq_neg (hY : DenseVia Jy) {A' : ConstCoeffOp E 𝕜 ι κ}
    (h : ∀ (φ : ι → E → 𝕜) (hφ : IsTestField Ω φ) (x : X), Jx x = testField hφ →
      testField (A'.isTestField_apply hφ) = -testField (A.isTestField_apply hφ)) :
    A'.minimalVia Jx Jy = -A.minimalVia Jx Jy := by
  let N : X × Y ≃ₜ X × Y := (Homeomorph.refl X).prodCongr (Homeomorph.neg Y)
  have hG : (A'.testGraphVia Jx Jy : Set (X × Y)) = N '' (A.testGraphVia Jx Jy : Set (X × Y)) := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨φ, hφ, h1, h2⟩
      refine ⟨(x, -y), ⟨φ, hφ, h1, ?_⟩, by simp [N]⟩
      simp only [map_neg, h2, h φ hφ x h1, neg_neg]
    · rintro ⟨⟨x', y'⟩, ⟨φ, hφ, h1, h2⟩, he⟩
      change (x', -y') = (x, y) at he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ⟨φ, hφ, h1, by simp [h2, h φ hφ x' h1]⟩
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.neg_graph, A'.minimalVia_graph Jx Jy hY, A.minimalVia_graph Jx Jy hY]
  apply SetLike.coe_injective
  rw [Submodule.topologicalClosure_coe, Submodule.map_coe, Submodule.topologicalClosure_coe, hG,
    ← N.image_closure]
  rfl

omit [CompleteSpace X] in
/-- An operator whose formal adjoint acts as `-Aᵗ` on the `Y`-valued test fields has the maximal
realization `-A_max,via`. -/
theorem maximalVia_eq_neg (hX : DenseVia Jx) (hY : DenseVia Jy)
    (hA : A.formalAdj.MapsToVia Jy Jx) {A' : ConstCoeffOp E 𝕜 ι κ}
    (h : ∀ (ψ : κ → E → 𝕜) (hψ : IsTestField Ω ψ) (y : Y), Jy y = testField hψ →
      testField (A'.formalAdj.isTestField_apply hψ) = -testField (A.formalAdj.isTestField_apply hψ)) :
    A'.maximalVia Jx Jy = -A.maximalVia Jx Jy := by
  rw [maximalVia, maximalVia, A.formalAdj.minimalVia_eq_neg Jy Jx hX h,
    LinearPMap.adjoint_neg _ (A.formalAdj.dense_minimalVia_domain_of Jy Jx hX hY hA)]

omit [CompleteSpace X] [CompleteSpace Y] in
theorem minimalVia_negOp (hY : DenseVia Jy) : A.negOp.minimalVia Jx Jy = -A.minimalVia Jx Jy :=
  A.minimalVia_eq_neg Jx Jy hY fun φ hφ _ _ => by
    rw [testField_congr _ ((A.isTestField_apply hφ).smul (-1 : 𝕜))
      (by rw [negOp_apply]; funext j x; simp), testField_smul, neg_one_smul]

omit [CompleteSpace X] in
theorem maximalVia_negOp (hX : DenseVia Jx) (hY : DenseVia Jy)
    (hA : A.formalAdj.MapsToVia Jy Jx) : A.negOp.maximalVia Jx Jy = -A.maximalVia Jx Jy :=
  A.maximalVia_eq_neg Jx Jy hX hY hA fun ψ hψ _ _ => by
    rw [testField_congr _ ((A.formalAdj.isTestField_apply hψ).smul (-1 : 𝕜))
      (by rw [formalAdj_negOp, negOp_apply]; funext j x; simp), testField_smul, neg_one_smul]

end Realization

/-! ## The zero operator and empty components -/

section Zero

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {𝕜 : Type*} [RCLike 𝕜]
  {ι κ : Type*} [Fintype ι]

/-- The zero operator. -/
def zeroOp (ι κ : Type*) : ConstCoeffOp E 𝕜 ι κ := ⟨fun _ _ => []⟩

theorem zeroOp_apply (f : ι → E → 𝕜) : (zeroOp ι κ : ConstCoeffOp E 𝕜 ι κ).apply f = 0 := by
  funext j x
  simp [zeroOp, apply, applyEntry]

theorem apply_of_isEmpty [IsEmpty ι] (A : ConstCoeffOp E 𝕜 ι κ) (f : ι → E → 𝕜) :
    A.apply f = 0 := by
  funext j x
  simp [apply]

end Zero

end ConstCoeffOp

/-! ## Pointwise matrix constraints -/

section Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {𝕜 : Type*} [RCLike 𝕜]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The pointwise action `(M φ)ᵢ = Σⱼ M i j φⱼ` of a constant matrix on a field. -/
def matMulField (M : ι → ι → 𝕜) (φ : ι → E → 𝕜) : ι → E → 𝕜 := fun i x => ∑ j, M i j * φ j x

theorem contDiff_matMulField (M : ι → ι → 𝕜) {φ : ι → E → 𝕜} (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (i : ι) : ContDiff ℝ ∞ (matMulField M φ i) :=
  ContDiff.sum fun j _ => contDiff_const.mul (hφ j)

theorem IsTestField.matMulField {Ω : Set E} (M : ι → ι → 𝕜) {φ : ι → E → 𝕜}
    (hφ : IsTestField Ω φ) : IsTestField Ω (matMulField M φ) := fun _ =>
  IsTest.sum _ fun j _ => (hφ j).const_mul _

/-- A constant matrix is an **orthogonal projection**: idempotent and self-adjoint. -/
structure IsProjMat (M : ι → ι → 𝕜) : Prop where
  idem : ∀ i k, ∑ j, M i j * M j k = M i k
  selfAdj : ∀ i j, M j i = conj (M i j)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem IsProjMat.matMulField_matMulField {M : ι → ι → 𝕜} (hM : IsProjMat M) (φ : ι → E → 𝕜) :
    matMulField M (matMulField M φ) = matMulField M φ := by
  funext i x
  simp only [matMulField, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_mul, hM.idem]

theorem ConstCoeffOp.postComp_apply_eq_matMulField (M : κ → κ → 𝕜) (A : ConstCoeffOp E 𝕜 ι κ)
    (f : ι → E → 𝕜) : (A.postComp M).apply f = matMulField M (A.apply f) := by
  funext j x
  exact ConstCoeffOp.postComp_apply M A f j x

omit [Fintype κ] in
theorem ConstCoeffOp.preComp_apply_eq_matMulField (M : ι → ι → 𝕜) (A : ConstCoeffOp E 𝕜 ι κ)
    {f : ι → E → 𝕜} (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    (A.preComp M).apply f = A.apply (matMulField M f) :=
  ConstCoeffOp.preComp_apply M A hf

variable [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] {Ω : Set E}

namespace L2F

/-- A field-level continuous linear map assembled from a constant matrix. -/
def matCLM (M : ι → ι → 𝕜) : L2F 𝕜 Ω ι →L[𝕜] L2F 𝕜 Ω ι :=
  (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => L2 𝕜 Ω)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => ∑ j, M i j • PiLp.proj 2 (fun _ : ι => L2 𝕜 Ω) j)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem matCLM_apply (M : ι → ι → 𝕜) (u : L2F 𝕜 Ω ι) (i : ι) :
    matCLM M u i = ∑ j, M i j • u j := by
  simp [matCLM]

/-- `matCLM` acts pointwise on test fields. -/
theorem matCLM_testField (M : ι → ι → 𝕜) {φ : ι → E → 𝕜} (hφ : IsTestField Ω φ) :
    matCLM M (testField hφ) = testField (hφ.matMulField M) := by
  refine (WithLp.ext_iff 2).2 (funext fun i => Lp.ext ?_)
  rw [matCLM_apply]
  have h1 := Lp.coeFn_fun_finsetSum (μ := volume.restrict Ω) Finset.univ
    (fun j => M i j • testField hφ j)
  filter_upwards [h1, coeFn_testField (hφ.matMulField M) i,
    ae_all_iff.2 fun j => Lp.coeFn_smul (M i j) (testField hφ j),
    ae_all_iff.2 fun j => coeFn_testField hφ j] with x h1 h2 h3 h4
  rw [h1, h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h3 j, Pi.smul_apply, h4 j, smul_eq_mul]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem inner_matCLM (M : ι → ι → 𝕜) (hM : ∀ i j, M j i = conj (M i j)) (u v : L2F 𝕜 Ω ι) :
    ⟪matCLM M u, v⟫_𝕜 = ⟪u, matCLM M v⟫_𝕜 := by
  rw [L2F.inner_def, L2F.inner_def]
  simp only [matCLM_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hM]
  simp

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem matCLM_matCLM {M : ι → ι → 𝕜} (hM : IsProjMat M) (u : L2F 𝕜 Ω ι) :
    matCLM M (matCLM M u) = matCLM M u := by
  refine (WithLp.ext_iff 2).2 (funext fun i => ?_)
  simp only [matCLM_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_smul, hM.idem]

variable (𝕜 Ω) in
/-- The fields with values in the range of the constant matrix `M` (for a projection `M`):
`{u | M u = u}`. -/
def matSubmodule (M : ι → ι → 𝕜) : Submodule 𝕜 (L2F 𝕜 Ω ι) :=
  LinearMap.ker ((matCLM M - ContinuousLinearMap.id 𝕜 (L2F 𝕜 Ω ι) : L2F 𝕜 Ω ι →L[𝕜] L2F 𝕜 Ω ι) :
    L2F 𝕜 Ω ι →ₗ[𝕜] L2F 𝕜 Ω ι)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem mem_matSubmodule {M : ι → ι → 𝕜} {u : L2F 𝕜 Ω ι} :
    u ∈ matSubmodule 𝕜 Ω M ↔ matCLM M u = u := by
  simp [matSubmodule, sub_eq_zero]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem isClosed_matSubmodule (M : ι → ι → 𝕜) :
    IsClosed (matSubmodule 𝕜 Ω M : Set (L2F 𝕜 Ω ι)) :=
  ContinuousLinearMap.isClosed_ker _

instance (M : ι → ι → 𝕜) : CompleteSpace (matSubmodule 𝕜 Ω M) :=
  (isClosed_matSubmodule M).completeSpace_coe

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem matCLM_mem {M : ι → ι → 𝕜} (hM : IsProjMat M) (u : L2F 𝕜 Ω ι) :
    matCLM M u ∈ matSubmodule 𝕜 Ω M :=
  mem_matSubmodule.2 (matCLM_matCLM hM u)

/-- A test field with values in the range of `M` lies in `matSubmodule M`. -/
theorem testField_mem_matSubmodule {M : ι → ι → 𝕜} {φ : ι → E → 𝕜} (hφ : IsTestField Ω φ)
    (h : matMulField M φ = φ) : testField hφ ∈ matSubmodule 𝕜 Ω M := by
  rw [mem_matSubmodule, matCLM_testField]
  exact testField_congr _ _ h

/-- A test field in `matSubmodule M` agrees in `L²` with its pointwise projection. -/
theorem testField_eq_of_mem_matSubmodule {M : ι → ι → 𝕜} {φ : ι → E → 𝕜} (hφ : IsTestField Ω φ)
    (h : testField hφ ∈ matSubmodule 𝕜 Ω M) : testField hφ = testField (hφ.matMulField M) := by
  rw [← matCLM_testField M hφ, mem_matSubmodule.1 h]

/-- **The test fields with values in the range of a projection are dense in
`matSubmodule M`.** -/
theorem denseVia_matSubmodule [FiniteDimensional ℝ E] (hΩ : IsOpen Ω) {M : ι → ι → 𝕜}
    (hM : IsProjMat M) : ConstCoeffOp.DenseVia (matSubmodule 𝕜 Ω M).subtypeₗᵢ :=
  ConstCoeffOp.denseVia_of_proj hΩ _ (matCLM M) (fun y => mem_matSubmodule.1 y.2)
    (inner_matCLM M hM.selfAdj) fun _ hψ =>
      ⟨_, hψ.matMulField M, ⟨_, matCLM_mem hM (testField hψ)⟩, matCLM_testField M hψ,
        matCLM_testField M hψ⟩

end L2F

/-- `A` maps fields with values in the range of `M` to fields with values in the range of
`N`: `N (A (M φ)) = A (M φ)` for smooth `φ`. -/
def ConstCoeffOp.MatMapsTo (A : ConstCoeffOp E 𝕜 ι κ) (M : ι → ι → 𝕜) (N : κ → κ → 𝕜) : Prop :=
  ∀ φ : ι → E → 𝕜, (∀ i, ContDiff ℝ ∞ (φ i)) →
    matMulField N (A.apply (matMulField M φ)) = A.apply (matMulField M φ)

omit [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
/-- `N ∘ A` maps everything to the range of an idempotent `N`. -/
theorem ConstCoeffOp.matMapsTo_postComp (A : ConstCoeffOp E 𝕜 ι κ) (M : ι → ι → 𝕜)
    {N : κ → κ → 𝕜} (hN : IsProjMat N) : (A.postComp N).MatMapsTo M N := fun φ _ => by
  rw [ConstCoeffOp.postComp_apply_eq_matMulField, hN.matMulField_matMulField]

omit [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
theorem ConstCoeffOp.matMapsTo_of_isEmpty_left [IsEmpty ι] (A : ConstCoeffOp E 𝕜 ι κ)
    (M : ι → ι → 𝕜) (N : κ → κ → 𝕜) : A.MatMapsTo M N := fun φ _ => by
  rw [A.apply_of_isEmpty]
  funext j x
  simp [matMulField]

omit [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
theorem ConstCoeffOp.matMapsTo_of_isEmpty_right [IsEmpty κ] (A : ConstCoeffOp E 𝕜 ι κ)
    (M : ι → ι → 𝕜) (N : κ → κ → 𝕜) : A.MatMapsTo M N := fun _ _ =>
  funext fun j => isEmptyElim j

omit [Fintype ι] in
theorem testField_neg {φ : ι → E → 𝕜} (hφ : IsTestField Ω φ) (hφ' : IsTestField Ω (-φ)) :
    testField hφ' = -testField hφ := by
  rw [testField_congr hφ' (hφ.smul (-1 : 𝕜)) (by funext i x; simp), testField_smul, neg_one_smul]

omit [Fintype κ] in
theorem ConstCoeffOp.testField_apply_eq_neg {A A' : ConstCoeffOp E 𝕜 ι κ} {φ : ι → E → 𝕜}
    (hφ : IsTestField Ω φ) (h : A'.apply φ = -A.apply φ) :
    testField (A'.isTestField_apply hφ) = -testField (A.isTestField_apply hφ) := by
  have h' : IsTestField Ω (-A.apply φ) := h ▸ A'.isTestField_apply hφ
  rw [testField_congr _ h' h, testField_neg]

/-- Equal test fields have equal images. -/
theorem ConstCoeffOp.testField_apply_congr [FiniteDimensional ℝ E] (hΩ : IsOpen Ω)
    (A : ConstCoeffOp E 𝕜 ι κ) {φ ψ : ι → E → 𝕜} (hφ : IsTestField Ω φ) (hψ : IsTestField Ω ψ)
    (h : testField hφ = testField hψ) :
    testField (A.isTestField_apply hφ) = testField (A.isTestField_apply hψ) := by
  rw [← A.minimal_testField hΩ hφ, ← A.minimal_testField hΩ hψ]
  congr 1
  exact Subtype.ext h

/-- **Pointwise mapping of the constraints gives `MapsToVia`.** -/
theorem ConstCoeffOp.MatMapsTo.mapsToVia [FiniteDimensional ℝ E] (hΩ : IsOpen Ω)
    {A : ConstCoeffOp E 𝕜 ι κ} {M : ι → ι → 𝕜} {N : κ → κ → 𝕜} (h : A.MatMapsTo M N) :
    A.MapsToVia (L2F.matSubmodule 𝕜 Ω M).subtypeₗᵢ (L2F.matSubmodule 𝕜 Ω N).subtypeₗᵢ := by
  intro φ hφ x hx
  have hx' : testField hφ ∈ L2F.matSubmodule 𝕜 Ω M := by rw [← hx]; exact x.2
  have e := A.testField_apply_congr hΩ hφ (hφ.matMulField M)
    (L2F.testField_eq_of_mem_matSubmodule hφ hx')
  refine ⟨⟨testField (A.isTestField_apply hφ), ?_⟩, rfl⟩
  rw [e]
  exact L2F.testField_mem_matSubmodule _ (h φ fun i => (hφ i).contDiff)

/-! ### The identity, symmetric and deviatoric projections -/

section Projections

omit [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- The identity matrix (no constraint). -/
def idMat (ι : Type*) [DecidableEq ι] : ι → ι → 𝕜 := fun i j => if i = j then 1 else 0

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem matMulField_idMat [DecidableEq ι] (φ : ι → E → 𝕜) : matMulField (idMat ι) φ = φ := by
  funext i x
  simp [matMulField, idMat]

theorem isProjMat_idMat [DecidableEq ι] : IsProjMat (idMat ι : ι → ι → 𝕜) where
  idem i k := by simp [idMat]
  selfAdj i j := by
    simp only [idMat, eq_comm (a := j)]
    split_ifs <;> simp

variable {n : ℕ}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem sum_symMat_mul (ij : Fin n × Fin n) (g : Fin n × Fin n → 𝕜) :
    ∑ kl, symMat n ij kl * g kl = (g ij + g (ij.2, ij.1)) / 2 := by
  simp only [symMat, add_div, add_mul, Finset.sum_add_distrib, div_mul_eq_mul_div, ite_mul,
    one_mul, zero_mul, ite_div, zero_div, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem symMat_swap (ij kl : Fin n × Fin n) :
    (symMat n ij kl : 𝕜) = symMat n (ij.2, ij.1) kl := by
  simp only [symMat, Prod.mk.eta]
  rw [add_comm (if kl = (ij.2, ij.1) then (1 : 𝕜) else 0)]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem matMulField_symMat (φ : Fin n × Fin n → E → 𝕜) (ij : Fin n × Fin n) (x : E) :
    matMulField (symMat n) φ ij x = (φ ij x + φ (ij.2, ij.1) x) / 2 :=
  sum_symMat_mul ij fun kl => φ kl x

theorem isProjMat_symMat : IsProjMat (symMat n : _ → _ → 𝕜) where
  idem ij kl := by
    rw [sum_symMat_mul ij fun j => symMat n j kl, ← symMat_swap]
    ring
  selfAdj ij kl := by
    simp only [symMat, map_div₀, map_add, apply_ite (starRingEnd 𝕜), map_one, map_zero,
      map_ofNat]
    congr 2
    · exact if_congr eq_comm rfl rfl
    · exact if_congr ⟨fun h => by rw [h], fun h => by rw [h]⟩ rfl rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- `sym φ = ½ (φ + φᵀ)`. -/
theorem matMulField_symMat_eq (φ : Fin n × Fin n → E → 𝕜) :
    matMulField (symMat n) φ = (1 / 2 : 𝕜) • (φ + fun ij => φ (ij.2, ij.1)) := by
  funext ij x
  rw [matMulField_symMat]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem matMulField_neg (M : ι → ι → 𝕜) (φ : ι → E → 𝕜) :
    matMulField M (-φ) = -matMulField M φ := by
  funext i x
  simp [matMulField, Finset.sum_neg_distrib]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem matMulField_symMat_of_symm {φ : Fin n × Fin n → E → 𝕜}
    (h : ∀ i j, φ (i, j) = φ (j, i)) : matMulField (symMat n) φ = φ := by
  funext ij x
  rw [matMulField_symMat, ← h ij.1 ij.2]
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem matMulField_symMat_symm (φ : Fin n × Fin n → E → 𝕜) (i j : Fin n) :
    matMulField (symMat n) φ (i, j) = matMulField (symMat n) φ (j, i) := by
  funext x
  rw [matMulField_symMat, matMulField_symMat, add_comm]

variable (n) in
/-- The deviatoric part `B ↦ B - (tr B / n) I` as a constant matrix on `𝕜^{n×n}`. -/
def deviatoricMat : Fin n × Fin n → Fin n × Fin n → 𝕜 := fun ij kl =>
  (if kl = ij then 1 else 0) - (if ij.1 = ij.2 ∧ kl.1 = kl.2 then (n : 𝕜)⁻¹ else 0)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem sum_deviatoricMat_mul (ij : Fin n × Fin n) (g : Fin n × Fin n → 𝕜) :
    ∑ kl, deviatoricMat n ij kl * g kl =
      g ij - if ij.1 = ij.2 then (n : 𝕜)⁻¹ * ∑ k, g (k, k) else 0 := by
  simp only [deviatoricMat, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  split_ifs with h
  · rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [h, Finset.sum_ite_eq]
  · simp [h]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem matMulField_deviatoricMat (φ : Fin n × Fin n → E → 𝕜) (ij : Fin n × Fin n) (x : E) :
    matMulField (deviatoricMat n) φ ij x =
      φ ij x - if ij.1 = ij.2 then (n : 𝕜)⁻¹ * ∑ k, φ (k, k) x else 0 :=
  sum_deviatoricMat_mul ij fun kl => φ kl x

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem matMulField_deviatoricMat_of_trace {φ : Fin n × Fin n → E → 𝕜}
    (h : ∀ x, ∑ k, φ (k, k) x = 0) : matMulField (deviatoricMat n) φ = φ := by
  funext ij x
  rw [matMulField_deviatoricMat, h x]
  simp

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem sum_diag_sub_trace [NeZero n] (g : Fin n × Fin n → 𝕜) :
    ∑ k, (g (k, k) - (n : 𝕜)⁻¹ * ∑ m, g (m, m)) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.2 (NeZero.ne n)), one_mul, sub_self]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem trace_matMulField_deviatoricMat [NeZero n] (φ : Fin n × Fin n → E → 𝕜) (x : E) :
    ∑ k, matMulField (deviatoricMat n) φ (k, k) x = 0 := by
  simp only [matMulField_deviatoricMat, ite_true]
  exact sum_diag_sub_trace fun kl => φ kl x

theorem isProjMat_deviatoricMat [NeZero n] : IsProjMat (deviatoricMat n : _ → _ → 𝕜) where
  idem ij kl := by
    rw [sum_deviatoricMat_mul ij fun j => deviatoricMat n j kl]
    have h0 : ∑ k, (deviatoricMat n (k, k) kl : 𝕜) = 0 := by
      have e : ∀ k, (deviatoricMat n (k, k) kl : 𝕜) =
          ∑ j, deviatoricMat n (k, k) j * (if j = kl then 1 else 0) := fun k => by simp
      simp only [e, sum_deviatoricMat_mul (𝕜 := 𝕜), ite_true]
      exact sum_diag_sub_trace (𝕜 := 𝕜) (n := n) fun j => if j = kl then 1 else 0
    rw [h0]
    simp
  selfAdj ij kl := by
    simp only [deviatoricMat, map_sub, apply_ite (starRingEnd 𝕜), map_one, map_zero, map_inv₀,
      map_natCast]
    congr 1
    · exact if_congr eq_comm rfl rfl
    · exact if_congr and_comm rfl rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem sum_symMat_smul {W : Type*} [AddCommGroup W] [Module 𝕜 W] (ij : Fin n × Fin n)
    (g : Fin n × Fin n → W) :
    ∑ kl, (symMat n ij kl : 𝕜) • g kl = (2⁻¹ : 𝕜) • (g ij + g (ij.2, ij.1)) := by
  simp only [symMat, div_eq_inv_mul, mul_smul, add_smul, ite_smul, one_smul, zero_smul,
    ← Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem sum_deviatoricMat_smul {W : Type*} [AddCommGroup W] [Module 𝕜 W] (ij : Fin n × Fin n)
    (g : Fin n × Fin n → W) :
    ∑ kl, (deviatoricMat n ij kl : 𝕜) • g kl =
      g ij - if ij.1 = ij.2 then (n : 𝕜)⁻¹ • ∑ k, g (k, k) else 0 := by
  simp only [deviatoricMat, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  split_ifs with h
  · rw [Fintype.sum_prod_type, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [h, Finset.sum_ite_eq]
  · simp [h]

end Projections

namespace L2F

variable (𝕜 Ω) (n : ℕ)

/-- `L²(Ω; S)`: the symmetric matrix fields (`mem_symSubmodule`). -/
abbrev symSubmodule : Submodule 𝕜 (L2F 𝕜 Ω (Fin n × Fin n)) := matSubmodule 𝕜 Ω (symMat n)

/-- `L²(Ω; T)`: the trace-free matrix fields (`mem_traceFreeSubmodule`). -/
abbrev traceFreeSubmodule : Submodule 𝕜 (L2F 𝕜 Ω (Fin n × Fin n)) :=
  matSubmodule 𝕜 Ω (deviatoricMat n)

variable {𝕜 Ω n}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem mem_symSubmodule {u : L2F 𝕜 Ω (Fin n × Fin n)} :
    u ∈ symSubmodule 𝕜 Ω n ↔ ∀ i j, u (i, j) = u (j, i) := by
  rw [mem_matSubmodule, WithLp.ext_iff]
  simp only [funext_iff, matCLM_apply, sum_symMat_smul]
  constructor
  · intro h i j
    have h1 := h (i, j)
    have h2 := h (j, i)
    simp only at h1 h2
    exact h1.symm.trans ((congrArg _ (add_comm _ _)).trans h2)
  · intro h ij
    change (2⁻¹ : 𝕜) • (u ij + u (ij.2, ij.1)) = u ij
    rw [← h ij.1 ij.2, ← two_smul 𝕜, smul_smul]
    norm_num

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem mem_traceFreeSubmodule [NeZero n] {u : L2F 𝕜 Ω (Fin n × Fin n)} :
    u ∈ traceFreeSubmodule 𝕜 Ω n ↔ ∑ k, u (k, k) = 0 := by
  rw [mem_matSubmodule, WithLp.ext_iff]
  simp only [funext_iff, matCLM_apply, sum_deviatoricMat_smul]
  constructor
  · intro h
    have h0 := h (0, 0)
    simp only [ite_true, sub_eq_self] at h0
    exact (smul_eq_zero.1 h0).resolve_left (inv_ne_zero (Nat.cast_ne_zero.2 (NeZero.ne n)))
  · intro h ij
    change u ij - _ = u ij
    rw [h, smul_zero, ite_self, sub_zero]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- No constraint: `matSubmodule 1 = ⊤`. -/
theorem matSubmodule_idMat {ι : Type*} [Fintype ι] [DecidableEq ι] :
    matSubmodule 𝕜 Ω (idMat ι) = ⊤ := by
  refine eq_top_iff.2 fun u _ => mem_matSubmodule.2 ((WithLp.ext_iff 2).2 (funext fun i => ?_))
  simp [matCLM_apply, idMat]

end L2F

omit [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
theorem ConstCoeffOp.matMapsTo_idMat [DecidableEq κ] (A : ConstCoeffOp E 𝕜 ι κ)
    (M : ι → ι → 𝕜) : A.MatMapsTo M (idMat κ) := fun _ _ => matMulField_idMat _

end Matrix

/-! ## Constrained complexes -/

section Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] {𝕜 : Type*} [RCLike 𝕜]

variable (E 𝕜) in
/-- A **complex of constrained realizations** on `Ω`: a complex of constant-coefficient operators
`A k : 𝕜^{ι k} → 𝕜^{ι (k+1)}` (`A (k+1) ∘ A k = 0` on smooth fields) with closed subspaces
`V k ⊆ L²(Ω; 𝕜^{ι k})` in which the constrained test fields are dense, mapped to each other by
the `A k` and by their formal adjoints. -/
structure ConstrainedComplex (Ω : Set E) where
  /-- the underlying complex of constant-coefficient operators -/
  toConstCoeffComplex : ConstCoeffComplex E 𝕜
  /-- the constraint subspaces -/
  V : ∀ k, Submodule 𝕜 (L2F 𝕜 Ω (toConstCoeffComplex.ι k))
  isClosed : ∀ k, IsClosed (V k : Set (L2F 𝕜 Ω (toConstCoeffComplex.ι k)))
  denseVia : ∀ k, ConstCoeffOp.DenseVia (V k).subtypeₗᵢ
  mapsTo : ∀ k, (toConstCoeffComplex.A k).MapsToVia (V k).subtypeₗᵢ (V (k + 1)).subtypeₗᵢ
  mapsTo_formalAdj : ∀ k,
    (toConstCoeffComplex.A k).formalAdj.MapsToVia (V (k + 1)).subtypeₗᵢ (V k).subtypeₗᵢ

namespace ConstrainedComplex

variable {Ω : Set E} (K : ConstrainedComplex E 𝕜 Ω)

/-- The component index types. -/
abbrev ι (k : ℤ) : Type := K.toConstCoeffComplex.ι k

/-- The operators. -/
abbrev A (k : ℤ) : ConstCoeffOp E 𝕜 (K.ι k) (K.ι (k + 1)) := K.toConstCoeffComplex.A k

/-- The isometric embeddings `V k ↪ L²(Ω; 𝕜^{ι k})`. -/
abbrev J (k : ℤ) : K.V k →ₗᵢ[𝕜] L2F 𝕜 Ω (K.ι k) := (K.V k).subtypeₗᵢ

instance (k : ℤ) : CompleteSpace (K.V k) := (K.isClosed k).completeSpace_coe

theorem dense_minimalVia (k : ℤ) : Dense (((K.A k).minimalVia (K.J k) (K.J (k + 1))).domain :
    Set (K.V k)) :=
  (K.A k).dense_minimalVia_domain_of _ _ (K.denseVia (k + 1)) (K.denseVia k) (K.mapsTo k)

theorem dense_formalAdj_minimalVia (k : ℤ) :
    Dense (((K.A k).formalAdj.minimalVia (K.J (k + 1)) (K.J k)).domain : Set (K.V (k + 1))) :=
  (K.A k).formalAdj.dense_minimalVia_domain_of _ _ (K.denseVia k) (K.denseVia (k + 1))
    (K.mapsTo_formalAdj k)

/-- The **minimal complex** `d k = (A k)_via` (the `H̊` boundary conditions). -/
def minimalComplex : HilbertComplex 𝕜 (ComplexShape.up ℤ) fun k => K.V k :=
  HilbertComplex.ofSucc (fun k => (K.A k).minimalVia (K.J k) (K.J (k + 1))) K.dense_minimalVia
    (fun k => (K.A k).isClosed_minimalVia _ _ (K.denseVia (k + 1)))
    (fun k => ConstCoeffOp.minimalVia_mapsTo _ _ _ _ (K.toConstCoeffComplex.comp k)
      (K.denseVia (k + 1)) (K.denseVia (k + 1 + 1)))
    (fun k => ConstCoeffOp.minimalVia_comp _ _ _ _ (K.toConstCoeffComplex.comp k)
      (K.denseVia (k + 1)) (K.denseVia (k + 1 + 1)))

theorem minimalComplex_d (k : ℤ) :
    K.minimalComplex.d k (k + 1) = (K.A k).minimalVia (K.J k) (K.J (k + 1)) :=
  HilbertComplex.ofSuccD_succ (fun k => (K.A k).minimalVia (K.J k) (K.J (k + 1))) k

/-- The constrained realizations of the formal adjoints form a descending complex. -/
theorem formalAdj_minimalVia_mapsTo (hΩ : IsOpen Ω) (k : ℤ)
    (x : ((K.A (k + 1)).formalAdj.minimalVia (K.J (k + 1 + 1)) (K.J (k + 1))).domain) :
    ((K.A (k + 1)).formalAdj.minimalVia (K.J (k + 1 + 1)) (K.J (k + 1)) x : K.V (k + 1)) ∈
      ((K.A k).formalAdj.minimalVia (K.J (k + 1)) (K.J k)).domain :=
  ConstCoeffOp.minimalVia_mapsTo_of_isComplexPairVia _ _ _ _
    (ConstCoeffOp.IsComplexPair.isComplexPairVia_formalAdj _ _ hΩ (K.toConstCoeffComplex.comp k))
    (K.denseVia (k + 1)) (K.denseVia k) x

theorem formalAdj_minimalVia_comp (hΩ : IsOpen Ω) (k : ℤ)
    (x : ((K.A (k + 1)).formalAdj.minimalVia (K.J (k + 1 + 1)) (K.J (k + 1))).domain) :
    (K.A k).formalAdj.minimalVia (K.J (k + 1)) (K.J k) ⟨_, K.formalAdj_minimalVia_mapsTo hΩ k x⟩ =
      0 :=
  ConstCoeffOp.minimalVia_comp_of_isComplexPairVia _ _ _ _
    (ConstCoeffOp.IsComplexPair.isComplexPairVia_formalAdj _ _ hΩ (K.toConstCoeffComplex.comp k))
    (K.denseVia (k + 1)) (K.denseVia k) x

/-- The **maximal complex** `d k = (A k)_max,via` (no boundary conditions). -/
def maximalComplex (hΩ : IsOpen Ω) : HilbertComplex 𝕜 (ComplexShape.up ℤ) fun k => K.V k :=
  HilbertComplex.ofSucc (fun k => (K.A k).maximalVia (K.J k) (K.J (k + 1)))
    (fun k => (K.A k).dense_maximalVia_domain _ _ (K.denseVia k) (K.denseVia (k + 1))
      (K.mapsTo_formalAdj k))
    (fun k => (K.A k).isClosed_maximalVia _ _ (K.denseVia k) (K.denseVia (k + 1))
      (K.mapsTo_formalAdj k))
    (fun k => Feec.Operator.adjoint_mapsTo (K.dense_formalAdj_minimalVia k)
      (K.formalAdj_minimalVia_mapsTo hΩ k) (K.formalAdj_minimalVia_comp hΩ k))
    (fun k => Feec.Operator.adjoint_comp_eq_zero (K.dense_formalAdj_minimalVia (k + 1))
      (K.dense_formalAdj_minimalVia k) (K.formalAdj_minimalVia_mapsTo hΩ k)
      (K.formalAdj_minimalVia_comp hΩ k))

theorem maximalComplex_d (hΩ : IsOpen Ω) (k : ℤ) :
    (K.maximalComplex hΩ).d k (k + 1) = (K.A k).maximalVia (K.J k) (K.J (k + 1)) :=
  HilbertComplex.ofSuccD_succ (fun k => (K.A k).maximalVia (K.J k) (K.J (k + 1))) k

/-- **Duality**: the dual of the minimal complex is the maximal complex of the formal adjoints,
`(d_min k)† = (A kᵗ)_max,via`. -/
theorem dual_minimalComplex_d (k : ℤ) :
    K.minimalComplex.dual.d (k + 1) k = (K.A k).formalAdj.maximalVia (K.J (k + 1)) (K.J k) := by
  rw [HilbertComplex.dual_d, minimalComplex_d, ConstCoeffOp.adjoint_minimalVia]

/-- The dual of the maximal complex is the minimal complex of the formal adjoints. -/
theorem dual_maximalComplex_d (hΩ : IsOpen Ω) (k : ℤ) :
    (K.maximalComplex hΩ).dual.d (k + 1) k = (K.A k).formalAdj.minimalVia (K.J (k + 1)) (K.J k) := by
  rw [HilbertComplex.dual_d, maximalComplex_d, ConstCoeffOp.adjoint_maximalVia _ _ _ (K.denseVia k)
    (K.denseVia (k + 1)) (K.mapsTo_formalAdj k)]

/-- **`H̊ ⊆ H`**: the minimal differentials are restrictions of the maximal ones. -/
theorem minimalComplex_d_le_maximalComplex_d (hΩ : IsOpen Ω) (k : ℤ) :
    K.minimalComplex.d k (k + 1) ≤ (K.maximalComplex hΩ).d k (k + 1) := by
  rw [minimalComplex_d, maximalComplex_d]
  exact (K.A k).minimalVia_le_maximalVia _ _ (K.denseVia k) (K.denseVia (k + 1))
    (K.mapsTo_formalAdj k)

/-- `D(d_max k)` is the weak domain, tested against the `V (k+1)`-valued test fields. -/
theorem mem_maximalComplex_d_domain_iff (hΩ : IsOpen Ω) (k : ℤ) {u : K.V k} :
    u ∈ ((K.maximalComplex hΩ).d k (k + 1)).domain ↔
      ∃ w : K.V (k + 1), ∀ p ∈ (K.A k).formalAdj.testGraphVia (K.J (k + 1)) (K.J k),
        ⟪w, p.1⟫_𝕜 = ⟪u, p.2⟫_𝕜 := by
  rw [maximalComplex_d]
  exact (K.A k).mem_maximalVia_domain_iff _ _ (K.denseVia k) (K.denseVia (k + 1))
    (K.mapsTo_formalAdj k)

/-- The minimal differentials are restrictions of the unconstrained minimal realizations:
`J (d_min k x) = (A k)_min (J x)`. -/
theorem minimalComplex_d_graph_map (hΩ : IsOpen Ω) (k : ℤ)
    (x : (K.minimalComplex.d k (k + 1)).domain) :
    (((x : K.V k) : L2F 𝕜 Ω (K.ι k)), ((K.minimalComplex.d k (k + 1) x : K.V (k + 1)) :
      L2F 𝕜 Ω (K.ι (k + 1)))) ∈ ((K.A k).minimal Ω).graph := by
  have h := K.minimalComplex_d k
  revert x
  rw [h]
  exact (K.A k).minimalVia_graph_map (K.J k) (K.J (k + 1)) hΩ (K.denseVia (k + 1))

end ConstrainedComplex

/-! ### Constraints by pointwise projections -/

/-- A constrained complex whose constraints are ranges of pointwise orthogonal projections
`M k`, given the pointwise mapping properties of the operators and their formal adjoints. -/
def ConstrainedComplex.ofMatrices {Ω : Set E} (hΩ : IsOpen Ω) (C : ConstCoeffComplex E 𝕜)
    (M : ∀ k, C.ι k → C.ι k → 𝕜) (hM : ∀ k, IsProjMat (M k))
    (hA : ∀ k, (C.A k).MatMapsTo (M k) (M (k + 1)))
    (hAt : ∀ k, (C.A k).formalAdj.MatMapsTo (M (k + 1)) (M k)) : ConstrainedComplex E 𝕜 Ω where
  toConstCoeffComplex := C
  V k := L2F.matSubmodule 𝕜 Ω (M k)
  isClosed k := L2F.isClosed_matSubmodule (M k)
  denseVia k := L2F.denseVia_matSubmodule hΩ (hM k)
  mapsTo k := (hA k).mapsToVia hΩ
  mapsTo_formalAdj k := (hAt k).mapsToVia hΩ

end Complex

end Feec.Domain
