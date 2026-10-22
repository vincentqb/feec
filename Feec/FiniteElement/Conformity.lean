module

public import Feec.FiniteElement.MeshDivergence
public import Feec.Domain.DeRham
public import Feec.Domain.WholeSpace
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Conformity of piecewise smooth fields on simplicial meshes

Let `M` be a conforming simplicial mesh of an open set `Ω ⊆ ℝⁿ` (`n ≥ 1`) and `A` a first-order
constant-coefficient operator (`Feec.Domain.ConstCoeffOp`, `A.IsOrderLE 1`) with principal symbol
`σ_A(ν)` (`ConstCoeffOp.symbol`; `(σ_A(ν) w)ⱼ = Σᵢ Σ_{([v], c) ∈ Aⱼᵢ} c (v · ν) wᵢ`, no factor `i`).
A field `u` given on each closed element `T` by a field `u_T` that is `C¹` up to the boundary
(modelled by `C¹` fields on `ℝⁿ`; a `C¹` field on a neighbourhood of `T` extends by a cut-off)
whose **`A`-traces** `σ_A(ν) u_T` agree from both sides of every interior facet (for the normals
`ν` of the facet, `IsFaceNormal`) lies in the domain of the maximal realization `A_max(Ω)`, and
`A_max u` is the elementwise `A u_T`. If moreover the `A`-traces vanish on the boundary facets,
the extension of `u` by zero lies in `D(A_max(ℝⁿ)) = D(A_min(ℝⁿ))`, and, when `Ω` is strictly
star-shaped (e.g. convex, in particular a cube), `u ∈ D(A_min(Ω))`.

The proof of the first statement is elementwise integration by parts: for a test field `φ`,
`Σⱼ conj (A u)ⱼ φⱼ - Σᵢ conj uᵢ (Aᵗ φ)ᵢ = div G` with `G · ν = Σⱼ φⱼ conj (σ_A(ν) u)ⱼ`, and the
divergence theorem on the mesh (`Feec.FiniteElement.sum_setIntegral_divergence_eq_zero`): the face
terms cancel across interior facets by the trace condition and vanish on boundary facets, where
`φ = 0`, then `Feec.Domain.ConstCoeffOp.mem_maximal_domain_iff`. For the minimal domain, the
dilates `x ↦ u(x₀ + s (x - x₀))` (`s > 1`) of the extension by zero lie in `D(A_max(ℝⁿ))` with
compact support in `Ω`, hence in `D(A_min(Ω))` (`Feec.Domain.ConstCoeffOp.mem_minimal_of_support_subset`),
and converge to `u` in the graph norm as `s → 1`; `A_min` is closed.

## Main definitions

* `ConstCoeffOp.symbol A ν`, `ConstCoeffOp.symbolApply A ν w`: the principal symbol.
* `ConstCoeffOp.greenField A u φ`: the vector field of the elementwise integration by parts.
* `Feec.FiniteElement.pieceFun M v`: the piecewise function `Σ_T 𝟙_{int T} v_T`, and
  `Feec.FiniteElement.pieceL2 M S u`: the piecewise field as an element of `L²(S; 𝕜^ι)`.
* `Feec.FiniteElement.TangentialTraceEq F k α β`: `α` and `β` agree on `k`-tuples of vectors
  tangent to `F`.
* `ConstCoeffOp.scale A s`, `Feec.FiniteElement.dilL2`: the operator and the fields under the
  homothety `x ↦ x₀ + s (x - x₀)`.

## Main results

* `ConstCoeffOp.conj_apply_mul_sub_eq_sum_partialDeriv`, `sum_mul_greenField`: pointwise
  integration by parts and the normal component of `G`.
* `sum_integral_conj_apply_mul_eq`: integration by parts on a mesh.
* `pieceL2_mem_maximal_domain`: **conformity**, `u ∈ D(A_max(Ω))`, `A_max u = (A u_T)_T`.
* `pieceL2_univ_mem_maximal_domain`: vanishing boundary `A`-traces, extension by zero.
* `pieceL2_mem_minimal_domain`: `u ∈ D(A_min(Ω))` for strictly star-shaped `Ω`.
* The exterior derivative: `extDerivOp_pieceL2_mem_maximal_domain` (`ν ∧ u` continuous), from
  `symbolApply_extDerivOp` (`σ_d(ν) = ν ∧ ·`).
* Real `k`-forms: `extDeriv_pieceL2_mem_maximal_domain` and `extDeriv_pieceL2_mem_minimal_domain`
  (continuous resp. vanishing tangential traces), with `d_max` the elementwise classical exterior
  derivative `Feec.FiniteElement.extDeriv` (`extDerivOp_apply_formComp`), via
  `wedge_eq_of_tangentialTraceEq` (equal tangential traces give `ν ∧ α = ν ∧ β`) and
  `Feec.ExteriorFibre.wedge_eq_zero_of_pullback_eq_zero`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §5 (piecewise smooth forms with single-valued traces lie in `HΛᵏ`)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff ComplexConjugate Matrix
open MeasureTheory Set Finset

@[expose] public noncomputable section

namespace Feec.Domain.ConstCoeffOp

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*}

/-! ### The principal symbol of a first-order operator -/

/-- The pairing `v · ν` of a single direction `[v]` with `ν`; zero for other direction lists. -/
def dirPair : List (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  | [v], ν => ∑ l, v l * ν l
  | _, _ => 0

theorem dirPair_eq_sum (vs : List (Fin n → ℝ)) (ν : Fin n → ℝ) :
    dirPair vs ν = ∑ l, ν l * dirPair vs (Pi.single l 1) := by
  match vs with
  | [] => simp [dirPair]
  | [v] =>
    simp only [dirPair, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  | _ :: _ :: _ => simp [dirPair]

/-- A scalar entry of the principal symbol: `Σ_{([v], c)} c (v · ν)`. -/
def symbolEntry (P : List (List (Fin n → ℝ) × 𝕜)) (ν : Fin n → ℝ) : 𝕜 :=
  (P.map fun t => t.2 * (dirPair t.1 ν : 𝕜)).sum

/-- The **principal symbol** `σ_A(ν)` of a (first-order) operator: the matrix
`(σ_A(ν))ⱼᵢ = Σ_{([v], c) ∈ Aⱼᵢ} c (v · ν)` (no factor `i`). -/
def symbol (A : ConstCoeffOp (Fin n → ℝ) 𝕜 ι κ) (ν : Fin n → ℝ) (j : κ) (i : ι) : 𝕜 :=
  symbolEntry (A.coeff j i) ν

/-- The principal symbol applied to a vector `w ∈ 𝕜^ι`. -/
def symbolApply [Fintype ι] (A : ConstCoeffOp (Fin n → ℝ) 𝕜 ι κ) (ν : Fin n → ℝ) (w : ι → 𝕜) :
    κ → 𝕜 :=
  fun j => ∑ i, A.symbol ν j i * w i

theorem symbolEntry_cons (t : List (Fin n → ℝ) × 𝕜) (P : List (List (Fin n → ℝ) × 𝕜))
    (ν : Fin n → ℝ) :
    symbolEntry (t :: P) ν = t.2 * (dirPair t.1 ν : 𝕜) + symbolEntry P ν := by
  simp [symbolEntry]

@[simp] theorem symbolEntry_nil (ν : Fin n → ℝ) :
    symbolEntry ([] : List (List (Fin n → ℝ) × 𝕜)) ν = 0 := by
  simp [symbolEntry]

/-- The symbol is linear in `ν`. -/
theorem symbolEntry_eq_sum (P : List (List (Fin n → ℝ) × 𝕜)) (ν : Fin n → ℝ) :
    symbolEntry P ν = ∑ l, (ν l : 𝕜) * symbolEntry P (Pi.single l 1) := by
  induction P with
  | nil => simp
  | cons t P ih =>
    simp only [symbolEntry_cons, ih, mul_add, Finset.sum_add_distrib]
    congr 1
    rw [dirPair_eq_sum, RCLike.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    push_cast; ring

/-! ### Pointwise integration by parts -/

/-- Leibniz rule for `conj f * g`. -/
theorem fderiv_conj_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → 𝕜} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (v : E) :
    fderiv ℝ (fun y => conj (f y) * g y) x v =
      conj (fderiv ℝ f x v) * g x + conj (f x) * fderiv ℝ g x v := by
  have hc : HasFDerivAt (fun y => conj (f y))
      ((RCLike.conjCLE (K := 𝕜)).toContinuousLinearMap.comp (fderiv ℝ f x)) x :=
    (RCLike.conjCLE (K := 𝕜)).toContinuousLinearMap.hasFDerivAt.comp x hf.hasFDerivAt
  rw [show (fun y => conj (f y) * g y) = (fun y => conj (f y)) * g from rfl,
    (hc.mul hg.hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, RCLike.conjCLE_apply,
    smul_eq_mul]
  ring

/-- `∂_v h = Σₗ vₗ ∂ₗ h`. -/
theorem fderiv_apply_eq_sum_partialDeriv' {h : (Fin n → ℝ) → 𝕜} (x v : Fin n → ℝ) :
    fderiv ℝ h x v = ∑ l, (v l : 𝕜) * partialDeriv l h x := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show (Pi.single l (v l) : Fin n → ℝ) = v l • Pi.single l 1 by
      funext j; by_cases h : j = l <;> simp [h], map_smul,
    partialDeriv, RCLike.real_smul_eq_coe_mul]

/-- **Integration by parts for one scalar entry of order `≤ 1`**, pointwise:
`conj (P f) g - conj f (Pᵗ g) = Σₗ conj (σ_P(eₗ)) ∂ₗ (conj f g)`. -/
theorem conj_applyEntry_mul_sub (P : List (List (Fin n → ℝ) × 𝕜))
    (hP : ∀ t ∈ P, t.1.length ≤ 1) {f g : (Fin n → ℝ) → 𝕜} {x : Fin n → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    conj (applyEntry P f x) * g x - conj (f x) * applyEntry (adjEntry P) g x =
      ∑ l, conj (symbolEntry P (Pi.single l 1)) *
        partialDeriv l (fun y => conj (f y) * g y) x := by
  induction P with
  | nil => simp [adjEntry]
  | cons t P ih =>
    have ih' := ih fun t' ht' => hP t' (List.mem_cons_of_mem _ ht')
    obtain ⟨vs, c⟩ := t
    have hvs : vs.length ≤ 1 := hP _ List.mem_cons_self
    simp only [adjEntry, List.map_cons] at ih' ⊢
    rw [applyEntry_cons, applyEntry_cons]
    simp only [symbolEntry_cons, map_add, add_mul, Finset.sum_add_distrib]
    rw [← ih']
    match vs, hvs with
    | [], _ =>
      simp [dirPair]
      ring
    | [v], _ =>
      have hd : ∀ l, partialDeriv l (fun y => conj (f y) * g y) x =
          fderiv ℝ (fun y => conj (f y) * g y) x (Pi.single l 1) := fun l => rfl
      have key : ∑ l, conj (c * ((dirPair [v] (Pi.single l 1) : ℝ) : 𝕜)) *
          partialDeriv l (fun y => conj (f y) * g y) x =
          conj c * fderiv ℝ (fun y => conj (f y) * g y) x v := by
        rw [fderiv_apply_eq_sum_partialDeriv', Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [dirPair, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true, map_mul, RCLike.conj_ofReal]
        ring
      rw [key, fderiv_conj_mul hf hg]
      simp only [iterDeriv_singleton, List.reverse_singleton, List.length_singleton, pow_one,
        map_mul]
      ring

variable [Fintype ι] [Fintype κ]

/-- The vector field `G` of the elementwise integration by parts:
`Gₗ = Σⱼ Σᵢ conj (σ_A(eₗ))ⱼᵢ conj uᵢ φⱼ`. -/
def greenField (A : ConstCoeffOp (Fin n → ℝ) 𝕜 ι κ) (u : ι → (Fin n → ℝ) → 𝕜)
    (φ : κ → (Fin n → ℝ) → 𝕜) (l : Fin n) (y : Fin n → ℝ) : 𝕜 :=
  ∑ j, ∑ i, conj (A.symbol (Pi.single l 1) j i) * (conj (u i y) * φ j y)

theorem differentiableAt_conj_mul {f g : (Fin n → ℝ) → 𝕜} {x : Fin n → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun y => conj (f y) * g y) x :=
  (((RCLike.conjCLE (K := 𝕜)).toContinuousLinearMap.differentiableAt).comp x hf).mul hg

theorem partialDeriv_const_mul' {f : (Fin n → ℝ) → 𝕜} {x : Fin n → ℝ}
    (hf : DifferentiableAt ℝ f x) (c : 𝕜) (l : Fin n) :
    partialDeriv l (fun y => c * f y) x = c * partialDeriv l f x := by
  rw [partialDeriv, fderiv_const_mul hf c]; rfl

/-- **Elementwise integration by parts, pointwise**: for a first-order operator `A`,
`Σⱼ conj (A u)ⱼ φⱼ - Σᵢ conj uᵢ (Aᵗ φ)ᵢ = div G`, `G = greenField A u φ`. -/
theorem conj_apply_mul_sub_eq_sum_partialDeriv (A : ConstCoeffOp (Fin n → ℝ) 𝕜 ι κ)
    (hA : A.IsOrderLE 1) {u : ι → (Fin n → ℝ) → 𝕜} {φ : κ → (Fin n → ℝ) → 𝕜} {x : Fin n → ℝ}
    (hu : ∀ i, DifferentiableAt ℝ (u i) x) (hφ : ∀ j, DifferentiableAt ℝ (φ j) x) :
    ∑ j, conj (A.apply u j x) * φ j x - ∑ i, conj (u i x) * A.formalAdj.apply φ i x =
      ∑ l, partialDeriv l (A.greenField u φ l) x := by
  have hd : ∀ i j, DifferentiableAt ℝ (fun y => conj (u i y) * φ j y) x := fun i j =>
    differentiableAt_conj_mul (hu i) (hφ j)
  have hR : ∀ l, partialDeriv l (A.greenField u φ l) x = ∑ j, ∑ i,
      conj (A.symbol (Pi.single l 1) j i) * partialDeriv l (fun y => conj (u i y) * φ j y) x := by
    intro l
    unfold greenField
    rw [partialDeriv_sum _ (fun j _ => DifferentiableAt.fun_sum fun i _ =>
      (hd i j).const_mul _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [partialDeriv_sum _ (fun i _ => (hd i j).const_mul _)]
    exact Finset.sum_congr rfl fun i _ => partialDeriv_const_mul' (hd i j) _ l
  rw [Finset.sum_congr rfl fun l _ => hR l]
  have hL : ∑ j, conj (A.apply u j x) * φ j x - ∑ i, conj (u i x) * A.formalAdj.apply φ i x =
      ∑ j, ∑ i, (conj (applyEntry (A.coeff j i) (u i) x) * φ j x -
        conj (u i x) * applyEntry (adjEntry (A.coeff j i)) (φ j) x) := by
    simp only [ConstCoeffOp.apply, ConstCoeffOp.formalAdj, map_sum, Finset.sum_mul,
      Finset.mul_sum, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun i j => conj (u i x) * applyEntry (adjEntry (A.coeff j i)) (φ j) x)]
  rw [hL]
  simp only [fun j i => conj_applyEntry_mul_sub (A.coeff j i) (hA j i) (hu i) (hφ j)]
  exact (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans Finset.sum_comm

/-- The normal component of `greenField`: `G · ν = Σⱼ φⱼ conj (σ_A(ν) u)ⱼ`. -/
theorem sum_mul_greenField (A : ConstCoeffOp (Fin n → ℝ) 𝕜 ι κ) (u : ι → (Fin n → ℝ) → 𝕜)
    (φ : κ → (Fin n → ℝ) → 𝕜) (ν : Fin n → ℝ) (y : Fin n → ℝ) :
    ∑ l, (ν l : 𝕜) * A.greenField u φ l y =
      ∑ j, φ j y * conj (A.symbolApply ν (fun i => u i y) j) := by
  simp only [greenField, symbolApply, symbol, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [symbolEntry_eq_sum, map_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [map_mul, RCLike.conj_ofReal]
  ring

theorem contDiff_greenField (A : ConstCoeffOp (Fin n → ℝ) 𝕜 ι κ) {u : ι → (Fin n → ℝ) → 𝕜}
    {φ : κ → (Fin n → ℝ) → 𝕜} (hu : ∀ i, ContDiff ℝ 1 (u i)) (hφ : ∀ j, ContDiff ℝ 1 (φ j))
    (l : Fin n) : ContDiff ℝ 1 (A.greenField u φ l) :=
  ContDiff.sum fun j _ => ContDiff.sum fun i _ => contDiff_const.mul
    (((RCLike.conjCLE (K := 𝕜)).toContinuousLinearMap.contDiff.comp (hu i)).mul (hφ j))

end Feec.Domain.ConstCoeffOp

namespace Feec.ExteriorFibre

/-- **Tangential traces and the symbol of `d`**: if the pullback of a fibre form `α` along the
(linearly independent) edge vectors `B` of a hyperplane vanishes, then `ν ∧ α = 0` for every
normal `ν` of the hyperplane. -/
theorem wedge_eq_zero_of_pullback_eq_zero {m : ℕ} (B : Fin (m + 1) → Fin m → ℝ)
    (hB : LinearIndependent ℝ fun l i => B i l) (ν : Fin (m + 1) → ℝ)
    (hν : ∀ l, ∑ i, ν i * B i l = 0) {α : Finset (Fin (m + 1)) → ℝ}
    (hα : pullback B α = 0) : wedge ν α = 0 := by
  classical
  by_cases hν0 : ν = 0
  · subst hν0; exact wedge_zero_left α
  have hs : (∑ i, ν i * ν i) ≠ 0 := by
    intro h
    apply hν0
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (ν i)).1 h i (Finset.mem_univ i)
    simpa using this
  set c := (∑ i, ν i * ν i)⁻¹
  set P : Fin (m + 1) → Fin (m + 1) → ℝ := fun i l => Fin.lastCases (c * ν i) (fun l' => B i l') l
  have hcov : covPullback P ν = Pi.single (Fin.last m) 1 := by
    funext l
    refine Fin.lastCases ?_ (fun l => ?_) l
    · simp only [covPullback, P, Fin.lastCases_last, Pi.single_eq_same]
      have e : (∑ i, ν i * (c * ν i)) = c * ∑ i, ν i * ν i := by
        rw [Finset.mul_sum]; exact sum_congr rfl fun i _ => by ring
      rw [e]
      exact inv_mul_cancel₀ hs
    · simp only [covPullback, P, Fin.lastCases_castSucc]
      rw [hν l, Pi.single_eq_of_ne (Fin.castSucc_lt_last l).ne]
  set incl : Fin (m + 1) → Fin m → ℝ := fun a l => if a = Fin.castSucc l then 1 else 0
  have hBP : (fun j l => ∑ i, P j i * incl i l) = B := by
    funext j l
    simp only [incl, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, P,
      Fin.lastCases_castSucc]
  have hres : ∀ t : Finset (Fin (m + 1)), Fin.last m ∉ t → pullback P α t = 0 := by
    intro t ht
    have h1 : pullback incl (pullback P α) = restrict Fin.castSuccOrderEmb (pullback P α) :=
      pullback_eq_restrict Fin.castSuccOrderEmb (fun i l => ⟨fun h => by simp [incl, h],
        fun h => by simp only [incl]; exact ite_eq_right_iff.2 fun h' => absurd h' h⟩) _
    rw [pullback_pullback, hBP, hα] at h1
    have ht' : t = (univ.filter fun l : Fin m => Fin.castSucc l ∈ t).map
        Fin.castSuccOrderEmb.toEmbedding := by
      ext i
      simp only [mem_map, mem_filter, Finset.mem_univ, true_and, RelEmbedding.coe_toEmbedding,
        Fin.coe_castSuccOrderEmb]
      constructor
      · intro hi
        obtain ⟨l, rfl⟩ := Fin.exists_castSucc_eq.2 (fun h => ht (h ▸ hi))
        exact ⟨l, hi, rfl⟩
      · rintro ⟨l, hl, rfl⟩; exact hl
    rw [ht']
    exact (congrFun h1 _).symm
  have hw : pullback P (wedge ν α) = 0 := by
    rw [pullback_wedge, hcov]
    funext s
    rw [wedge_apply, Pi.zero_apply]
    refine sum_eq_zero fun j hj => ?_
    by_cases hjl : j = Fin.last m
    · subst hjl
      rw [hres _ (notMem_erase _ _), mul_zero]
    · rw [Pi.single_eq_of_ne hjl, mul_zero, zero_mul]
  -- `P` is invertible
  have hPinv : IsUnit (Matrix.of P) := by
    rw [← Matrix.linearIndependent_col_iff_isUnit]
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : ∀ i, ∑ l, g l * P i l = 0 := fun i => by
      have := congrFun hg i
      simpa [Matrix.col, Finset.sum_apply] using this
    have hlast : g (Fin.last m) = 0 := by
      have : ∑ i, ν i * ∑ l, g l * P i l = 0 := by simp [hg']
      rw [show (∑ i, ν i * ∑ l, g l * P i l) = ∑ l, g l * ∑ i, ν i * P i l by
        simp only [Finset.mul_sum]; rw [Finset.sum_comm]; exact sum_congr rfl fun l _ =>
          sum_congr rfl fun i _ => by ring] at this
      rw [Fin.sum_univ_castSucc] at this
      have h2 : ∀ l : Fin m, ∑ i, ν i * P i (Fin.castSucc l) = 0 := fun l => by
        simp only [P, Fin.lastCases_castSucc]; exact hν l
      have h3 : ∑ i, ν i * P i (Fin.last m) = 1 := by
        have := congrFun hcov (Fin.last m)
        simpa [covPullback] using this
      simp only [h2, mul_zero, sum_const_zero, zero_add, h3, mul_one] at this
      exact this
    have hcs : ∀ l : Fin m, g (Fin.castSucc l) = 0 := by
      have := Fintype.linearIndependent_iff.1 hB (fun l => g (Fin.castSucc l)) (by
        funext i
        have := hg' i
        rw [Fin.sum_univ_castSucc, hlast, zero_mul, add_zero] at this
        simpa [P] using this)
      exact this
    intro l
    refine Fin.lastCases hlast hcs l
  have hinj : ∀ β : Finset (Fin (m + 1)) → ℝ,
      pullback (fun i l => ((Matrix.of P)⁻¹) i l) (pullback P β) = β := by
    intro β
    rw [pullback_pullback]
    have : (fun j l => ∑ i, P j i * (Matrix.of P)⁻¹ i l) =
        fun i j => if i = j then (1 : ℝ) else 0 := by
      funext j l
      have := congrFun (congrFun (Matrix.mul_nonsing_inv (Matrix.of P)
        ((Matrix.isUnit_iff_isUnit_det _).1 hPinv)) j) l
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    rw [this, pullback_id]
  rw [← hinj (wedge ν α), hw, pullback_zero]

end Feec.ExteriorFibre

namespace Feec.Domain

open ConstCoeffOp ExteriorFibre

variable {n m : ℕ} {𝕜 : Type*} [RCLike 𝕜]

theorem dirPair_coordDir (j : Fin n) (ν : Fin n → ℝ) : dirPair [coordDir j] ν = ν j := by
  simp [dirPair, Pi.single_apply]

@[simp] theorem symbolEntry_singleton (vs : List (Fin n → ℝ)) (c : 𝕜) (ν : Fin n → ℝ) :
    symbolEntry [(vs, c)] ν = c * dirPair vs ν := by
  simp [symbolEntry]

theorem symbolEntry_extDerivOp_coeff {k : ℤ} (t : formIdx n (k + 1)) (r : formIdx n k)
    (ν : Fin n → ℝ) :
    symbolEntry ((extDerivOp 𝕜 n k).coeff t r) ν =
      ∑ j ∈ t.1 with t.1.erase j = r.1, sgn j t.1 * (ν j : 𝕜) := by
  simp only [symbolEntry, extDerivOp, List.map_map]
  rw [← Finset.sum_map_toList]
  simp [Function.comp_def, dirPair_coordDir]

/-- The symbol of `d` is exterior multiplication: `σ_d(ν) w = ν ∧ w`. -/
theorem symbolApply_extDerivOp {k : ℤ} (ν : Fin n → ℝ) (w : formIdx n k → 𝕜)
    (t : formIdx n (k + 1)) :
    (extDerivOp 𝕜 n k).symbolApply ν w t = wedge (fun j => (ν j : 𝕜)) (formExt w) t.1 := by
  simp only [symbolApply, symbol, symbolEntry_extDerivOp_coeff, Finset.sum_filter, wedge,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  set r₀ : formIdx n k := ⟨t.1.erase j, card_erase_of_formIdx t hj⟩
  have e : ∀ r : formIdx n k, (t.1.erase j = r.1) ↔ r = r₀ := fun r => by
    rw [Subtype.ext_iff]; exact eq_comm
  simp only [e, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [formExt_of_card w (card_erase_of_formIdx t hj)]

end Feec.Domain

namespace Feec.FiniteElement

open Feec.Domain Feec.Mesh ConstCoeffOp ExteriorFibre

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*}

/-! ### Piecewise fields -/

/-- The piecewise function `Σ_T 𝟙_{int T} v_T` of a family `v_T` (`T ∈ M`). -/
def pieceFun {F : Type*} [AddCommMonoid F] (M : SimplicialMesh n)
    (v : Affine.Simplex ℝ (Fin n → ℝ) n → (Fin n → ℝ) → F) (x : Fin n → ℝ) : F :=
  ∑ T ∈ M.simplices, (interior T.closedInterior).indicator (v T) x

/-- On the interior of an element, the piecewise function is the element function. -/
theorem pieceFun_of_mem_interior {F : Type*} [AddCommMonoid F] (M : SimplicialMesh n)
    (v : Affine.Simplex ℝ (Fin n → ℝ) n → (Fin n → ℝ) → F) {T : Affine.Simplex ℝ (Fin n → ℝ) n}
    (hT : T ∈ M.simplices) {x : Fin n → ℝ} (hx : x ∈ interior T.closedInterior) :
    pieceFun M v x = v T x := by
  rw [pieceFun, Finset.sum_eq_single T (fun T' hT' hne => Set.indicator_of_notMem
    (Set.disjoint_left.1 (M.pairwise_disjoint_interior hT hT' hne.symm) hx) _)
    (fun h => absurd hT h), Set.indicator_of_mem hx]

theorem memLp_pieceFun (M : SimplicialMesh n) {v : Affine.Simplex ℝ (Fin n → ℝ) n → (Fin n → ℝ) → 𝕜}
    (hv : ∀ T ∈ M.simplices, Continuous (v T)) (S : Set (Fin n → ℝ)) :
    MemLp (pieceFun M v) 2 (volume.restrict S) := by
  have : MemLp (pieceFun M v) 2 volume := by
    have h := memLp_finsetSum' (μ := volume) (p := 2) M.simplices (f := fun T x =>
      (interior T.closedInterior).indicator (v T) x) fun T hT =>
      (memLp_indicator_iff_restrict isOpen_interior.measurableSet.nullMeasurableSet).2
        (memLp_of_continuous isOpen_interior.measurableSet
          (T.isCompact_closedInterior.isBounded.subset interior_subset) (hv T hT))
    convert h using 1
    funext x
    simp [pieceFun]
  exact this.restrict S

theorem integral_conj_pieceFun_mul (M : SimplicialMesh n)
    {v : Affine.Simplex ℝ (Fin n → ℝ) n → (Fin n → ℝ) → 𝕜}
    (hv : ∀ T ∈ M.simplices, Continuous (v T)) {S : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → 𝕜}
    (hf : Continuous f) (hfS : ∀ x, x ∉ S → f x = 0) :
    ∫ x in S, conj (pieceFun M v x) * f x =
      ∑ T ∈ M.simplices, ∫ x in T.closedInterior, conj (v T x) * f x := by
  rw [integral_restrict_of_eq_zero (fun x hx => by rw [hfS x hx, mul_zero])]
  have e : (fun x => conj (pieceFun M v x) * f x) = fun x => ∑ T ∈ M.simplices,
      (interior T.closedInterior).indicator (fun x => conj (v T x) * f x) x := by
    funext x
    simp only [pieceFun, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun T _ => ?_
    by_cases hx : x ∈ interior T.closedInterior <;> simp [hx]
  have hint : ∀ T ∈ M.simplices, IntegrableOn (fun x => conj (v T x) * f x) T.closedInterior :=
    fun T hT => ((((RCLike.continuous_conj).comp (hv T hT)).mul hf).continuousOn).integrableOn_compact
      T.isCompact_closedInterior
  rw [e, integral_finsetSum _ fun T hT => (integrable_indicator_iff isOpen_interior.measurableSet).2
    ((hint T hT).mono_set interior_subset)]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [integral_indicator isOpen_interior.measurableSet]
  exact setIntegral_congr_set (interior_ae_eq_of_null_frontier (μ := volume)
    (s := T.closedInterior) (Convex.addHaar_frontier volume (Feec.Mesh.convex_closedInterior T)))

variable [Fintype ι]

/-- A piecewise continuous field as an element of `L²(S; 𝕜^ι)`. -/
def pieceL2 (M : SimplicialMesh n) (S : Set (Fin n → ℝ))
    (v : Affine.Simplex ℝ (Fin n → ℝ) n → ι → (Fin n → ℝ) → 𝕜)
    (hv : ∀ T ∈ M.simplices, ∀ i, Continuous (v T i)) : L2F 𝕜 S ι :=
  toL2F fun i => memLp_pieceFun M (v := fun T => v T i) (fun T hT => hv T hT i) S

omit [Fintype ι] in
theorem coeFn_pieceL2 (M : SimplicialMesh n) (S : Set (Fin n → ℝ))
    (v : Affine.Simplex ℝ (Fin n → ℝ) n → ι → (Fin n → ℝ) → 𝕜)
    (hv : ∀ T ∈ M.simplices, ∀ i, Continuous (v T i)) (i : ι) :
    (pieceL2 M S v hv i : (Fin n → ℝ) → 𝕜) =ᵐ[volume.restrict S] pieceFun M fun T => v T i :=
  (memLp_pieceFun M (v := fun T => v T i) (fun T hT => hv T hT i) S).coeFn_toLp

/-- `⟪u, φ⟫ = Σ_T Σᵢ ∫_T conj (u_T)ᵢ φᵢ` for a piecewise field `u` and a test field `φ`. -/
theorem inner_pieceL2_testField (M : SimplicialMesh n) {S : Set (Fin n → ℝ)}
    {v : Affine.Simplex ℝ (Fin n → ℝ) n → ι → (Fin n → ℝ) → 𝕜}
    (hv : ∀ T ∈ M.simplices, ∀ i, Continuous (v T i)) {φ : ι → (Fin n → ℝ) → 𝕜}
    (hφ : IsTestField S φ) :
    ⟪pieceL2 M S v hv, testField hφ⟫_𝕜 =
      ∑ T ∈ M.simplices, ∑ i, ∫ x in T.closedInterior, conj (v T i x) * φ i x := by
  rw [inner_testField, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← integral_conj_pieceFun_mul M (fun T hT => hv T hT i) (hφ i).continuous
    fun x hx => (hφ i).eq_zero_of_notMem hx]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_pieceL2 M S v hv i] with x hx
  rw [hx]

/-! ### Integration by parts on a mesh -/

/-- **Integration by parts on a mesh.** For a first-order operator `A`, a piecewise `C¹` field
`u` whose `A`-traces agree across the interior facets, and a `C¹` field `φ` whose pairing with
the `A`-traces vanishes on the boundary facets:
`Σ_T Σⱼ ∫_T conj (A u_T)ⱼ φⱼ = Σ_T Σᵢ ∫_T conj (u_T)ᵢ (Aᵗ φ)ᵢ`. -/
theorem sum_integral_conj_apply_mul_eq {m : ℕ} [Fintype κ]
    (A : ConstCoeffOp (Fin (m + 1) → ℝ) 𝕜 ι κ) (hA : A.IsOrderLE 1) (M : SimplicialMesh (m + 1))
    {u : Affine.Simplex ℝ (Fin (m + 1) → ℝ) (m + 1) → ι → (Fin (m + 1) → ℝ) → 𝕜}
    (hu : ∀ T ∈ M.simplices, ∀ i, ContDiff ℝ 1 (u T i)) {φ : κ → (Fin (m + 1) → ℝ) → 𝕜}
    (hφ : ∀ j, ContDiff ℝ 1 (φ j))
    (htr : ∀ F, M.IsInteriorFacet F → ∀ T ∈ M.cofaces F, ∀ T' ∈ M.cofaces F, ∀ ν,
      IsFaceNormal F ν → ∀ x ∈ convexHull ℝ (F : Set (Fin (m + 1) → ℝ)),
        A.symbolApply ν (fun i => u T i x) = A.symbolApply ν (fun i => u T' i x))
    (hbd : ∀ F, M.IsBoundaryFacet F → ∀ T ∈ M.cofaces F, ∀ ν, IsFaceNormal F ν →
      ∀ x ∈ convexHull ℝ (F : Set (Fin (m + 1) → ℝ)),
        ∑ j, φ j x * conj (A.symbolApply ν (fun i => u T i x) j) = 0) :
    ∑ T ∈ M.simplices, ∑ j, ∫ x in T.closedInterior, conj (A.apply (u T) j x) * φ j x =
      ∑ T ∈ M.simplices, ∑ i, ∫ x in T.closedInterior, conj (u T i x) * A.formalAdj.apply φ i x := by
  have hdiv := sum_setIntegral_divergence_eq_zero M (fun T => A.greenField (u T) φ)
    (fun T hT l => contDiff_greenField A (hu T hT) hφ l)
    (fun F hF T hT T' hT' ν hν x hx => by
      simp only [sum_mul_greenField, htr F hF T hT T' hT' ν hν x hx])
    (fun F hF T hT ν hν x hx => by rw [sum_mul_greenField]; exact hbd F hF T hT ν hν x hx)
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← hdiv]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hc1 : ∀ j, IntegrableOn (fun x => conj (A.apply (u T) j x) * φ j x) T.closedInterior :=
    fun j => (((RCLike.continuous_conj).comp (A.continuous_apply hA (hu T hT) j)).mul
      (hφ j).continuous).continuousOn.integrableOn_compact T.isCompact_closedInterior
  have hc2 : ∀ i, IntegrableOn (fun x => conj (u T i x) * A.formalAdj.apply φ i x)
      T.closedInterior :=
    fun i => (((RCLike.continuous_conj).comp (hu T hT i).continuous).mul
      (A.formalAdj.continuous_apply hA.formalAdj hφ i)).continuousOn.integrableOn_compact
        T.isCompact_closedInterior
  rw [← integral_finsetSum _ fun j _ => hc1 j, ← integral_finsetSum _ fun i _ => hc2 i,
    ← integral_sub (integrable_finsetSum _ fun j _ => hc1 j)
      (integrable_finsetSum _ fun i _ => hc2 i)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact A.conj_apply_mul_sub_eq_sum_partialDeriv hA
    (fun i => (hu T hT i).differentiable one_ne_zero x)
    (fun j => (hφ j).differentiable one_ne_zero x)

theorem notMem_of_mem_frontier_closure {E : Type*} [TopologicalSpace E] {Ω : Set E}
    (hΩ : IsOpen Ω) {x : E} (hx : x ∈ frontier (closure Ω)) : x ∉ Ω := fun h =>
  hx.2 (interior_maximal subset_closure hΩ h)

/-! ### Conformity: membership in the maximal domain -/

/-- **Conformity of piecewise `C¹` fields** ([AFW2006], §5). Let `M` be a simplicial mesh of an
open `Ω ⊆ ℝⁿ`, `A` a first-order constant-coefficient operator, and `u` a field given on each
closed element `T` by a `C¹` field `u_T`. If the `A`-traces `σ_A(ν) u_T` agree from both sides
of every interior facet (for the normals `ν` of the facet), then `u ∈ D(A_max(Ω))` and
`A_max u` is the elementwise `A u_T`. -/
theorem pieceL2_mem_maximal_domain [NeZero n] [Fintype κ]
    (A : ConstCoeffOp (Fin n → ℝ) 𝕜 ι κ) (hA : A.IsOrderLE 1) (M : SimplicialMesh n)
    (hΩ : IsOpen M.domain) {u : Affine.Simplex ℝ (Fin n → ℝ) n → ι → (Fin n → ℝ) → 𝕜}
    (hu : ∀ T ∈ M.simplices, ∀ i, ContDiff ℝ 1 (u T i))
    (htr : ∀ F, M.IsInteriorFacet F → ∀ T ∈ M.cofaces F, ∀ T' ∈ M.cofaces F, ∀ ν,
      IsFaceNormal F ν → ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)),
        A.symbolApply ν (fun i => u T i x) = A.symbolApply ν (fun i => u T' i x)) :
    ∃ h : pieceL2 M M.domain u (fun T hT i => (hu T hT i).continuous) ∈
        (A.maximal M.domain).domain,
      A.maximal M.domain ⟨_, h⟩ = pieceL2 M M.domain (fun T => A.apply (u T))
        (fun T hT j => A.continuous_apply hA (hu T hT) j) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.ne n; omega⟩
  have key : ∀ φ : κ → (Fin (m + 1) → ℝ) → 𝕜, ∀ hφ : IsTestField M.domain φ,
      ⟪pieceL2 M M.domain (fun T => A.apply (u T))
          (fun T hT j => A.continuous_apply hA (hu T hT) j), testField hφ⟫_𝕜 =
        ⟪pieceL2 M M.domain u (fun T hT i => (hu T hT i).continuous),
          testField (A.formalAdj.isTestField_apply hφ)⟫_𝕜 := by
    intro φ hφ
    rw [inner_pieceL2_testField, inner_pieceL2_testField]
    refine sum_integral_conj_apply_mul_eq A hA M hu
      (fun j => (hφ j).contDiff.of_le (by exact_mod_cast le_top)) htr ?_
    intro F hF T _ ν _ x hx
    have hxΩ := notMem_of_mem_frontier_closure hΩ (hF.2.2 hx)
    exact Finset.sum_eq_zero fun j _ => by rw [(hφ j).eq_zero_of_notMem hxΩ, zero_mul]
  have hmem := (A.mem_maximal_domain_iff hΩ).2 ⟨_, key⟩
  exact ⟨hmem, A.maximal_apply_eq hΩ ⟨_, hmem⟩ key⟩

/-- **Extension by zero.** If moreover the `A`-traces vanish on the boundary facets, the
extension of `u` by zero lies in `D(A_max(ℝⁿ))`, with `A_max` the elementwise `A u_T`
(extended by zero). -/
theorem pieceL2_univ_mem_maximal_domain [NeZero n] [Fintype κ]
    (A : ConstCoeffOp (Fin n → ℝ) 𝕜 ι κ) (hA : A.IsOrderLE 1) (M : SimplicialMesh n)
    {u : Affine.Simplex ℝ (Fin n → ℝ) n → ι → (Fin n → ℝ) → 𝕜}
    (hu : ∀ T ∈ M.simplices, ∀ i, ContDiff ℝ 1 (u T i))
    (htr : ∀ F, M.IsInteriorFacet F → ∀ T ∈ M.cofaces F, ∀ T' ∈ M.cofaces F, ∀ ν,
      IsFaceNormal F ν → ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)),
        A.symbolApply ν (fun i => u T i x) = A.symbolApply ν (fun i => u T' i x))
    (hbd : ∀ F, M.IsBoundaryFacet F → ∀ T ∈ M.cofaces F, ∀ ν, IsFaceNormal F ν →
      ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)), A.symbolApply ν (fun i => u T i x) = 0) :
    ∃ h : pieceL2 M univ u (fun T hT i => (hu T hT i).continuous) ∈ (A.maximal univ).domain,
      A.maximal univ ⟨_, h⟩ = pieceL2 M univ (fun T => A.apply (u T))
        (fun T hT j => A.continuous_apply hA (hu T hT) j) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.ne n; omega⟩
  have key : ∀ φ : κ → (Fin (m + 1) → ℝ) → 𝕜, ∀ hφ : IsTestField univ φ,
      ⟪pieceL2 M univ (fun T => A.apply (u T))
          (fun T hT j => A.continuous_apply hA (hu T hT) j), testField hφ⟫_𝕜 =
        ⟪pieceL2 M univ u (fun T hT i => (hu T hT i).continuous),
          testField (A.formalAdj.isTestField_apply hφ)⟫_𝕜 := by
    intro φ hφ
    rw [inner_pieceL2_testField, inner_pieceL2_testField]
    refine sum_integral_conj_apply_mul_eq A hA M hu
      (fun j => (hφ j).contDiff.of_le (by exact_mod_cast le_top)) htr ?_
    intro F hF T hT ν hν x hx
    rw [hbd F hF T hT ν hν x hx]
    simp
  have hmem := (A.mem_maximal_domain_iff isOpen_univ).2 ⟨_, key⟩
  exact ⟨hmem, A.maximal_apply_eq isOpen_univ ⟨_, hmem⟩ key⟩

omit [Fintype ι] in
theorem pieceL2_congr (M : SimplicialMesh n) (S : Set (Fin n → ℝ))
    {v v' : Affine.Simplex ℝ (Fin n → ℝ) n → ι → (Fin n → ℝ) → 𝕜}
    (hv : ∀ T ∈ M.simplices, ∀ i, Continuous (v T i))
    (hv' : ∀ T ∈ M.simplices, ∀ i, Continuous (v' T i)) (h : ∀ T ∈ M.simplices, v T = v' T) :
    pieceL2 M S v hv = pieceL2 M S v' hv' := by
  refine PiLp.ext fun i => Lp.ext ?_
  filter_upwards [coeFn_pieceL2 M S v hv i, coeFn_pieceL2 M S v' hv' i] with x h1 h2
  rw [h1, h2, pieceFun, pieceFun]
  exact Finset.sum_congr rfl fun T hT => by rw [h T hT]

/-! ### Instances: grad, curl, div, and the exterior derivative -/

/-- **`HΛᵏ`-conformity**, symbol form: piecewise `C¹` `k`-forms (with values in `𝕜`) whose
traces `ν ∧ u` agree across the interior facets lie in `D(d_max(Ω))`. -/
theorem extDerivOp_pieceL2_mem_maximal_domain [NeZero n] {k : ℤ} (M : SimplicialMesh n)
    (hΩ : IsOpen M.domain)
    {u : Affine.Simplex ℝ (Fin n → ℝ) n → formIdx n k → (Fin n → ℝ) → 𝕜}
    (hu : ∀ T ∈ M.simplices, ∀ s, ContDiff ℝ 1 (u T s))
    (htan : ∀ F, M.IsInteriorFacet F → ∀ T ∈ M.cofaces F, ∀ T' ∈ M.cofaces F, ∀ ν,
      IsFaceNormal F ν → ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)),
        wedge (fun j => (ν j : 𝕜)) (formExt fun s => u T s x) =
          wedge (fun j => (ν j : 𝕜)) (formExt fun s => u T' s x)) :
    ∃ h : pieceL2 M M.domain u (fun T hT s => (hu T hT s).continuous) ∈
        ((extDerivOp 𝕜 n k).maximal M.domain).domain,
      (extDerivOp 𝕜 n k).maximal M.domain ⟨_, h⟩ =
        pieceL2 M M.domain (fun T => (extDerivOp 𝕜 n k).apply (u T))
          (fun T hT t => (extDerivOp 𝕜 n k).continuous_apply (extDerivOp_isOrderLE k) (hu T hT) t) :=
  pieceL2_mem_maximal_domain _ (extDerivOp_isOrderLE k) M hΩ hu fun F hF T hT T' hT' ν hν x hx =>
    funext fun t => by
      rw [symbolApply_extDerivOp, symbolApply_extDerivOp, htan F hF T hT T' hT' ν hν x hx]

/-! ### Real `k`-forms: tangential traces and the classical exterior derivative -/

/-- `α` and `β` have the same **tangential trace** on the face spanned by `F`: they agree on all
`k`-tuples of vectors tangent to `F`, `α(v₁, …, v_k) = β(v₁, …, v_k)` for `vₗ ∈ vec span F`
(the columns of `V`; `α(V) = (V^* α)_{univ}`). -/
def TangentialTraceEq (F : Finset (Fin n → ℝ)) (k : ℕ) (α β : Finset (Fin n) → ℝ) : Prop :=
  ∀ V : Fin n → Fin k → ℝ, (∀ l, (fun i => V i l) ∈ vectorSpan ℝ (F : Set (Fin n → ℝ))) →
    pullback V α univ = pullback V β univ

theorem wedge_sub_right {d : Type*} [LinearOrder d] (ξ : d → ℝ) (α β : Finset d → ℝ) :
    wedge ξ (α - β) = wedge ξ α - wedge ξ β := by
  funext s
  simp only [wedge_apply, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

open Feec.Mesh in
/-- The edge vectors of a facet of an `n`-simplex are linearly independent. -/
theorem linearIndependent_simplexMatrix_faceEnum {m : ℕ}
    {T : Affine.Simplex ℝ (Fin (m + 1) → ℝ) (m + 1)} {F : Finset (Fin (m + 1) → ℝ)}
    (hF : F ⊆ vertexSet T) (hc : F.card = m + 1) :
    LinearIndependent ℝ fun l i => simplexMatrix (faceEnum F (m + 1)) i l := by
  classical
  set q := faceEnum F (m + 1)
  have hq : Set.range q = F := range_faceEnum hc
  have hmem : ∀ l, ∃ i, T.points i = q l := fun l =>
    mem_vertexSet.1 (hF (by rw [← Finset.mem_coe, ← hq]; exact ⟨l, rfl⟩))
  choose e he using hmem
  have hinj : Function.Injective e := fun a b hab =>
    injective_faceEnum hc ((he a).symm.trans ((congrArg T.points hab).trans (he b)))
  have hai : AffineIndependent ℝ q := by
    have := T.independent.comp_embedding ⟨e, hinj⟩
    convert this using 1
    funext l; exact (he l).symm
  have h := (affineIndependent_iff_linearIndependent_vsub ℝ q 0).1 hai
  have h2 := h.comp (fun l : Fin m => (⟨l.succ, Fin.succ_ne_zero l⟩ : {x : Fin (m + 1) // x ≠ 0}))
    fun a b hab => Fin.succ_injective _ (congrArg Subtype.val hab)
  convert h2 using 1
  funext l i
  simp [simplexMatrix]

open Feec.Mesh in
/-- **Equal tangential traces give equal `d`-traces**: on a facet `F` of an `n`-simplex, two
`k`-forms with the same tangential trace satisfy `ν ∧ α = ν ∧ β` for every normal `ν`. -/
theorem wedge_eq_of_tangentialTraceEq {m : ℕ} {T : Affine.Simplex ℝ (Fin (m + 1) → ℝ) (m + 1)}
    {F : Finset (Fin (m + 1) → ℝ)} (hF : F ⊆ vertexSet T) (hc : F.card = m + 1) {k : ℕ}
    {α β : Finset (Fin (m + 1)) → ℝ} (hα : IsDeg k α) (hβ : IsDeg k β)
    (h : TangentialTraceEq F k α β) {ν : Fin (m + 1) → ℝ} (hν : IsFaceNormal F ν) :
    wedge ν α = wedge ν β := by
  classical
  set q := faceEnum F (m + 1)
  have hq : Set.range q = F := range_faceEnum hc
  have hqF : ∀ l, q l ∈ F := fun l => by rw [← Finset.mem_coe, ← hq]; exact ⟨l, rfl⟩
  set B := simplexMatrix q
  have hν' : ∀ l, ∑ i, ν i * B i l = 0 := fun l => hν _ (hqF l.succ) _ (hqF 0)
  have hpull : pullback B (α - β) = 0 := by
    funext t
    by_cases ht : #t = k
    · set e := t.orderEmbOfFin ht
      set incl : Fin m → Fin k → ℝ := fun l a => if l = e a then 1 else 0
      have h1 : pullback incl (pullback B (α - β)) = restrict e (pullback B (α - β)) :=
        pullback_eq_restrict e (fun l a => ⟨fun hl => by simp [incl, hl],
          fun hl => by simp only [incl]; exact ite_eq_right_iff.2 fun h' => absurd h' hl⟩) _
      have h2 := congrFun h1 univ
      rw [ExteriorFibre.restrict, map_orderEmbOfFin_univ, pullback_pullback] at h2
      rw [Pi.zero_apply, ← h2, pullback_sub, Pi.sub_apply, sub_eq_zero]
      refine h _ fun a => ?_
      have : (fun i => ∑ l, B i l * incl l a) = q (e a).succ -ᵥ q 0 := by
        funext i
        simp only [incl, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
          ite_true, B, simplexMatrix, vsub_eq_sub, Pi.sub_apply]
      rw [this]
      exact vsub_mem_vectorSpan ℝ (Finset.mem_coe.2 (hqF _)) (Finset.mem_coe.2 (hqF 0))
    · have hd : IsDeg k (α - β) := fun r hr => by simp [hα r hr, hβ r hr]
      exact (hd.pullback B) t ht
  have := wedge_eq_zero_of_pullback_eq_zero B
    (linearIndependent_simplexMatrix_faceEnum hF hc) ν hν' hpull
  rw [wedge_sub_right, sub_eq_zero] at this
  exact this

/-- The components `ω_s`, `s` a `k`-subset, of a coefficient form field. -/
def formComp {k : ℤ} (η : FormField n) : formIdx n k → (Fin n → ℝ) → ℝ := fun s x => η x s.1

theorem formExt_formComp {k : ℕ} {η : FormField n} {x : Fin n → ℝ} (hη : IsDeg k (η x)) :
    (formExt fun s : formIdx n k => formComp η s x) = η x := by
  funext r
  unfold formExt
  split_ifs with h
  · rfl
  · exact (hη r (fun h' => h (by rw [h']))).symm

/-- **The bridge to the classical exterior derivative**: on the components of a `k`-form field,
`extDerivOp` is `Feec.FiniteElement.extDeriv`. -/
theorem extDerivOp_apply_formComp {k : ℕ} {η : FormField n} (hη : ∀ x, IsDeg k (η x))
    (t : formIdx n ((k : ℤ) + 1)) (x : Fin n → ℝ) :
    (extDerivOp ℝ n k).apply (formComp η) t x = extDeriv η x t.1 := by
  rw [extDerivOp_apply, extD, extDeriv_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : formExt (formComp (k := (k : ℤ)) η) (t.1.erase j) = fun y => η y (t.1.erase j) := by
    funext y
    exact congrFun (formExt_formComp (hη y)) _ ▸ by
      unfold formExt; split_ifs <;> rfl
  rw [this]
  rfl

theorem continuous_formComp {k : ℤ} {η : FormField n} (hη : Continuous η) (s : formIdx n k) :
    Continuous (formComp η s) :=
  (continuous_apply s.1).comp hη

/-- **`HΛᵏ`-conformity of piecewise smooth real `k`-forms** ([AFW2006], §5): if the tangential
traces of the `η_T` agree on every interior facet, then `η ∈ HΛᵏ(Ω) = D(d_max)` and
`d_max η` is the elementwise classical exterior derivative. -/
theorem extDeriv_pieceL2_mem_maximal_domain [NeZero n] (k : ℕ) (M : SimplicialMesh n)
    (hΩ : IsOpen M.domain) {η : Affine.Simplex ℝ (Fin n → ℝ) n → FormField n}
    (hη : ∀ T ∈ M.simplices, ContDiff ℝ 1 (η T)) (hdeg : ∀ T ∈ M.simplices, ∀ x, IsDeg k (η T x))
    (htr : ∀ F, M.IsInteriorFacet F → ∀ T ∈ M.cofaces F, ∀ T' ∈ M.cofaces F,
      ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)), TangentialTraceEq F k (η T x) (η T' x)) :
    ∃ h : pieceL2 M M.domain (fun T => formComp (k := k) (η T))
        (fun T hT s => continuous_formComp (hη T hT).continuous s) ∈
        ((extDerivOp ℝ n k).maximal M.domain).domain,
      (extDerivOp ℝ n k).maximal M.domain ⟨_, h⟩ =
        pieceL2 M M.domain (fun T => formComp (k := (k : ℤ) + 1) (extDeriv (η T)))
          (fun T hT t => continuous_formComp (continuous_extDeriv (hη T hT)) t) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.ne n; omega⟩
  have hu : ∀ T ∈ M.simplices, ∀ s : formIdx (m + 1) k, ContDiff ℝ 1 (formComp (η T) s) :=
    fun T hT s => contDiff_pi.1 (hη T hT) s.1
  obtain ⟨h, hval⟩ := extDerivOp_pieceL2_mem_maximal_domain (𝕜 := ℝ) M hΩ hu
    fun F hF T hT T' hT' ν hν x hx => by
      have hc : F.card = m + 1 := hF.1.1
      rw [formExt_formComp (hdeg T (M.mem_cofaces.1 hT).1 x),
        formExt_formComp (hdeg T' (M.mem_cofaces.1 hT').1 x)]
      exact wedge_eq_of_tangentialTraceEq (M.mem_cofaces.1 hT).2 hc
        (hdeg T (M.mem_cofaces.1 hT).1 x) (hdeg T' (M.mem_cofaces.1 hT').1 x)
        (htr F hF T hT T' hT' x hx) hν
  refine ⟨h, hval.trans (pieceL2_congr M _ _ _ fun T hT => ?_)⟩
  funext t x
  exact extDerivOp_apply_formComp (hdeg T hT) t x

end Feec.FiniteElement

namespace Feec.Domain.ConstCoeffOp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*}

/-! ### Dilations and the minimal domain -/

/-- `A_s`: the operator with each `k`-th order coefficient multiplied by `sᵏ`, so that
`A_s (f ∘ h) = (A f) ∘ h` for the homothety `h(y) = x₀ + s⁻¹ (y - x₀)`. -/
def scale (A : ConstCoeffOp E 𝕜 ι κ) (s : ℝ) : ConstCoeffOp E 𝕜 ι κ where
  coeff j i := (A.coeff j i).map fun t => (t.1, (s : 𝕜) ^ t.1.length * t.2)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem IsOrderLE.scale {A : ConstCoeffOp E 𝕜 ι κ} {N : ℕ} (h : A.IsOrderLE N) (s : ℝ) :
    (A.scale s).IsOrderLE N := by
  intro j i t ht
  simp only [ConstCoeffOp.scale, List.mem_map] at ht
  obtain ⟨t', ht', rfl⟩ := ht
  exact h j i t' ht'

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem formalAdj_scale (A : ConstCoeffOp E 𝕜 ι κ) (s : ℝ) :
    (A.scale s).formalAdj = A.formalAdj.scale s := by
  simp only [ConstCoeffOp.scale, ConstCoeffOp.formalAdj, adjEntry, List.map_map]
  congr 1
  funext i j
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply, List.length_reverse, map_mul, map_pow, RCLike.conj_ofReal,
    Prod.mk.injEq, true_and]
  ring

theorem applyEntry_map_scale (P : List (List E × 𝕜)) (s : ℝ) (f : E → 𝕜) (x : E) :
    applyEntry (P.map fun t => (t.1, (s : 𝕜) ^ t.1.length * t.2)) f x =
      (P.map fun t => (s : 𝕜) ^ t.1.length * t.2 * iterDeriv t.1 f x).sum := by
  simp [applyEntry, List.map_map, Function.comp_def]

/-- Chain rule for the homothety `h(y) = x₀ + r (y - x₀)`. -/
theorem iterDeriv_comp_homothety {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ ∞ f) (x₀ : E) (r : ℝ) (vs : List E) (y : E) :
    iterDeriv vs (fun y => f (x₀ + r • (y - x₀))) y =
      r ^ vs.length • iterDeriv vs f (x₀ + r • (y - x₀)) := by
  induction vs generalizing y with
  | nil => simp
  | cons v vs ih =>
    have hfun : iterDeriv vs (fun y => f (x₀ + r • (y - x₀))) =
        fun y => r ^ vs.length • iterDeriv vs f (x₀ + r • (y - x₀)) := funext ih
    rw [iterDeriv_cons, hfun]
    have hh : HasFDerivAt (fun y : E => x₀ + r • (y - x₀)) (r • ContinuousLinearMap.id ℝ E) y := by
      have := (((hasFDerivAt_id (𝕜 := ℝ) y).sub_const x₀).const_smul r).const_add x₀
      simpa using this
    have hd : DifferentiableAt ℝ (iterDeriv vs f) (x₀ + r • (y - x₀)) :=
      (contDiff_iterDeriv hf vs).differentiable (by simp) _
    have h3 : HasFDerivAt (fun y => r ^ vs.length • iterDeriv vs f (x₀ + r • (y - x₀)))
        (r ^ vs.length • (fderiv ℝ (iterDeriv vs f) (x₀ + r • (y - x₀))).comp
          (r • ContinuousLinearMap.id ℝ E)) y :=
      (hd.hasFDerivAt.comp y hh).const_smul (r ^ vs.length)
    show fderiv ℝ (fun y => r ^ vs.length • iterDeriv vs f (x₀ + r • (y - x₀))) y v = _
    rw [h3.fderiv]
    simp [iterDeriv_cons, List.length_cons, pow_succ, smul_smul, mul_comm]

end Feec.Domain.ConstCoeffOp

namespace Feec.Domain.ConstCoeffOp

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} {n : ℕ}

theorem apply_scale_comp_homothety [Fintype ι] (A : ConstCoeffOp (Fin n → ℝ) 𝕜 ι κ) {s : ℝ}
    (hs : s ≠ 0) (x₀ : Fin n → ℝ) {f : ι → (Fin n → ℝ) → 𝕜} (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (j : κ) (y : Fin n → ℝ) :
    (A.scale s).apply (fun i y => f i (x₀ + s⁻¹ • (y - x₀))) j y =
      A.apply f j (x₀ + s⁻¹ • (y - x₀)) := by
  simp only [ConstCoeffOp.apply, ConstCoeffOp.scale, applyEntry_map_scale]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [applyEntry]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  rw [iterDeriv_comp_homothety (hf i), RCLike.real_smul_eq_coe_mul]
  push_cast
  have h0 : ((s : 𝕜) ^ t.1.length) ≠ 0 := pow_ne_zero _ (RCLike.ofReal_ne_zero.2 hs)
  rw [inv_pow]
  field_simp

theorem symbolEntry_map_scale (P : List (List (Fin n → ℝ) × 𝕜)) (s : ℝ) (ν : Fin n → ℝ) :
    symbolEntry (P.map fun t => (t.1, (s : 𝕜) ^ t.1.length * t.2)) ν =
      (s : 𝕜) * symbolEntry P ν := by
  induction P with
  | nil => simp
  | cons t P ih =>
    rw [List.map_cons, symbolEntry_cons, symbolEntry_cons, ih, mul_add]
    congr 1
    obtain ⟨vs, c⟩ := t
    match vs with
    | [] => simp [dirPair]
    | [v] => simp; ring
    | _ :: _ :: _ => simp [dirPair]

theorem symbolApply_scale [Fintype ι] (A : ConstCoeffOp (Fin n → ℝ) 𝕜 ι κ) (s : ℝ)
    (ν : Fin n → ℝ) (w : ι → 𝕜) (j : κ) :
    (A.scale s).symbolApply ν w j = (s : 𝕜) * A.symbolApply ν w j := by
  simp only [symbolApply, symbol, ConstCoeffOp.scale, symbolEntry_map_scale, Finset.mul_sum,
    mul_assoc]

end Feec.Domain.ConstCoeffOp

namespace Feec.FiniteElement

open Feec.Domain Feec.Mesh ConstCoeffOp

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} {n : ℕ}

/-- The homothety `x ↦ x₀ + s (x - x₀)`. -/
def homothety (x₀ : Fin n → ℝ) (s : ℝ) (x : Fin n → ℝ) : Fin n → ℝ := x₀ + s • (x - x₀)

/-- Change of variables under a homothety: `∫ F(x₀ + s (x - x₀)) dx = |sⁿ|⁻¹ ∫ F`. -/
theorem integral_comp_homothety {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : (Fin n → ℝ) → F) (x₀ : Fin n → ℝ) (s : ℝ) :
    ∫ x, f (homothety x₀ s x) = |(s ^ n)⁻¹| • ∫ x, f x := by
  have e : (fun x => f (homothety x₀ s x)) =
      fun x => (fun z => f (z + (x₀ - s • x₀))) (s • x) := by
    funext x; unfold homothety; congr 1; rw [smul_sub]; abel
  have h := Measure.integral_comp_smul (volume : Measure (Fin n → ℝ))
    (fun z => f (z + (x₀ - s • x₀))) s
  rw [e, h, integral_add_right_eq_self, Module.finrank_fin_fun]

theorem continuous_homothety (x₀ : Fin n → ℝ) (s : ℝ) : Continuous (homothety x₀ s) := by
  unfold homothety; fun_prop

theorem homothety_inv_homothety (x₀ : Fin n → ℝ) {s : ℝ} (hs : s ≠ 0) (x : Fin n → ℝ) :
    homothety x₀ s⁻¹ (homothety x₀ s x) = x := by
  simp [homothety, smul_smul, inv_mul_cancel₀ hs]

theorem memLp_pieceFun_comp_homothety (M : SimplicialMesh n)
    {v : Affine.Simplex ℝ (Fin n → ℝ) n → (Fin n → ℝ) → 𝕜}
    (hv : ∀ T ∈ M.simplices, Continuous (v T)) (x₀ : Fin n → ℝ) {s : ℝ} (hs : s ≠ 0)
    (S : Set (Fin n → ℝ)) :
    MemLp (fun x => pieceFun M v (homothety x₀ s x)) 2 (volume.restrict S) := by
  have hg := continuous_homothety x₀ s
  have : MemLp (fun x => pieceFun M v (homothety x₀ s x)) 2 volume := by
    have h := memLp_finsetSum' (μ := volume) (p := 2) M.simplices (f := fun T x =>
      (homothety x₀ s ⁻¹' interior T.closedInterior).indicator (fun x => v T (homothety x₀ s x)) x)
      fun T hT => (memLp_indicator_iff_restrict
        (isOpen_interior.preimage hg).measurableSet.nullMeasurableSet).2
        (memLp_of_continuous (isOpen_interior.preimage hg).measurableSet
          (((T.isCompact_closedInterior.image (continuous_homothety x₀ s⁻¹)).isBounded).subset
            fun x hx => ⟨_, interior_subset hx, homothety_inv_homothety x₀ hs x⟩)
          ((hv T hT).comp hg))
    convert h using 1
    funext x
    simp only [pieceFun, Finset.sum_apply]
    refine Finset.sum_congr rfl fun T _ => ?_
    by_cases hx : homothety x₀ s x ∈ interior T.closedInterior
    · rw [Set.indicator_of_mem hx,
        Set.indicator_of_mem (s := homothety x₀ s ⁻¹' interior T.closedInterior) hx]
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (s := homothety x₀ s ⁻¹' interior T.closedInterior) hx]
  exact this.restrict S

variable [Fintype ι]

/-- The dilate `x ↦ u(x₀ + s (x - x₀))` of a piecewise field, in `L²(S; 𝕜^ι)`. -/
def dilL2 (M : SimplicialMesh n) (S : Set (Fin n → ℝ))
    (v : Affine.Simplex ℝ (Fin n → ℝ) n → ι → (Fin n → ℝ) → 𝕜)
    (hv : ∀ T ∈ M.simplices, ∀ i, Continuous (v T i)) (x₀ : Fin n → ℝ) {s : ℝ} (hs : s ≠ 0) :
    L2F 𝕜 S ι :=
  toL2F fun i => memLp_pieceFun_comp_homothety M (v := fun T => v T i) (fun T hT => hv T hT i)
    x₀ hs S

omit [Fintype ι] in
theorem coeFn_dilL2 (M : SimplicialMesh n) (S : Set (Fin n → ℝ))
    (v : Affine.Simplex ℝ (Fin n → ℝ) n → ι → (Fin n → ℝ) → 𝕜)
    (hv : ∀ T ∈ M.simplices, ∀ i, Continuous (v T i)) (x₀ : Fin n → ℝ) {s : ℝ} (hs : s ≠ 0)
    (i : ι) :
    (dilL2 M S v hv x₀ hs i : (Fin n → ℝ) → 𝕜) =ᵐ[volume.restrict S]
      fun x => pieceFun M (fun T => v T i) (homothety x₀ s x) :=
  (memLp_pieceFun_comp_homothety M (v := fun T => v T i) (fun T hT => hv T hT i) x₀ hs S).coeFn_toLp

theorem inner_dilL2_testField_univ (M : SimplicialMesh n)
    {v : Affine.Simplex ℝ (Fin n → ℝ) n → ι → (Fin n → ℝ) → 𝕜}
    (hv : ∀ T ∈ M.simplices, ∀ i, Continuous (v T i)) (x₀ : Fin n → ℝ) {s : ℝ} (hs : s ≠ 0)
    {φ : ι → (Fin n → ℝ) → 𝕜} (hφ : IsTestField univ φ) :
    ⟪dilL2 M univ v hv x₀ hs, testField hφ⟫_𝕜 =
      ∑ i, ∫ x, conj (pieceFun M (fun T => v T i) (homothety x₀ s x)) * φ i x := by
  rw [inner_testField]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [setIntegral_univ]
  refine integral_congr_ae ?_
  have := (ae_restrict_iff' MeasurableSet.univ).1 (coeFn_dilL2 M univ v hv x₀ hs i)
  filter_upwards [this] with x hx
  rw [hx (mem_univ x)]

theorem inner_pieceL2_testField_univ (M : SimplicialMesh n)
    {v : Affine.Simplex ℝ (Fin n → ℝ) n → ι → (Fin n → ℝ) → 𝕜}
    (hv : ∀ T ∈ M.simplices, ∀ i, Continuous (v T i))
    {φ : ι → (Fin n → ℝ) → 𝕜} (hφ : IsTestField univ φ) :
    ⟪pieceL2 M univ v hv, testField hφ⟫_𝕜 =
      ∑ i, ∫ x, conj (pieceFun M (fun T => v T i) x) * φ i x := by
  rw [inner_testField]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [setIntegral_univ]
  refine integral_congr_ae ?_
  have := (ae_restrict_iff' MeasurableSet.univ).1 (coeFn_pieceL2 M univ v hv i)
  filter_upwards [this] with x hx
  rw [hx (mem_univ x)]

theorem _root_.Feec.Domain.IsTest.comp_homothety {f : (Fin n → ℝ) → 𝕜} (hf : IsTest univ f) (x₀ : Fin n → ℝ)
    {s : ℝ} (hs : s ≠ 0) : IsTest univ (fun y => f (homothety x₀ s y)) := by
  refine ⟨hf.contDiff.comp (by unfold homothety; fun_prop), ?_, subset_univ _⟩
  have hK := hf.hasCompactSupport.isCompact.image (continuous_homothety x₀ s⁻¹)
  refine HasCompactSupport.of_support_subset_isCompact hK ?_
  intro y hy
  exact ⟨homothety x₀ s y, subset_tsupport _ hy, homothety_inv_homothety x₀ hs y⟩

/-- **Dilates of zero extensions.** Under the hypotheses of the zero-extension theorem, the
dilate `x ↦ u(x₀ + s (x - x₀))` lies in `D(A_max(ℝⁿ))`, with `A_max` the dilate of the
elementwise `A_s u_T` (`A_s` with first-order coefficients multiplied by `s`). -/
theorem dilL2_mem_maximal_univ {m : ℕ} [Fintype κ]
    (A : ConstCoeffOp (Fin (m + 1) → ℝ) 𝕜 ι κ) (hA : A.IsOrderLE 1) (M : SimplicialMesh (m + 1))
    {u : Affine.Simplex ℝ (Fin (m + 1) → ℝ) (m + 1) → ι → (Fin (m + 1) → ℝ) → 𝕜}
    (hu : ∀ T ∈ M.simplices, ∀ i, ContDiff ℝ 1 (u T i))
    (htr : ∀ F, M.IsInteriorFacet F → ∀ T ∈ M.cofaces F, ∀ T' ∈ M.cofaces F, ∀ ν,
      IsFaceNormal F ν → ∀ x ∈ convexHull ℝ (F : Set (Fin (m + 1) → ℝ)),
        A.symbolApply ν (fun i => u T i x) = A.symbolApply ν (fun i => u T' i x))
    (hbd : ∀ F, M.IsBoundaryFacet F → ∀ T ∈ M.cofaces F, ∀ ν, IsFaceNormal F ν →
      ∀ x ∈ convexHull ℝ (F : Set (Fin (m + 1) → ℝ)), A.symbolApply ν (fun i => u T i x) = 0)
    (x₀ : Fin (m + 1) → ℝ) {s : ℝ} (hs : 0 < s) :
    ∃ h : dilL2 M univ u (fun T hT i => (hu T hT i).continuous) x₀ hs.ne' ∈
        (A.maximal univ).domain,
      A.maximal univ ⟨_, h⟩ = dilL2 M univ (fun T => (A.scale s).apply (u T))
        (fun T hT j => (A.scale s).continuous_apply (hA.scale s) (hu T hT) j) x₀ hs.ne' := by
  obtain ⟨h1, h2⟩ := pieceL2_univ_mem_maximal_domain (A.scale s) (hA.scale s) M hu
    (fun F hF T hT T' hT' ν hν x hx => funext fun j => by
      rw [symbolApply_scale, symbolApply_scale, htr F hF T hT T' hT' ν hν x hx])
    (fun F hF T hT ν hν x hx => funext fun j => by
      rw [symbolApply_scale, hbd F hF T hT ν hν x hx, Pi.zero_apply, mul_zero])
  set c : ℝ := |(s ^ (m + 1))⁻¹|
  have key : ∀ φ : κ → (Fin (m + 1) → ℝ) → 𝕜, ∀ hφ : IsTestField univ φ,
      ⟪dilL2 M univ (fun T => (A.scale s).apply (u T))
          (fun T hT j => (A.scale s).continuous_apply (hA.scale s) (hu T hT) j) x₀ hs.ne',
        testField hφ⟫_𝕜 =
      ⟪dilL2 M univ u (fun T hT i => (hu T hT i).continuous) x₀ hs.ne',
        testField (A.formalAdj.isTestField_apply hφ)⟫_𝕜 := by
    intro φ hφ
    have hψ : IsTestField univ (fun j y => φ j (homothety x₀ s⁻¹ y)) := fun j =>
      (hφ j).comp_homothety x₀ (inv_ne_zero hs.ne')
    have hX := (A.scale s).maximal_inner_testField isOpen_univ ⟨_, h1⟩ hψ
    rw [h2, inner_pieceL2_testField_univ, inner_pieceL2_testField_univ] at hX
    rw [inner_dilL2_testField_univ, inner_dilL2_testField_univ]
    have hL : ∀ j, ∫ x, conj (pieceFun M (fun T => (A.scale s).apply (u T) j) (homothety x₀ s x)) *
        φ j x = (c : 𝕜) * ∫ y, conj (pieceFun M (fun T => (A.scale s).apply (u T) j) y) *
          φ j (homothety x₀ s⁻¹ y) := by
      intro j
      have := integral_comp_homothety (fun y => conj (pieceFun M (fun T => (A.scale s).apply
        (u T) j) y) * φ j (homothety x₀ s⁻¹ y)) x₀ s
      simp only [homothety_inv_homothety x₀ hs.ne'] at this
      rw [this, RCLike.real_smul_eq_coe_mul]
    have hR : ∀ i, ∫ x, conj (pieceFun M (fun T => u T i) (homothety x₀ s x)) *
        A.formalAdj.apply φ i x = (c : 𝕜) * ∫ y, conj (pieceFun M (fun T => u T i) y) *
          (A.scale s).formalAdj.apply (fun j y => φ j (homothety x₀ s⁻¹ y)) i y := by
      intro i
      have := integral_comp_homothety (fun y => conj (pieceFun M (fun T => u T i) y) *
        A.formalAdj.apply φ i (homothety x₀ s⁻¹ y)) x₀ s
      simp only [homothety_inv_homothety x₀ hs.ne'] at this
      rw [this, RCLike.real_smul_eq_coe_mul]
      congr 2
      funext y
      rw [formalAdj_scale]
      congr 1
      exact (apply_scale_comp_homothety A.formalAdj hs.ne' x₀ (fun j => (hφ j).contDiff) i y).symm
    simp only [hL, hR, ← Finset.mul_sum]
    rw [hX]
  have hmem := (A.mem_maximal_domain_iff isOpen_univ).2 ⟨_, key⟩
  exact ⟨hmem, A.maximal_apply_eq isOpen_univ ⟨_, hmem⟩ key⟩

end Feec.FiniteElement

namespace Feec.FiniteElement

open Feec.Domain Feec.Mesh ConstCoeffOp Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} {n : ℕ}

theorem isCompact_closure_domain (M : SimplicialMesh n) : IsCompact (closure M.domain) := by
  rw [← M.biUnion_closedInterior]
  exact M.simplices.finite_toSet.isCompact_biUnion fun T _ => T.isCompact_closedInterior

theorem measurable_pieceFun (M : SimplicialMesh n)
    {v : Affine.Simplex ℝ (Fin n → ℝ) n → (Fin n → ℝ) → 𝕜}
    (hv : ∀ T ∈ M.simplices, Continuous (v T)) : Measurable (pieceFun M v) := by
  unfold pieceFun
  exact Finset.measurable_sum _ fun T hT =>
    (hv T hT).measurable.indicator isOpen_interior.measurableSet

/-- Almost every point of `Ω` lies in the interior of an element. -/
theorem ae_mem_interior (M : SimplicialMesh n) (hΩ : MeasurableSet M.domain) :
    ∀ᵐ x ∂volume.restrict M.domain, ∃ T ∈ M.simplices, x ∈ interior T.closedInterior := by
  have hnull : volume (⋃ T ∈ M.simplices, frontier T.closedInterior) = 0 :=
    (measure_biUnion_null_iff M.simplices.countable_toSet).2 fun T _ =>
      Convex.addHaar_frontier volume (Feec.Mesh.convex_closedInterior T)
  have h := measure_eq_zero_iff_ae_notMem.1 hnull
  filter_upwards [ae_restrict_mem hΩ, ae_restrict_of_ae h] with x hxΩ hx
  have hx' : x ∈ ⋃ T ∈ M.simplices, T.closedInterior := by
    rw [M.biUnion_closedInterior]; exact subset_closure hxΩ
  obtain ⟨T, hT, hxT⟩ := Set.mem_iUnion₂.1 hx'
  refine ⟨T, hT, ?_⟩
  by_contra hint
  exact hx (Set.mem_iUnion₂.2 ⟨T, hT, ⟨T.isClosed_closedInterior.closure_eq.symm ▸ hxT, hint⟩⟩)

theorem norm_pieceFun_le (M : SimplicialMesh n)
    {v : Affine.Simplex ℝ (Fin n → ℝ) n → (Fin n → ℝ) → 𝕜} {C : Affine.Simplex ℝ (Fin n → ℝ) n → ℝ}
    (hC : ∀ T ∈ M.simplices, ∀ y ∈ T.closedInterior, ‖v T y‖ ≤ C T)
    (hC0 : ∀ T ∈ M.simplices, 0 ≤ C T) (y : Fin n → ℝ) :
    ‖pieceFun M v y‖ ≤ ∑ T ∈ M.simplices, C T := by
  unfold pieceFun
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun T hT => ?_)
  by_cases hy : y ∈ interior T.closedInterior
  · rw [Set.indicator_of_mem hy]; exact hC T hT y (interior_subset hy)
  · rw [Set.indicator_of_notMem hy, norm_zero]; exact hC0 T hT

/-- **Continuity of dilations on piecewise fields**: for a family `v_s` of piecewise fields
depending continuously on `s`, the dilates `x ↦ v_{s_k}(x₀ + s_k (x - x₀))` converge in
`L²(Ω)` to `v₁` as `s_k → 1`. -/
theorem tendsto_eLpNorm_pieceFun_homothety (M : SimplicialMesh n) (hΩ : MeasurableSet M.domain)
    {v : ℝ → Affine.Simplex ℝ (Fin n → ℝ) n → (Fin n → ℝ) → 𝕜}
    (hv : ∀ T ∈ M.simplices, Continuous fun p : ℝ × (Fin n → ℝ) => v p.1 T p.2)
    (x₀ : Fin n → ℝ) {s : ℕ → ℝ} (hs : Tendsto s atTop (𝓝 1))
    (hs12 : ∀ k, s k ∈ Set.Icc (1 : ℝ) 2) :
    Tendsto (fun k => eLpNorm ((fun x => pieceFun M (v (s k)) (homothety x₀ (s k) x)) -
      pieceFun M (v 1)) 2 (volume.restrict M.domain)) atTop (𝓝 0) := by
  classical
  have : IsFiniteMeasure (volume.restrict M.domain) := isFiniteMeasure_restrict.2
    ((isCompact_closure_domain M).isBounded.subset subset_closure).measure_lt_top.ne
  have hvc : ∀ T ∈ M.simplices, ∀ r, Continuous (v r T) := fun T hT r =>
    (hv T hT).comp (continuous_const.prodMk continuous_id)
  have hb : ∀ T ∈ M.simplices, ∃ C, 0 ≤ C ∧
      ∀ p ∈ Set.Icc (1 : ℝ) 2 ×ˢ T.closedInterior, ‖v p.1 T p.2‖ ≤ C := fun T hT => by
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod T.isCompact_closedInterior).exists_bound_of_continuousOn
      (hv T hT).continuousOn
    exact ⟨max C 0, le_max_right _ _, fun p hp => (hC p hp).trans (le_max_left _ _)⟩
  choose! C hC0 hC using hb
  have hbound : ∀ k x, ‖pieceFun M (v (s k)) (homothety x₀ (s k) x)‖ ≤ ∑ T ∈ M.simplices, C T :=
    fun k x => norm_pieceFun_le M (fun T hT y hy => hC T hT (s k, y) ⟨hs12 k, hy⟩) hC0 _
  have hmeas : ∀ k, AEStronglyMeasurable (fun x => pieceFun M (v (s k)) (homothety x₀ (s k) x))
      (volume.restrict M.domain) := fun k =>
    ((measurable_pieceFun M fun T hT => hvc T hT (s k)).comp
      (continuous_homothety x₀ (s k)).measurable).aestronglyMeasurable
  refine tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num) hmeas
    (memLp_pieceFun M (fun T hT => hvc T hT 1) _) ?_ ?_
  · refine unifIntegrable_of (by norm_num) (by norm_num) hmeas fun ε _ =>
      ⟨Real.toNNReal ((∑ T ∈ M.simplices, C T) + 1), fun k => ?_⟩
    have : ({x | Real.toNNReal ((∑ T ∈ M.simplices, C T) + 1) ≤
        ‖pieceFun M (v (s k)) (homothety x₀ (s k) x)‖₊}.indicator
        fun x => pieceFun M (v (s k)) (homothety x₀ (s k) x)) = 0 := by
      funext x
      refine Set.indicator_of_notMem (fun hx => ?_) _
      have hx' : (∑ T ∈ M.simplices, C T) + 1 ≤ ‖pieceFun M (v (s k)) (homothety x₀ (s k) x)‖ := by
        have := (Real.toNNReal_le_iff_le_coe).1 hx
        simpa using this
      linarith [hbound k x]
    rw [this, eLpNorm_zero]
    exact zero_le
  · filter_upwards [ae_mem_interior M hΩ] with x ⟨T, hT, hx⟩
    have hg : Tendsto (fun k => homothety x₀ (s k) x) atTop (𝓝 x) := by
      have hc : Continuous fun r : ℝ => homothety x₀ r x := by unfold homothety; fun_prop
      have := (hc.tendsto 1).comp hs
      simp only [homothety, one_smul, add_sub_cancel] at this
      exact this
    have hlim : Tendsto (fun k => v (s k) T (homothety x₀ (s k) x)) atTop (𝓝 (v 1 T x)) :=
      ((hv T hT).tendsto (1, x)).comp (hs.prodMk_nhds hg)
    rw [pieceFun_of_mem_interior M _ hT hx]
    refine hlim.congr' ?_
    filter_upwards [hg.eventually (isOpen_interior.mem_nhds hx)] with k hk
    rw [pieceFun_of_mem_interior M _ hT hk]

theorem _root_.Feec.Domain.ConstCoeffOp.scale_one {E : Type*} (A : ConstCoeffOp E 𝕜 ι κ) :
    A.scale 1 = A := by
  cases A
  simp only [ConstCoeffOp.scale, RCLike.ofReal_one, one_pow, one_mul]
  congr 1
  funext j i
  exact List.map_id' _

theorem _root_.Feec.Domain.ConstCoeffOp.continuous_scale_apply [Fintype ι]
    (A : ConstCoeffOp (Fin n → ℝ) 𝕜 ι κ) (hA : A.IsOrderLE 1) {f : ι → (Fin n → ℝ) → 𝕜}
    (hf : ∀ i, ContDiff ℝ 1 (f i)) (j : κ) :
    Continuous fun p : ℝ × (Fin n → ℝ) => (A.scale p.1).apply f j p.2 := by
  simp only [ConstCoeffOp.apply, ConstCoeffOp.scale, applyEntry_map_scale]
  refine continuous_finsetSum _ fun i _ => ?_
  refine continuous_list_sum _ fun t ht => ?_
  have h1 := contDiff_iterDeriv_of_le (hf i) t.1 (M := 0) (by simpa using hA j i t ht)
  exact (((RCLike.continuous_ofReal.comp continuous_fst).pow _).mul continuous_const).mul
    (h1.continuous.comp continuous_snd)

theorem pieceFun_eq_zero_of_forall_notMem {F : Type*} [AddCommMonoid F] (M : SimplicialMesh n)
    (v : Affine.Simplex ℝ (Fin n → ℝ) n → (Fin n → ℝ) → F) {y : Fin n → ℝ}
    (hy : ∀ T ∈ M.simplices, y ∉ interior T.closedInterior) : pieceFun M v y = 0 :=
  Finset.sum_eq_zero fun T hT => Set.indicator_of_notMem (hy T hT) _

theorem restrictL2F_dilL2 (M : SimplicialMesh n) (S : Set (Fin n → ℝ))
    (v : Affine.Simplex ℝ (Fin n → ℝ) n → ι → (Fin n → ℝ) → 𝕜)
    (hv : ∀ T ∈ M.simplices, ∀ i, Continuous (v T i)) (x₀ : Fin n → ℝ) {s : ℝ} (hs : s ≠ 0) :
    restrictL2F S (dilL2 M univ v hv x₀ hs) = dilL2 M S v hv x₀ hs := by
  refine PiLp.ext fun i => Lp.ext ?_
  have h1 := (ae_restrict_iff' MeasurableSet.univ).1 (coeFn_dilL2 M univ v hv x₀ hs i)
  filter_upwards [coeFn_restrictL2F S (dilL2 M univ v hv x₀ hs) i, ae_restrict_of_ae h1,
    coeFn_dilL2 M S v hv x₀ hs i] with x ha hb hc
  rw [ha, hb (mem_univ x), hc]

variable [Fintype ι]

/-- **Vanishing `A`-traces give the minimal domain** (`Ω` strictly star-shaped). Under the
hypotheses of `pieceL2_mem_maximal_domain`, if moreover the `A`-traces vanish on the boundary
facets and `Ω` is strictly star-shaped with respect to `x₀`
(`x₀ + t (x - x₀) ∈ Ω` for `x ∈ closure Ω`, `0 ≤ t < 1`; e.g. `Ω` convex, or star-shaped with
respect to a ball), then `u ∈ D(A_min(Ω))`. Proof: the dilates of the extension by zero lie in
`D(A_max(ℝⁿ))` and are supported in compact subsets of `Ω`, hence in `D(A_min(Ω))`
(`Feec.Domain.ConstCoeffOp.mem_minimal_of_support_subset`); they converge to `u` in the graph
norm, and `A_min` is closed. -/
theorem pieceL2_mem_minimal_domain [NeZero n] [Fintype κ]
    (A : ConstCoeffOp (Fin n → ℝ) 𝕜 ι κ) (hA : A.IsOrderLE 1) (M : SimplicialMesh n)
    (hΩ : IsOpen M.domain) {u : Affine.Simplex ℝ (Fin n → ℝ) n → ι → (Fin n → ℝ) → 𝕜}
    (hu : ∀ T ∈ M.simplices, ∀ i, ContDiff ℝ 1 (u T i))
    (htr : ∀ F, M.IsInteriorFacet F → ∀ T ∈ M.cofaces F, ∀ T' ∈ M.cofaces F, ∀ ν,
      IsFaceNormal F ν → ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)),
        A.symbolApply ν (fun i => u T i x) = A.symbolApply ν (fun i => u T' i x))
    (hbd : ∀ F, M.IsBoundaryFacet F → ∀ T ∈ M.cofaces F, ∀ ν, IsFaceNormal F ν →
      ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)), A.symbolApply ν (fun i => u T i x) = 0)
    (x₀ : Fin n → ℝ)
    (hstar : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ M.domain) :
    ∃ h : pieceL2 M M.domain u (fun T hT i => (hu T hT i).continuous) ∈
        (A.minimal M.domain).domain,
      A.minimal M.domain ⟨_, h⟩ = pieceL2 M M.domain (fun T => A.apply (u T))
        (fun T hT j => A.continuous_apply hA (hu T hT) j) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.ne n; omega⟩
  set Ω := M.domain
  set s : ℕ → ℝ := fun k => 1 + 1 / ((k : ℝ) + 1)
  have hspos : ∀ k, 0 < s k := fun k => by positivity
  have hs1 : ∀ k, 1 < s k := fun k => by
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    simp only [s]; linarith
  have hs12 : ∀ k, s k ∈ Set.Icc (1 : ℝ) 2 := fun k => ⟨(hs1 k).le, by
    simp only [s]
    have : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [k.cast_nonneg (α := ℝ)]
    linarith⟩
  have hslim : Tendsto s atTop (𝓝 1) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
    simpa [s] using this
  have hcu : ∀ T ∈ M.simplices, ∀ i, Continuous (u T i) := fun T hT i => (hu T hT i).continuous
  have hcA : ∀ r, ∀ T ∈ M.simplices, ∀ j, Continuous ((A.scale r).apply (u T) j) :=
    fun r T hT j => (A.scale r).continuous_apply (hA.scale r) (hu T hT) j
  -- the dilates lie in the graph of `A_min(Ω)`
  have hgraph : ∀ k, (dilL2 M Ω u hcu x₀ (hspos k).ne',
      dilL2 M Ω (fun T => (A.scale (s k)).apply (u T)) (hcA (s k)) x₀ (hspos k).ne') ∈
        (A.minimal Ω).graph := by
    intro k
    obtain ⟨hD, hW⟩ := dilL2_mem_maximal_univ A hA M hu htr hbd x₀ (hspos k)
    set K := homothety x₀ (s k)⁻¹ '' closure Ω
    have hK : IsCompact K := (isCompact_closure_domain M).image (continuous_homothety x₀ _)
    have hKΩ : K ⊆ Ω := by
      rintro _ ⟨x, hx, rfl⟩
      exact hstar x hx _ (inv_nonneg.2 (hspos k).le) (inv_lt_one_of_one_lt₀ (hs1 k))
    have hsupp : ∀ i, ∀ᵐ x, x ∉ K →
        (dilL2 M univ u hcu x₀ (hspos k).ne' : L2F 𝕜 univ ι) i x = 0 := by
      intro i
      have h1 := (ae_restrict_iff' MeasurableSet.univ).1 (coeFn_dilL2 M univ u hcu x₀
        (hspos k).ne' i)
      filter_upwards [h1] with x hx hxK
      rw [hx (mem_univ x)]
      refine pieceFun_eq_zero_of_forall_notMem M _ fun T hT hint => hxK ?_
      refine ⟨homothety x₀ (s k) x, ?_, homothety_inv_homothety x₀ (hspos k).ne' x⟩
      rw [← M.biUnion_closedInterior]
      exact Set.mem_iUnion₂.2 ⟨T, hT, interior_subset hint⟩
    obtain ⟨hmin, hval⟩ := A.mem_minimal_of_support_subset hΩ hK hKΩ ⟨_, hD⟩ hsupp
    rw [LinearPMap.mem_graph_iff]
    refine ⟨⟨_, hmin⟩, restrictL2F_dilL2 M Ω u hcu x₀ (hspos k).ne', ?_⟩
    rw [hval]
    change restrictL2F Ω (A.maximal univ ⟨_, hD⟩) = _
    rw [hW, restrictL2F_dilL2]
  -- the dilates converge in the graph norm
  have hlim1 : Tendsto (fun k => dilL2 M Ω u hcu x₀ (hspos k).ne') atTop
      (𝓝 (pieceL2 M Ω u hcu)) := by
    refine tendsto_toL2F _ _ fun i => ?_
    have h := tendsto_eLpNorm_pieceFun_homothety M hΩ.measurableSet
      (v := fun _ T => u T i) (fun T hT => (hcu T hT i).comp continuous_snd) x₀ hslim hs12
    refine h.congr fun k => eLpNorm_congr_ae ?_
    filter_upwards [coeFn_pieceL2 M Ω u hcu i] with x hx
    simp [hx]
  have hlim2 : Tendsto (fun k => dilL2 M Ω (fun T => (A.scale (s k)).apply (u T)) (hcA (s k)) x₀
      (hspos k).ne') atTop (𝓝 (pieceL2 M Ω (fun T => A.apply (u T))
        (fun T hT j => A.continuous_apply hA (hu T hT) j))) := by
    refine tendsto_toL2F _ _ fun j => ?_
    have h := tendsto_eLpNorm_pieceFun_homothety M hΩ.measurableSet
      (v := fun r T => (A.scale r).apply (u T) j)
      (fun T hT => A.continuous_scale_apply hA (hu T hT) j) x₀ hslim hs12
    simp only [ConstCoeffOp.scale_one] at h
    refine h.congr fun k => eLpNorm_congr_ae ?_
    filter_upwards [coeFn_pieceL2 M Ω (fun T => A.apply (u T))
      (fun T hT j => A.continuous_apply hA (hu T hT) j) j] with x hx
    simp [hx]
  have hmem := (A.isClosed_minimal hΩ).mem_of_tendsto (hlim1.prodMk_nhds hlim2)
    (Eventually.of_forall hgraph)
  rw [SetLike.mem_coe, LinearPMap.mem_graph_iff] at hmem
  obtain ⟨y, hy1, hy2⟩ := hmem
  simp only at hy1 hy2
  refine ⟨hy1 ▸ y.2, ?_⟩
  rw [← hy2]
  congr 1
  exact Subtype.ext hy1.symm

end Feec.FiniteElement

namespace Feec.FiniteElement

open Feec.Domain Feec.Mesh ConstCoeffOp ExteriorFibre

variable {n : ℕ}

/-- **`H̊Λᵏ`-conformity of piecewise smooth real `k`-forms** (`Ω` strictly star-shaped): if the
tangential traces agree on the interior facets and vanish on the boundary facets, then
`ω ∈ H̊Λᵏ(Ω) = D(d_min)`, and `d_min ω` is the elementwise exterior derivative. -/
theorem extDeriv_pieceL2_mem_minimal_domain [NeZero n] (k : ℕ) (M : SimplicialMesh n)
    (hΩ : IsOpen M.domain) {η : Affine.Simplex ℝ (Fin n → ℝ) n → FormField n}
    (hη : ∀ T ∈ M.simplices, ContDiff ℝ 1 (η T)) (hdeg : ∀ T ∈ M.simplices, ∀ x, IsDeg k (η T x))
    (htr : ∀ F, M.IsInteriorFacet F → ∀ T ∈ M.cofaces F, ∀ T' ∈ M.cofaces F,
      ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)), TangentialTraceEq F k (η T x) (η T' x))
    (hbd : ∀ F, M.IsBoundaryFacet F → ∀ T ∈ M.cofaces F,
      ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)), TangentialTraceEq F k (η T x) 0)
    (x₀ : Fin n → ℝ)
    (hstar : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ M.domain) :
    ∃ h : pieceL2 M M.domain (fun T => formComp (k := k) (η T))
        (fun T hT s => continuous_formComp (hη T hT).continuous s) ∈
        ((extDerivOp ℝ n k).minimal M.domain).domain,
      (extDerivOp ℝ n k).minimal M.domain ⟨_, h⟩ =
        pieceL2 M M.domain (fun T => formComp (k := (k : ℤ) + 1) (extDeriv (η T)))
          (fun T hT t => continuous_formComp (continuous_extDeriv (hη T hT)) t) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.ne n; omega⟩
  have hu : ∀ T ∈ M.simplices, ∀ s : formIdx (m + 1) k, ContDiff ℝ 1 (formComp (η T) s) :=
    fun T hT s => contDiff_pi.1 (hη T hT) s.1
  have hwedge : ∀ T ∈ M.simplices, ∀ x ν,
      (extDerivOp ℝ (m + 1) k).symbolApply ν (fun s => formComp (η T) s x) =
        fun t => wedge ν (η T x) t.1 := fun T hT x ν => funext fun t => by
    rw [symbolApply_extDerivOp, formExt_formComp (hdeg T hT x)]
    rfl
  obtain ⟨h, hval⟩ := pieceL2_mem_minimal_domain (extDerivOp ℝ (m + 1) k)
    (extDerivOp_isOrderLE k) M hΩ hu
    (fun F hF T hT T' hT' ν hν x hx => by
      rw [hwedge T (M.mem_cofaces.1 hT).1, hwedge T' (M.mem_cofaces.1 hT').1,
        wedge_eq_of_tangentialTraceEq (M.mem_cofaces.1 hT).2 hF.1.1
          (hdeg T (M.mem_cofaces.1 hT).1 x) (hdeg T' (M.mem_cofaces.1 hT').1 x)
          (htr F hF T hT T' hT' x hx) hν])
    (fun F hF T hT ν hν x hx => by
      rw [hwedge T (M.mem_cofaces.1 hT).1,
        wedge_eq_of_tangentialTraceEq (M.mem_cofaces.1 hT).2 hF.1.1
          (hdeg T (M.mem_cofaces.1 hT).1 x) (fun _ _ => rfl) (hbd F hF T hT x hx) hν]
      funext t
      simp [wedge_apply])
    x₀ hstar
  refine ⟨h, hval.trans (pieceL2_congr M _ _ _ fun T hT => ?_)⟩
  funext t x
  exact extDerivOp_apply_formComp (hdeg T hT) t x

end Feec.FiniteElement
