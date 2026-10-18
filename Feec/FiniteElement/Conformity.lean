module

public import Feec.FiniteElement.MeshDivergence
public import Feec.Domain.DeRham
public import Feec.Domain.WholeSpace
public import Mathlib.LinearAlgebra.CrossProduct

/-!
# Conformity of piecewise smooth fields on simplicial meshes

Let `M` be a conforming simplicial mesh of an open set `Ω ⊆ ℝⁿ` (`n ≥ 1`) and `A` a first-order
constant-coefficient operator (`Feec.Domain.ConstCoeffOp`) with principal symbol
`σ_A(ν)` (`ConstCoeffOp.symbol`; `(σ_A(ν) w)ⱼ = Σᵢ Σ_{([v], c) ∈ Aⱼᵢ} c (v · ν) wᵢ`). A field `u`
given on each closed element `T` by a `C¹` field `u_T` (classical traces only) whose
**`A`-traces** `σ_A(ν_F) u_T` agree from both sides of every interior facet `F` lies in the
domain of the maximal realization `A_max(Ω)`, and `A_max u` is the elementwise `A u_T`
(`ConstCoeffOp.pieceL2_mem_maximal_domain`). If moreover the `A`-traces vanish on the boundary
facets, the extension of `u` by zero lies in `D(A_max(ℝⁿ)) = D(A_min(ℝⁿ))`
(`ConstCoeffOp.pieceL2_univ_mem_maximal_domain`), and when `Ω` is strictly star-shaped (e.g.
convex, in particular a cube), `u ∈ D(A_min(Ω))` (`ConstCoeffOp.pieceL2_mem_minimal_domain`).

The proof is elementwise integration by parts: for a test field `φ`,
`Σⱼ conj (A u)ⱼ φⱼ - Σᵢ conj uᵢ (Aᵗ φ)ᵢ = div G` with `G · ν = Σⱼ φⱼ conj (σ_A(ν) u)ⱼ`
(`ConstCoeffOp.conj_apply_mul_sub_eq_sum_partialDeriv`), and the divergence theorem on the mesh
(`Feec.FiniteElement.sum_setIntegral_divergence_eq_zero`): the face terms cancel across interior
facets by the trace condition and vanish on boundary facets, where `φ = 0`.

Instances: the gradient (continuity), the curl (continuity of `ν × u`, the tangential trace) and
the divergence (continuity of `ν · u`, the normal trace), and the exterior derivative on
`k`-forms (continuity of `ν ∧ u`; for real forms, equivalently of the pullback to the facets,
`Feec.FiniteElement.extDerivOp_conforming`).

## Main definitions

* `ConstCoeffOp.symbol A ν`, `ConstCoeffOp.symbolApply A ν w`: the principal symbol.
* `Feec.FiniteElement.pieceFun M v`: the piecewise function `Σ_T 𝟙_{int T} v_T`, and
  `Feec.FiniteElement.pieceL2 M S u`: the piecewise field as an element of `L²(S; 𝕜^ι)`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §5 (piecewise smooth forms with single-valued traces lie in `HΛᵏ`)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7
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

/-- The symbol of the gradient: `σ_grad(ν) w = w ⊗ ν`. -/
theorem symbolApply_gradOp (ν : Fin n → ℝ) (w : Fin m → 𝕜) (ij : Fin m × Fin n) :
    (gradOp n m : ConstCoeffOp (Fin n → ℝ) 𝕜 _ _).symbolApply ν w ij = (ν ij.2 : 𝕜) * w ij.1 := by
  simp [symbolApply, symbol, gradOp, symbolEntry, dirPair_coordDir, apply_ite]

/-- The symbol of the divergence: `σ_div(ν) B = B ν` (the normal component). -/
theorem symbolApply_divOp (ν : Fin n → ℝ) (B : Fin m × Fin n → 𝕜) (i : Fin m) :
    (divOp n m : ConstCoeffOp (Fin n → ℝ) 𝕜 _ _).symbolApply ν B i =
      ∑ j, (ν j : 𝕜) * B (i, j) := by
  simp [symbolApply, symbol, divOp, symbolEntry, dirPair_coordDir, apply_ite, Fintype.sum_prod_type]

theorem symbolEntry_ite (p : Prop) [Decidable p] (P Q : List (List (Fin n → ℝ) × 𝕜))
    (ν : Fin n → ℝ) :
    symbolEntry (if p then P else Q) ν = if p then symbolEntry P ν else symbolEntry Q ν := by
  split_ifs <;> rfl

@[simp] theorem symbolEntry_singleton (vs : List (Fin n → ℝ)) (c : 𝕜) (ν : Fin n → ℝ) :
    symbolEntry [(vs, c)] ν = c * dirPair vs ν := by
  simp [symbolEntry]

/-- The symbol of the curl: `σ_curl(ν) Φ = ν × Φ` (row-wise; the tangential trace). -/
theorem symbolApply_curlOp (ν : Fin 3 → ℝ) (Φ : Fin m × Fin 3 → 𝕜) (ik : Fin m × Fin 3) :
    (curlOp m : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).symbolApply ν Φ ik =
      ((fun l => (ν l : 𝕜)) ⨯₃ fun l => Φ (ik.1, l)) ik.2 := by
  obtain ⟨i, k⟩ := ik
  simp only [symbolApply, symbol, curlOp, Fintype.sum_prod_type, symbolEntry_ite,
    symbolEntry_singleton, symbolEntry_nil, dirPair_coordDir, ite_mul, zero_mul,
    Fin.sum_univ_three, cross_apply]
  fin_cases k <;> simp [Finset.sum_add_distrib] <;> ring

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

/-- **`H¹`-conformity** (Lagrange elements): piecewise `C¹` fields continuous across the interior
facets lie in `D(grad_max(Ω))`, with the elementwise gradient. -/
theorem gradOp_pieceL2_mem_maximal_domain [NeZero n] {m : ℕ} (M : SimplicialMesh n)
    (hΩ : IsOpen M.domain) {u : Affine.Simplex ℝ (Fin n → ℝ) n → Fin m → (Fin n → ℝ) → 𝕜}
    (hu : ∀ T ∈ M.simplices, ∀ i, ContDiff ℝ 1 (u T i))
    (hcont : ∀ F, M.IsInteriorFacet F → ∀ T ∈ M.cofaces F, ∀ T' ∈ M.cofaces F,
      ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)), ∀ i, u T i x = u T' i x) :
    ∃ h : pieceL2 M M.domain u (fun T hT i => (hu T hT i).continuous) ∈
        ((gradOp n m : ConstCoeffOp (Fin n → ℝ) 𝕜 _ _).maximal M.domain).domain,
      (gradOp n m : ConstCoeffOp (Fin n → ℝ) 𝕜 _ _).maximal M.domain ⟨_, h⟩ =
        pieceL2 M M.domain (fun T => (gradOp n m).apply (u T))
          (fun T hT j => (gradOp n m).continuous_apply gradOp_isOrderLE (hu T hT) j) :=
  pieceL2_mem_maximal_domain _ gradOp_isOrderLE M hΩ hu fun F hF T hT T' hT' _ _ x hx =>
    funext fun ij => by rw [symbolApply_gradOp, symbolApply_gradOp, hcont F hF T hT T' hT' x hx]

/-- **`H(div)`-conformity** (Raviart–Thomas elements): piecewise `C¹` (row-wise) vector fields
whose normal components `ν · u` agree across the interior facets lie in `D(div_max(Ω))`. -/
theorem divOp_pieceL2_mem_maximal_domain [NeZero n] {m : ℕ} (M : SimplicialMesh n)
    (hΩ : IsOpen M.domain)
    {u : Affine.Simplex ℝ (Fin n → ℝ) n → Fin m × Fin n → (Fin n → ℝ) → 𝕜}
    (hu : ∀ T ∈ M.simplices, ∀ i, ContDiff ℝ 1 (u T i))
    (hnormal : ∀ F, M.IsInteriorFacet F → ∀ T ∈ M.cofaces F, ∀ T' ∈ M.cofaces F, ∀ ν,
      IsFaceNormal F ν → ∀ x ∈ convexHull ℝ (F : Set (Fin n → ℝ)), ∀ i,
        ∑ j, (ν j : 𝕜) * u T (i, j) x = ∑ j, (ν j : 𝕜) * u T' (i, j) x) :
    ∃ h : pieceL2 M M.domain u (fun T hT i => (hu T hT i).continuous) ∈
        ((divOp n m : ConstCoeffOp (Fin n → ℝ) 𝕜 _ _).maximal M.domain).domain,
      (divOp n m : ConstCoeffOp (Fin n → ℝ) 𝕜 _ _).maximal M.domain ⟨_, h⟩ =
        pieceL2 M M.domain (fun T => (divOp n m).apply (u T))
          (fun T hT j => (divOp n m).continuous_apply divOp_isOrderLE (hu T hT) j) :=
  pieceL2_mem_maximal_domain _ divOp_isOrderLE M hΩ hu fun F hF T hT T' hT' ν hν x hx =>
    funext fun i => by
      rw [symbolApply_divOp, symbolApply_divOp, hnormal F hF T hT T' hT' ν hν x hx]

/-- **`H(curl)`-conformity** (Nédélec elements, `ℝ³`): piecewise `C¹` (row-wise) vector fields
whose tangential traces `ν × u` agree across the interior facets lie in `D(curl_max(Ω))`. -/
theorem curlOp_pieceL2_mem_maximal_domain {m : ℕ} (M : SimplicialMesh 3)
    (hΩ : IsOpen M.domain)
    {u : Affine.Simplex ℝ (Fin 3 → ℝ) 3 → Fin m × Fin 3 → (Fin 3 → ℝ) → 𝕜}
    (hu : ∀ T ∈ M.simplices, ∀ i, ContDiff ℝ 1 (u T i))
    (htan : ∀ F, M.IsInteriorFacet F → ∀ T ∈ M.cofaces F, ∀ T' ∈ M.cofaces F, ∀ ν,
      IsFaceNormal F ν → ∀ x ∈ convexHull ℝ (F : Set (Fin 3 → ℝ)), ∀ i,
        (fun l => (ν l : 𝕜)) ⨯₃ (fun l => u T (i, l) x) =
          (fun l => (ν l : 𝕜)) ⨯₃ (fun l => u T' (i, l) x)) :
    ∃ h : pieceL2 M M.domain u (fun T hT i => (hu T hT i).continuous) ∈
        ((curlOp m : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).maximal M.domain).domain,
      (curlOp m : ConstCoeffOp (Fin 3 → ℝ) 𝕜 _ _).maximal M.domain ⟨_, h⟩ =
        pieceL2 M M.domain (fun T => (curlOp m).apply (u T))
          (fun T hT j => (curlOp m).continuous_apply curlOp_isOrderLE (hu T hT) j) :=
  pieceL2_mem_maximal_domain _ curlOp_isOrderLE M hΩ hu fun F hF T hT T' hT' ν hν x hx =>
    funext fun ik => by
      rw [symbolApply_curlOp, symbolApply_curlOp, htan F hF T hT T' hT' ν hν x hx]

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
