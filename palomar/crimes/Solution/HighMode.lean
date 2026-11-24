module

public import Solution.Defs
public import Feec.Counterexamples.ClassicalRegularity
public import Feec.ForMathlib.Analysis.Inequalities

/-!
# The witness of the defect in the graph norm

The complex `ℓ²(ℕ, ℝ)` in every degree with `d⁰ = A⁻¹ = diag(k + 1)` (closed, densely defined
and onto; `Feec.Counterexamples.Fredholm.invDiag`) and all other differentials `0`
(`HighMode.complex`), on the window `ℓ² --A⁻¹--> ℓ²` (`𝐝 (x⁰, x¹) = (0, A⁻¹ x⁰)`). The discrete
spaces `Xₙ = E ⊕ E` are the spans `E = span{e₀, …, eₙ}` of the modes `k ≤ n` in both degrees
(`Feec.Counterexamples.ClassicalRegularity.trunc`), read by the inclusions with the highest mode of
degree `0` multiplied by `√2`, `iₙ (u, w) = (u + (√2 - 1) uₙ eₙ, w)` (`HighMode.incl`), with the
discrete differential `𝐝ₙ (u, w) = (0, A⁻¹ (u + (√2 - 1) uₙ eₙ))` that makes `iₙ` a cochain map
(`HighMode.totalD_incl`) and the cochain projections `πₙ x = (P x⁰ + (1/√2 - 1) (P x⁰)ₙ eₙ, P x¹)`,
`P` the orthogonal projection on `E` (`HighMode.family`, `HighMode.proj`): `iₙ πₙ = P ⊕ P`, so
`iₙ πₙ → 1` (`HighMode.tendsto_incl_proj`). The reading maps double the square norm of the
highest mode of degree `0`, `⟪iₙ v, iₙ w⟫ = ⟪v, w⟫ + v⁰ₙ w⁰ₙ` (`HighMode.inner_incl`), so
`1 - iₙ* iₙ` is minus the projection on that mode (`HighMode.one_sub_J_apply`) and
`‖1 - iₙ* iₙ‖ = 1` (`HighMode.norm_one_sub_J`), while `𝐝ₙ` is `(n + 1) √2` on it:
`‖(1 - iₙ* iₙ) v‖ ≤ (‖v‖ + ‖𝐝ₙ v‖) / (n + 1)` (`HighMode.norm_one_sub_J_apply_le`). So `𝐝` is
unbounded: `‖𝐝 iₙ (eₙ, 0)‖ ≥ (n + 1) √2` while `‖iₙ (eₙ, 0)‖ ≤ 2` (`HighMode.not_bounded_totalD`).

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012], §3

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace lp
open Filter Topology Set LinearPMap
open Feec.Counterexamples.Fredholm (invDiag invDiag_isClosed dense_invDiag_domain invDiag_apply
  range_invDiag)
open Feec.Counterexamples.ClassicalRegularity (trunc truncSum trunc_le_domain invDiag_mem_trunc
  starProjection_trunc truncSum_invDiag tendsto_truncSum)

@[expose] public noncomputable section

namespace FEEC.HighMode

/-- The differentials of the witness complex: `δ⁰ = A⁻¹ = diag(k + 1)`, `δⁱ = 0` for `i ≠ 0`. -/
def δ (i : ℤ) : ℓ²(ℕ, ℝ) →ₗ.[ℝ] ℓ²(ℕ, ℝ) := if i = 0 then invDiag ℝ else 0

theorem δ_zero : δ 0 = invDiag ℝ := by simp [δ]

theorem δ_of_ne {i : ℤ} (h : i ≠ 0) : δ i = 0 := by simp [δ, h]

theorem dense_δ (i : ℤ) : Dense ((δ i).domain : Set ℓ²(ℕ, ℝ)) := by
  by_cases h : i = 0
  · rw [h, δ_zero]; exact dense_invDiag_domain
  · rw [δ_of_ne h, LinearPMap.zero_domain, Submodule.top_coe]; exact dense_univ

theorem isClosed_δ (i : ℤ) : (δ i).IsClosed := by
  by_cases h : i = 0
  · rw [h, δ_zero]; exact invDiag_isClosed
  · rw [δ_of_ne h]; exact LinearPMap.isClosed_zero

theorem δ_mapsTo (i : ℤ) (x : (δ i).domain) : (δ i x : ℓ²(ℕ, ℝ)) ∈ (δ (i + 1)).domain := by
  by_cases h : i = 0
  · subst h
    rw [δ_of_ne (by norm_num : (0 : ℤ) + 1 ≠ 0), LinearPMap.zero_domain]
    exact Submodule.mem_top
  · rw [LinearPMap.apply_eq_zero_of_eq_zero (δ_of_ne h) x]
    exact Submodule.zero_mem _

theorem δ_comp (i : ℤ) (x : (δ i).domain) : δ (i + 1) ⟨δ i x, δ_mapsTo i x⟩ = 0 := by
  by_cases h : i = 0
  · subst h
    exact LinearPMap.apply_eq_zero_of_eq_zero (δ_of_ne (by norm_num)) _
  · have e : (⟨δ i x, δ_mapsTo i x⟩ : (δ (i + 1)).domain) = 0 :=
      Subtype.ext (LinearPMap.apply_eq_zero_of_eq_zero (δ_of_ne h) x)
    rw [e, LinearPMap.map_zero]

/-- The witness complex as a `Feec` complex. -/
def feecComplex : Feec.HilbertComplex ℝ (ComplexShape.up ℤ) fun _ : ℤ => ℓ²(ℕ, ℝ) :=
  Feec.HilbertComplex.ofSucc δ dense_δ isClosed_δ δ_mapsTo δ_comp

/-- **The witness complex**: `ℓ²(ℕ, ℝ)` in every degree, `d⁰ = A⁻¹ = diag(k + 1)`
(`Feec.Counterexamples.Fredholm.invDiag`), all other differentials `0`. -/
def complex : HilbertComplex ℝ fun _ : ℤ => ℓ²(ℕ, ℝ) :=
  ⟨feecComplex.d, feecComplex.shape, feecComplex.dense, feecComplex.closed, feecComplex.mapsTo,
    feecComplex.d_comp_d⟩

theorem d_succ (i : ℤ) : complex.d i (i + 1) = δ i := Feec.HilbertComplex.ofSuccD_succ δ i

theorem d_of_ne {i j : ℤ} (h : i + 1 ≠ j) : complex.d i j = 0 :=
  Feec.HilbertComplex.ofSuccD_of_ne δ h

theorem d_zero_one : complex.d 0 1 = invDiag ℝ := (d_succ 0).trans δ_zero

/-- The window `[0, 2)`: `ℓ² ⊕ ℓ²`. -/
abbrev T : Type := Total (fun _ : ℤ => ℓ²(ℕ, ℝ)) 0 2

/-- The component of degree `0` of a point of `D(𝐝)`, a point of `D(A⁻¹)`. -/
def fst (x : (complex.totalD 0 2).domain) : (invDiag ℝ).domain :=
  ⟨(x : T) 0, d_zero_one ▸ (x.2 0 1 : (x : T) 0 ∈ (complex.d 0 1).domain)⟩

/-- `(𝐝 x)⁰ = 0`. -/
theorem totalD_apply_zero (x : (complex.totalD 0 2).domain) : (complex.totalD 0 2 x : T) 0 = 0 := by
  change ∑ i : Fin 2, complex.d (0 + ((i : ℕ) : ℤ)) (0 + (((0 : Fin 2) : ℕ) : ℤ))
    ⟨(x : T) i, x.2 i 0⟩ = 0
  rw [Fin.sum_univ_two]
  change complex.d 0 0 ⟨(x : T) 0, x.2 0 0⟩ + complex.d 1 0 ⟨(x : T) 1, x.2 1 0⟩ = 0
  rw [LinearPMap.apply_eq_zero_of_eq_zero (d_of_ne (by norm_num)),
    LinearPMap.apply_eq_zero_of_eq_zero (d_of_ne (by norm_num)), add_zero]

/-- `(𝐝 x)¹ = A⁻¹ x⁰`. -/
theorem totalD_apply_one (x : (complex.totalD 0 2).domain) :
    (complex.totalD 0 2 x : T) 1 = invDiag ℝ (fst x) := by
  change ∑ i : Fin 2, complex.d (0 + ((i : ℕ) : ℤ)) (0 + (((1 : Fin 2) : ℕ) : ℤ))
    ⟨(x : T) i, x.2 i 1⟩ = _
  rw [Fin.sum_univ_two]
  change complex.d 0 1 ⟨(x : T) 0, x.2 0 1⟩ + complex.d 1 1 ⟨(x : T) 1, x.2 1 1⟩ = _
  rw [LinearPMap.apply_eq_zero_of_eq_zero (d_of_ne (i := 1) (j := 1) (by norm_num)), add_zero,
    LinearPMap.apply_eq_of_eq' d_zero_one]
  rfl

theorem mem_totalD_domain {x : T} (h0 : (x : T) 0 ∈ (invDiag ℝ).domain) :
    x ∈ (complex.totalD 0 2).domain := by
  intro i j
  fin_cases i <;> fin_cases j
  · change (x : T) 0 ∈ (complex.d 0 0).domain
    rw [d_of_ne (by norm_num)]; exact Submodule.mem_top
  · change (x : T) 0 ∈ (complex.d 0 1).domain
    rw [d_zero_one]; exact h0
  · change (x : T) 1 ∈ (complex.d 1 0).domain
    rw [d_of_ne (by norm_num)]; exact Submodule.mem_top
  · change (x : T) 1 ∈ (complex.d 1 1).domain
    rw [d_of_ne (by norm_num)]; exact Submodule.mem_top

/-- The boundaries of degree `1` are all of `ℓ²` (`A⁻¹` is onto), so closed. -/
theorem isClosed_boundaries : ∀ i : Fin 2, 0 < (i : ℕ) →
    IsClosed (complex.boundaries (0 + (i : ℕ)) : Set ℓ²(ℕ, ℝ)) := by
  intro i hi
  fin_cases i
  · exact absurd hi (lt_irrefl 0)
  · change IsClosed (LinearMap.range (complex.d 0 1).toFun : Set ℓ²(ℕ, ℝ))
    rw [d_zero_one, range_invDiag, Submodule.top_coe]
    exact isClosed_univ

/-! ### The discrete spaces -/

variable (n : ℕ)

/-- The modes `0, …, n` of one degree: `span{e₀, …, eₙ}` (`ClassicalRegularity.trunc`). -/
abbrev E : Type := trunc ℝ (n + 1)

/-- The discrete space `Xₙ = E ⊕ E` (degrees `0` and `1`). -/
abbrev X : Type := PiLp 2 fun _ : Fin 2 => E n

/-- The highest mode `eₙ` of `E`. -/
def top : E n := ⟨lp.single 2 n 1, fun _ hm => lp.single_apply_ne 2 n 1 (by omega)⟩

theorem inner_top_left (u : E n) : ⟪top n, u⟫_ℝ = (u : ℓ²(ℕ, ℝ)) n := by
  rw [Submodule.coe_inner, top, lp.inner_single_left]
  simp

/-- The rescaling `u ↦ u + (t - 1) uₙ eₙ` of the highest mode by `t`. -/
def sc (t : ℝ) : E n →L[ℝ] E n := LinearMap.toContinuousLinearMap
  { toFun := fun u => u + ((t - 1) * (u : ℓ²(ℕ, ℝ)) n) • top n
    map_add' := fun u w => by
      rw [Submodule.coe_add, lp.coeFn_add, Pi.add_apply, mul_add, add_smul]
      abel
    map_smul' := fun r u => by
      rw [Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
        smul_add, smul_smul, mul_left_comm] }

variable {n} in
theorem sc_apply (t : ℝ) (u : E n) : sc n t u = u + ((t - 1) * (u : ℓ²(ℕ, ℝ)) n) • top n := rfl

variable {n} in
/-- `sc t` multiplies the highest coordinate by `t` and fixes the others. -/
theorem sc_apply_coord (t : ℝ) (u : E n) (m : ℕ) :
    (sc n t u : ℓ²(ℕ, ℝ)) m = if m = n then t * (u : ℓ²(ℕ, ℝ)) m else (u : ℓ²(ℕ, ℝ)) m := by
  rw [sc_apply, Submodule.coe_add, Submodule.coe_smul, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply,
    Pi.smul_apply, top, lp.single_apply]
  split_ifs with h
  · subst h; simp; ring
  · simp [Pi.single_eq_of_ne h]

variable {n} in
theorem sc_apply_top (t : ℝ) (u : E n) : (sc n t u : ℓ²(ℕ, ℝ)) n = t * (u : ℓ²(ℕ, ℝ)) n := by
  rw [sc_apply_coord]; simp

variable {n} in
theorem sc_sc (t t' : ℝ) (u : E n) : sc n t (sc n t' u) = sc n (t * t') u := by
  refine Subtype.ext (lp.ext (funext fun m => ?_))
  rw [sc_apply_coord, sc_apply_coord, sc_apply_coord]
  split_ifs <;> ring

variable {n} in
theorem sc_one (u : E n) : sc n 1 u = u := by
  rw [sc_apply, sub_self, zero_mul, zero_smul, add_zero]

variable {n} in
/-- `⟪sc t u, sc t w⟫ = ⟪u, w⟫ + (t² - 1) uₙ wₙ`. -/
theorem inner_sc (t : ℝ) (u w : E n) :
    ⟪sc n t u, sc n t w⟫_ℝ = ⟪u, w⟫_ℝ + (t ^ 2 - 1) * ((u : ℓ²(ℕ, ℝ)) n * (w : ℓ²(ℕ, ℝ)) n) := by
  have e : ∀ v : E n, ⟪((top n : E n) : ℓ²(ℕ, ℝ)), (v : ℓ²(ℕ, ℝ))⟫_ℝ = (v : ℓ²(ℕ, ℝ)) n :=
    fun v => by rw [← Submodule.coe_inner]; exact inner_top_left n v
  have e' : ∀ v : E n, ⟪(v : ℓ²(ℕ, ℝ)), ((top n : E n) : ℓ²(ℕ, ℝ))⟫_ℝ = (v : ℓ²(ℕ, ℝ)) n :=
    fun v => by rw [real_inner_comm]; exact e v
  have htt : ⟪((top n : E n) : ℓ²(ℕ, ℝ)), ((top n : E n) : ℓ²(ℕ, ℝ))⟫_ℝ = 1 := by
    rw [e]; simp [top]
  rw [Submodule.coe_inner, Submodule.coe_inner, sc_apply, sc_apply, Submodule.coe_add,
    Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, inner_add_left, inner_add_right,
    inner_add_right, real_inner_smul_left, real_inner_smul_right, real_inner_smul_left,
    real_inner_smul_right, e, e', htt]
  ring

/-- `A⁻¹` on `E` (`ClassicalRegularity.invDiag_mem_trunc`). -/
def Λ : E n →L[ℝ] E n := LinearMap.toContinuousLinearMap
  { toFun := fun u => ⟨invDiag ℝ ⟨u, trunc_le_domain _ u.2⟩, invDiag_mem_trunc _ u.2⟩
    map_add' := fun u w => Subtype.ext ((invDiag ℝ).map_add ⟨u, trunc_le_domain _ u.2⟩
      ⟨w, trunc_le_domain _ w.2⟩)
    map_smul' := fun r u => Subtype.ext ((invDiag ℝ).map_smul r ⟨u, trunc_le_domain _ u.2⟩) }

variable {n} in
theorem coe_Λ (u : E n) : (Λ n u : ℓ²(ℕ, ℝ)) = invDiag ℝ ⟨u, trunc_le_domain _ u.2⟩ := rfl

/-- The truncation `P` onto `E`, the orthogonal projection (`starProjection_trunc`). -/
abbrev P : ℓ²(ℕ, ℝ) →L[ℝ] E n := (trunc ℝ (n + 1)).orthogonalProjectionOnto

variable {n} in
theorem coe_P (x : ℓ²(ℕ, ℝ)) : (P n x : ℓ²(ℕ, ℝ)) = truncSum ℝ (n + 1) x := by
  rw [Submodule.coe_orthogonalProjectionOnto_apply, starProjection_trunc]

variable {n} in
/-- `‖sc t u‖² = ‖u‖² + (t² - 1) uₙ²`. -/
theorem norm_sc_sq (t : ℝ) (u : E n) :
    ‖sc n t u‖ ^ 2 = ‖u‖ ^ 2 + (t ^ 2 - 1) * ((u : ℓ²(ℕ, ℝ)) n * (u : ℓ²(ℕ, ℝ)) n) := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_sc]

variable {n} in
theorem abs_coord_le (u : E n) : |(u : ℓ²(ℕ, ℝ)) n| ≤ ‖u‖ := by
  rw [← Real.norm_eq_abs]
  exact lp.norm_apply_le_norm two_ne_zero (u : ℓ²(ℕ, ℝ)) n

variable {n} in
theorem norm_sc_le {t : ℝ} (ht : t ^ 2 ≤ 1) (u : E n) : ‖sc n t u‖ ≤ ‖u‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [norm_sc_sq]
  nlinarith [mul_self_nonneg ((u : ℓ²(ℕ, ℝ)) n)]

/-- The element `(u, w)` of `Xₙ`. -/
abbrev pair (u w : E n) : X n := WithLp.toLp 2 ![u, w]

/-- The reading map `iₙ (u, w) = (u + (√2 - 1) uₙ eₙ, w)`: the inclusion, with the highest mode of
degree `0` multiplied by `√2`. -/
def incl : X n →L[ℝ] T := LinearMap.toContinuousLinearMap
  { toFun := fun v => WithLp.toLp 2 ![(sc n √2 (v 0) : ℓ²(ℕ, ℝ)), (v 1 : ℓ²(ℕ, ℝ))]
    map_add' := fun v w => by ext i : 1; fin_cases i <;> simp
    map_smul' := fun r v => by ext i : 1; fin_cases i <;> simp }

theorem incl_apply_zero (v : X n) : incl n v 0 = (sc n √2 (v 0) : ℓ²(ℕ, ℝ)) := rfl

theorem incl_apply_one (v : X n) : incl n v 1 = (v 1 : ℓ²(ℕ, ℝ)) := rfl

/-- The discrete differential `𝐝ₙ (u, w) = (0, A⁻¹ (u + (√2 - 1) uₙ eₙ))`, which makes `iₙ` a
cochain map. -/
def D : X n →L[ℝ] X n := LinearMap.toContinuousLinearMap
  { toFun := fun v => pair n 0 (Λ n (sc n √2 (v 0)))
    map_add' := fun v w => by ext i : 1; fin_cases i <;> simp
    map_smul' := fun r v => by ext i : 1; fin_cases i <;> simp }

theorem D_apply_zero (v : X n) : D n v 0 = 0 := rfl

theorem D_apply_one (v : X n) : D n v 1 = Λ n (sc n √2 (v 0)) := rfl

theorem D_D (v : X n) : D n (D n v) = 0 := by
  ext i : 1
  fin_cases i
  · rfl
  · change Λ n (sc n √2 (D n v 0)) = 0
    rw [D_apply_zero, _root_.map_zero, _root_.map_zero]

/-- The cochain projections `πₙ x = (P x⁰ + (1/√2 - 1) (P x⁰)ₙ eₙ, P x¹)`, linear. -/
def projₗ : T →ₗ[ℝ] X n where
  toFun x := pair n (sc n (√2)⁻¹ (P n (x 0))) (P n (x 1))
  map_add' x y := by ext i : 1; fin_cases i <;> simp
  map_smul' r x := by ext i : 1; fin_cases i <;> simp

theorem norm_X_sq (v : X n) : ‖v‖ ^ 2 = ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]

theorem norm_T_sq (x : T) : ‖x‖ ^ 2 = ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]

theorem norm_projₗ_le (x : T) : ‖projₗ n x‖ ≤ ‖x‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [norm_X_sq, norm_T_sq]
  have h2 : (√2)⁻¹ ^ 2 ≤ 1 := by
    rw [inv_pow, Real.sq_sqrt zero_le_two]; norm_num
  have h0 : ‖sc n (√2)⁻¹ (P n (x 0))‖ ≤ ‖x 0‖ :=
    (norm_sc_le h2 _).trans (Submodule.norm_orthogonalProjectionOnto_apply_le _ _)
  have h1 : ‖P n (x 1)‖ ≤ ‖x 1‖ := Submodule.norm_orthogonalProjectionOnto_apply_le _ _
  change ‖sc n (√2)⁻¹ (P n (x 0))‖ ^ 2 + ‖P n (x 1)‖ ^ 2 ≤ _
  gcongr

/-- The cochain projections as bounded operators, `‖πₙ‖ ≤ 1`. -/
def projL : T →L[ℝ] X n := (projₗ n).mkContinuous 1 fun x => by
  rw [one_mul]; exact norm_projₗ_le n x

theorem sc_sqrt_two_inv (u : E n) : sc n √2 (sc n (√2)⁻¹ u) = u := by
  rw [sc_sc, mul_inv_cancel₀ (by positivity), sc_one]

theorem sc_inv_sqrt_two (u : E n) : sc n (√2)⁻¹ (sc n √2 u) = u := by
  rw [sc_sc, inv_mul_cancel₀ (by positivity), sc_one]

theorem projₗ_incl (v : X n) : projₗ n (incl n v) = v := by
  ext i : 1
  fin_cases i
  · change sc n (√2)⁻¹ (P n (sc n √2 (v 0) : ℓ²(ℕ, ℝ))) = v 0
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, sc_inv_sqrt_two]
  · change P n (v 1 : ℓ²(ℕ, ℝ)) = v 1
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

/-! ### The inner-product defect -/

/-- The highest mode `(eₙ, 0)` of degree `0` in `Xₙ`. -/
def topX : X n := pair n (top n) 0

theorem inner_topX (w : X n) : ⟪topX n, w⟫_ℝ = (w 0 : ℓ²(ℕ, ℝ)) n := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  change ⟪top n, w 0⟫_ℝ + ⟪(0 : E n), w 1⟫_ℝ = _
  rw [inner_top_left, inner_zero_left, add_zero]

theorem inner_smul_topX (c : ℝ) (w : X n) : ⟪c • topX n, w⟫_ℝ = c * (w 0 : ℓ²(ℕ, ℝ)) n :=
  (real_inner_smul_left _ _ _).trans (congrArg _ (inner_topX n w))

theorem coord_topX : ((topX n 0 : E n) : ℓ²(ℕ, ℝ)) n = 1 := by
  change (lp.single 2 n (1 : ℝ) : ℓ²(ℕ, ℝ)) n = 1
  exact lp.single_apply_self 2 n 1

theorem norm_topX : ‖topX n‖ = 1 := by
  have e := inner_topX n (topX n)
  rw [real_inner_self_eq_norm_sq, coord_topX] at e
  nlinarith [norm_nonneg (topX n)]

/-- `⟪iₙ v, iₙ w⟫ = ⟪v, w⟫ + v⁰ₙ w⁰ₙ`: the reading maps double the square norm of the highest mode
of degree `0`. -/
theorem inner_incl (v w : X n) :
    ⟪incl n v, incl n w⟫_ℝ = ⟪v, w⟫_ℝ + (v 0 : ℓ²(ℕ, ℝ)) n * (w 0 : ℓ²(ℕ, ℝ)) n := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, PiLp.inner_apply v w, Fin.sum_univ_two]
  change ⟪(sc n √2 (v 0) : ℓ²(ℕ, ℝ)), (sc n √2 (w 0) : ℓ²(ℕ, ℝ))⟫_ℝ +
    ⟪(v 1 : ℓ²(ℕ, ℝ)), (w 1 : ℓ²(ℕ, ℝ))⟫_ℝ = ⟪v 0, w 0⟫_ℝ + ⟪v 1, w 1⟫_ℝ + _
  rw [← Submodule.coe_inner, ← Submodule.coe_inner, inner_sc, Real.sq_sqrt zero_le_two]
  ring

/-- **`1 - iₙ* iₙ` is minus the projection on the highest mode of degree `0`**:
`(1 - iₙ* iₙ) v = -v⁰ₙ (eₙ, 0)`. -/
theorem one_sub_J_apply (v : X n) :
    (1 - (incl n).adjoint ∘L incl n) v = -((v 0 : ℓ²(ℕ, ℝ)) n) • topX n := by
  refine ext_inner_right ℝ fun w => ?_
  rw [_root_.sub_apply, one_apply_eq_self, inner_sub_left, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, inner_incl, inner_smul_topX]
  ring

theorem norm_one_sub_J_apply (v : X n) :
    ‖(1 - (incl n).adjoint ∘L incl n) v‖ = |(v 0 : ℓ²(ℕ, ℝ)) n| := by
  rw [one_sub_J_apply, norm_smul, norm_neg, norm_topX, mul_one, Real.norm_eq_abs]

theorem abs_top_le (v : X n) : |(v 0 : ℓ²(ℕ, ℝ)) n| ≤ ‖v‖ :=
  (abs_coord_le (v 0)).trans (PiLp.norm_apply_le v 0)

/-- **`‖1 - iₙ* iₙ‖ = 1`** for every `n`. -/
theorem norm_one_sub_J : ‖1 - (incl n).adjoint ∘L incl n‖ = 1 := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_) ?_
  · rw [norm_one_sub_J_apply, one_mul]; exact abs_top_le n v
  · have h := (1 - (incl n).adjoint ∘L incl n).le_opNorm (topX n)
    rwa [norm_one_sub_J_apply, norm_topX, mul_one, coord_topX, abs_one] at h

/-- `𝐝ₙ` is `(n + 1) √2` on the highest mode of degree `0`: `(n + 1) √2 |v⁰ₙ| ≤ ‖𝐝ₙ v‖`. -/
theorem mul_abs_top_le (v : X n) :
    ((n : ℝ) + 1) * √2 * |(v 0 : ℓ²(ℕ, ℝ)) n| ≤ ‖D n v‖ := by
  have h := (abs_coord_le (D n v 1)).trans (PiLp.norm_apply_le (D n v) 1)
  rw [D_apply_one, coe_Λ, invDiag_apply, sc_apply_top, abs_mul, abs_mul,
    abs_of_pos (show (0 : ℝ) < (n : ℝ) + 1 by positivity),
    abs_of_pos (show (0 : ℝ) < √2 by positivity)] at h
  linarith

/-- **The inner-product defect in the graph norm is at most `1/(n + 1)`**:
`‖(1 - iₙ* iₙ) v‖ ≤ (‖v‖ + ‖𝐝ₙ v‖) / (n + 1)`. -/
theorem norm_one_sub_J_apply_le (v : X n) :
    ‖(1 - (incl n).adjoint ∘L incl n) v‖ ≤ 1 / ((n : ℝ) + 1) * (‖v‖ + ‖D n v‖) := by
  rw [norm_one_sub_J_apply, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  have h := mul_abs_top_le n v
  have h0 := abs_nonneg ((v 0 : ℓ²(ℕ, ℝ)) n)
  have hs := Real.one_lt_sqrt_two
  nlinarith [norm_nonneg v, mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) h0)
    (sub_nonneg.2 hs.le)]

theorem norm_incl_apply_le (v : X n) : ‖incl n v‖ ≤ 2 * ‖v‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  have e := inner_incl n v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at e
  have h := abs_top_le n v
  have h2 : (v 0 : ℓ²(ℕ, ℝ)) n * (v 0 : ℓ²(ℕ, ℝ)) n ≤ ‖v‖ ^ 2 := by
    rw [← abs_mul_abs_self, pow_two]
    exact mul_self_le_mul_self (abs_nonneg _) h
  rw [e, mul_pow]
  nlinarith [norm_nonneg v]

theorem norm_incl_le : ‖incl n‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_two (norm_incl_apply_le n)

/-- **The witness family**: the modes `0, …, n` of both degrees, `Xₙ = E ⊕ E`, read by `iₙ`, with
the discrete differential `𝐝ₙ` and the left inverses `πₙ`. -/
def family : complex.CrimeFamily.{0} 0 2 ℕ where
  l := atTop
  X := X
  D := D
  D_D := D_D
  incl := incl
  proj := projL
  proj_incl := projₗ_incl
  bound := ⟨2, fun n => ⟨norm_incl_le n,
    (LinearMap.mkContinuous_norm_le _ zero_le_one _).trans one_le_two⟩⟩

theorem incl_mem (v : X n) : incl n v ∈ (complex.totalD 0 2).domain :=
  mem_totalD_domain (trunc_le_domain _ (sc n √2 (v 0)).2)

/-- **`iₙ` is a cochain map**: `𝐝 iₙ = iₙ 𝐝ₙ`. -/
theorem totalD_incl (v : X n) :
    complex.totalD 0 2 ⟨incl n v, incl_mem n v⟩ = incl n (D n v) := by
  refine PiLp.ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · rw [totalD_apply_zero]
    change 0 = (sc n √2 (D n v 0) : ℓ²(ℕ, ℝ))
    rw [D_apply_zero, _root_.map_zero, Submodule.coe_zero]
  · rw [totalD_apply_one]
    rfl

theorem isCochain : family.IsCochain := ⟨fun n v => incl_mem n v, fun n v => totalD_incl n v⟩

/-- `‖v‖ ≤ ‖iₙ v‖` (`HighMode.inner_incl`). -/
theorem norm_le_norm_incl (v : X n) : ‖v‖ ≤ ‖incl n v‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  have e := inner_incl n v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at e
  rw [e]
  nlinarith [mul_self_nonneg ((v 0 : ℓ²(ℕ, ℝ)) n)]

/-- **The differential of the window is unbounded**: at `x = iₙ (eₙ, 0)`, `‖x‖ ≤ 2` while
`‖𝐝 x‖ = ‖iₙ 𝐝ₙ (eₙ, 0)‖ ≥ (n + 1) √2` (`HighMode.mul_abs_top_le`). -/
theorem not_bounded_totalD : ¬ ∃ C, ∀ x : (complex.totalD 0 2).domain,
    ‖complex.totalD 0 2 x‖ ≤ C * ‖(x : T)‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * C)
  have h := hC ⟨incl n (topX n), incl_mem n (topX n)⟩
  rw [totalD_incl] at h
  change ‖incl n (D n (topX n))‖ ≤ C * ‖incl n (topX n)‖ at h
  have h1 : (n : ℝ) + 1 ≤ ‖D n (topX n)‖ := by
    have := mul_abs_top_le n (topX n)
    rw [coord_topX, abs_one, mul_one] at this
    nlinarith [Real.one_lt_sqrt_two, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h2 := (h1.trans (norm_le_norm_incl n (D n (topX n)))).trans h
  have h3 : ‖incl n (topX n)‖ ≤ 2 := by
    simpa [norm_topX] using norm_incl_apply_le n (topX n)
  have h4 := norm_nonneg (incl n (topX n))
  have h5 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases le_or_gt 0 C with hC0 | hC0
  · nlinarith [mul_le_mul_of_nonneg_left h3 hC0]
  · nlinarith [mul_le_mul_of_nonneg_right hC0.le h4]

/-- The truncation commutes with `A⁻¹`: `P A⁻¹ u = A⁻¹ P u` (`truncSum_invDiag`). -/
theorem P_invDiag (u : (invDiag ℝ).domain) : P n (invDiag ℝ u) = Λ n (P n u) := by
  refine Subtype.ext ?_
  rw [coe_P, truncSum_invDiag, coe_Λ]
  exact LinearPMap.apply_congr' _ _ _ (coe_P _).symm

/-- **`πₙ` commutes with the differentials**: `πₙ 𝐝 = 𝐝ₙ πₙ` on `D(𝐝)`. -/
theorem projₗ_totalD (z : (complex.totalD 0 2).domain) :
    projₗ n (complex.totalD 0 2 z) = D n (projₗ n z) := by
  refine PiLp.ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · change sc n (√2)⁻¹ (P n ((complex.totalD 0 2 z : T) 0)) = D n (projₗ n z) 0
    rw [totalD_apply_zero, _root_.map_zero, _root_.map_zero, D_apply_zero]
  · change P n ((complex.totalD 0 2 z : T) 1) = Λ n (sc n √2 (sc n (√2)⁻¹ (P n ((z : T) 0))))
    rw [totalD_apply_one, sc_sqrt_two_inv, P_invDiag]
    rfl

/-- **The cochain projections** `πₙ`, bounded by `1` in the graph norm. -/
def proj : family.CochainProj 1 where
  π := projₗ
  π_incl := projₗ_incl
  norm_π_le n x := by
    have h1 := norm_projₗ_le n (x : T)
    have h2 := norm_nonneg (complex.totalD 0 2 x)
    change ‖projₗ n (x : T)‖ ≤ 1 * (‖(x : T)‖ + ‖complex.totalD 0 2 x‖)
    linarith
  π_totalD n z := projₗ_totalD n z

theorem tendsto_sub_truncSum (y : ℓ²(ℕ, ℝ)) :
    Tendsto (fun n => ‖y - truncSum ℝ (n + 1) y‖) atTop (𝓝 0) := by
  have h := (tendsto_truncSum (𝕜 := ℝ) y).comp (tendsto_add_atTop_nat 1)
  simpa [Function.comp_def, norm_sub_rev] using tendsto_iff_norm_sub_tendsto_zero.1 h

/-- **`iₙ πₙ → 1`**: `iₙ πₙ` is the truncation to the modes `0, …, n` of both degrees. -/
theorem tendsto_incl_proj (x : T) :
    Tendsto (fun n => ‖x - incl n (projₗ n x)‖) atTop (𝓝 0) := by
  refine squeeze_zero (fun _ => norm_nonneg _)
    (fun n => ((PiLp.norm_le_sum_norm _).trans_eq (Fin.sum_univ_two _)).trans (le_of_eq ?_))
    (by simpa using (tendsto_sub_truncSum (x 0)).add (tendsto_sub_truncSum (x 1)))
  change ‖x 0 - (sc n √2 (sc n (√2)⁻¹ (P n (x 0))) : ℓ²(ℕ, ℝ))‖ +
    ‖x 1 - (P n (x 1) : ℓ²(ℕ, ℝ))‖ = _
  rw [sc_sqrt_two_inv, coe_P, coe_P]

end FEEC.HighMode
