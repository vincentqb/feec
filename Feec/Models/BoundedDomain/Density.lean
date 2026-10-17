module

public import Feec.Models.BoundedDomain.GradCurl
public import Feec.Domain.Mollify

/-!
# The closure of `L²(TSD) ∩ H̊(curl)`: the normal-trace obstruction (thesis Prop 4.17)

On a bounded open `Ω ⊆ ℝ³` let `Z = L²(TSD) ∩ H̊(curl, M)`.

* **Generalized zero mean** (`sum_integral_mul_pd_eq_zero`): every `B ∈ Z` satisfies
  `Σ_{jk} ∫_Ω B_{jk} ∂_k φ_j = 0` for every `C¹` field `φ` on `ℝ³` (no boundary condition),
  i.e. `B n = 0` weakly on `∂Ω`; so `cl Z ⊆ L²(TSD₀)` (`tsd₀`, `closure_le_tsd₀`).
* **Density** (`tsd₀_le_closure`): on a domain star-shaped with respect to a ball, every
  `B ∈ L²(TSD₀)` is an `L²` limit of smooth compactly supported fields that are pointwise
  symmetric, trace-free and divergence-free; an instance of the constrained density theorem
  `Feec.Domain.exists_isTestField_ker_dist_lt` for the row-homogeneous TSD operator `tsdOp`.
* Hence `cl Z = L²(TSD₀)` (`closure_eq_tsd₀`) and the obstruction of `L²(TSD)` for `H̊(curl)`
  is `L²(TSD) ⊓ L²(TSD₀)ᗮ` (`obstruction_eq`).

## References

* [QuennevilleBelair2015], §4.10 (Prop 4.17, the density gap)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ContDiff Matrix ComplexConjugate LinearPMap
open MeasureTheory Set Filter Topology Feec.Domain

namespace Feec.Models.BoundedDomain

variable {Ω : Set R3}

/-! ## Generalized zero mean -/

/-- **`B n = 0` weakly on `∂Ω`** for `B ∈ L²(TSD) ∩ H̊(curl)` (`Ω` bounded open): for every
`C¹` field `φ` on `ℝ³`, `Σ_{jk} ∫_Ω B_{jk} ∂_k φ_j = 0`. Thesis: Prop 4.17 -/
theorem sum_integral_mul_pd_eq_zero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (B : ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain) (hB : (B : L2F ℝ Ω Ix) ∈ tsd Ω)
    {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, ContDiff ℝ 1 (φ i)) :
    ∑ jk : Ix, ∫ x, (B : L2F ℝ Ω Ix) jk x * pd jk.2 (φ jk.1) x ∂volume.restrict Ω = 0 := by
  have hCs := curl_symm_of_mem_tsd hΩ B hB
  have e := minimal_curl_identity hΩ hb B (Ψ := skewOf φ) (contDiff_skewOf hφ)
  rw [sum_integral_mul_skewOf_eq_zero hCs] at e
  simp only [curlM_skewOf (fun i => (hφ i).differentiable one_ne_zero), mul_sub] at e
  set d : R3 → ℝ := fun x => ∑ m, pd m (φ m) x
  have hdm : MemLp d 2 (volume.restrict Ω) :=
    memLp_of_continuous hΩ.measurableSet hb (continuous_finsetSum _ fun m _ =>
      continuous_pd (hφ m) m)
  have hpm : ∀ jk : Ix, MemLp (pd jk.1 (φ jk.2)) 2 (volume.restrict Ω) := fun jk =>
    memLp_of_continuous hΩ.measurableSet hb (continuous_pd (hφ _) _)
  rw [Finset.sum_congr rfl fun jk _ => integral_sub ?_ ?_] at e
  rotate_left
  · exact integrable_mul _ (by split_ifs; exacts [hdm, MemLp.zero])
  · exact integrable_mul _ (hpm jk)
  rw [Finset.sum_sub_distrib] at e
  have h1 : ∑ jk : Ix, ∫ x, (B : L2F ℝ Ω Ix) jk x * (if jk.1 = jk.2 then d x else 0)
      ∂volume.restrict Ω = 0 := by
    simp only [mul_ite, mul_zero, integral_ite_zero, Fintype.sum_prod_type, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    simp only [fun f : L2 ℝ Ω => integral_mul_eq_inner f hdm, ← sum_inner, hB.2.1,
      inner_zero_left]
  rw [h1, zero_sub] at e
  rw [← neg_eq_zero.1 e.symm]
  refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun jk => ?_
  obtain ⟨j, k⟩ := jk
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
  rw [hB.1 j k]

/-! ## The space `L²(TSD₀)` -/

/-- The gradient `∇φ` of a `C¹` field on `ℝ³`, as an element of `L²(Ω; ℝ³ˣ³)` (`Ω` bounded). -/
def gradL2 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {φ : Fin 3 → R3 → ℝ}
    (hφ : ∀ i, ContDiff ℝ 1 (φ i)) : L2F ℝ Ω Ix :=
  toL2F fun jk : Ix => memLp_of_continuous hΩ.measurableSet hb (continuous_pd (hφ jk.1) jk.2)

theorem inner_gradL2 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {φ : Fin 3 → R3 → ℝ}
    (hφ : ∀ i, ContDiff ℝ 1 (φ i)) (B : L2F ℝ Ω Ix) :
    ⟪B, gradL2 hΩ hb hφ⟫_ℝ = ∑ jk : Ix, ∫ x, B jk x * pd jk.2 (φ jk.1) x ∂volume.restrict Ω :=
  inner_toL2F_eq B _

variable (Ω) in
/-- `L²(TSD₀)`: TSD fields orthogonal to every gradient `∇φ`, `φ ∈ C¹(ℝ³; ℝ³)` (weakly
`B n = 0` on `∂Ω`). Thesis: Prop 4.17 -/
def tsd₀ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : Submodule ℝ (L2F ℝ Ω Ix) :=
  tsd Ω ⊓ ⨅ (φ : Fin 3 → R3 → ℝ) (hφ : ∀ i, ContDiff ℝ 1 (φ i)), (ℝ ∙ gradL2 hΩ hb hφ)ᗮ

theorem mem_tsd₀ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {B : L2F ℝ Ω Ix} :
    B ∈ tsd₀ Ω hΩ hb ↔ B ∈ tsd Ω ∧ ∀ φ : Fin 3 → R3 → ℝ, (∀ i, ContDiff ℝ 1 (φ i)) →
      ∑ jk : Ix, ∫ x, B jk x * pd jk.2 (φ jk.1) x ∂volume.restrict Ω = 0 := by
  simp only [tsd₀, Submodule.mem_inf, Submodule.mem_iInf,
    Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm, inner_gradL2]

theorem isClosed_tsd₀ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    IsClosed (tsd₀ Ω hΩ hb : Set (L2F ℝ Ω Ix)) := by
  rw [tsd₀, Submodule.coe_inf, Submodule.coe_iInf]
  refine isClosed_tsd.inter (isClosed_iInter fun φ => ?_)
  rw [Submodule.coe_iInf]
  exact isClosed_iInter fun hφ => Submodule.isClosed_orthogonal _

/-- `L²(TSD) ∩ H̊(curl) ⊆ L²(TSD₀)`. -/
theorem inf_le_tsd₀ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    tsd Ω ⊓ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain ≤ tsd₀ Ω hΩ hb :=
  fun B hB => (mem_tsd₀ hΩ hb).2 ⟨hB.1, fun _ hφ =>
    sum_integral_mul_pd_eq_zero hΩ hb ⟨B, hB.2⟩ hB.1 hφ⟩

/-- `cl (L²(TSD) ∩ H̊(curl)) ⊆ L²(TSD₀)`. -/
theorem closure_le_tsd₀ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (tsd Ω ⊓ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain).topologicalClosure ≤
      tsd₀ Ω hΩ hb :=
  Submodule.topologicalClosure_minimal _ (inf_le_tsd₀ hΩ hb) (isClosed_tsd₀ hΩ hb)


/-! ## The TSD constraint operator -/

/-- The row index of the TSD constraints: symmetry rows `(a, b)`, the trace, divergence rows. -/
abbrev TsdRow := Ix ⊕ (Unit ⊕ Fin 3)

/-- The TSD constraint operator: `B_{ab} - B_{ba}`, `tr B` (order `0`) and `(div B)ᵢ` (order `1`). -/
def tsdOp : ConstCoeffOp R3 ℝ Ix TsdRow where
  coeff r ij := match r with
    | Sum.inl ab => (if ij = ab then [([], 1)] else []) ++
        (if ij = (ab.2, ab.1) then [([], -1)] else [])
    | Sum.inr (Sum.inl _) => if ij.1 = ij.2 then [([], 1)] else []
    | Sum.inr (Sum.inr i) => if ij.1 = i then [([coordDir ij.2], 1)] else []

/-- The orders of the rows of `tsdOp`. -/
def tsdOrder : TsdRow → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr _) => 1

theorem tsdOp_isRowHomogeneous : tsdOp.IsRowHomogeneous tsdOrder := by
  rintro (ab | _ | i) ij t ht
  · simp only [tsdOp, List.mem_append] at ht
    rcases ht with ht | ht <;> split_ifs at ht <;> simp_all [tsdOrder]
  · simp only [tsdOp] at ht
    split_ifs at ht <;> simp_all [tsdOrder]
  · simp only [tsdOp] at ht
    split_ifs at ht <;> simp_all [tsdOrder]

theorem tsdOp_apply_sym (φ : Ix → R3 → ℝ) (ab : Ix) (x : R3) :
    tsdOp.apply φ (Sum.inl ab) x = φ ab x - φ (ab.2, ab.1) x := by
  simp [ConstCoeffOp.apply, tsdOp, ConstCoeffOp.applyEntry_append, ConstCoeffOp.applyEntry_ite, Finset.sum_add_distrib]
  ring

theorem tsdOp_apply_tr (φ : Ix → R3 → ℝ) (u : Unit) (x : R3) :
    tsdOp.apply φ (Sum.inr (Sum.inl u)) x = ∑ i, φ (i, i) x := by
  simp only [ConstCoeffOp.apply, tsdOp, ConstCoeffOp.applyEntry_ite, ConstCoeffOp.applyEntry_singleton, ConstCoeffOp.applyEntry_nil',
    iterDeriv_nil, one_mul]
  rw [Fintype.sum_prod_type]
  simp

theorem tsdOp_apply_div (φ : Ix → R3 → ℝ) (i : Fin 3) (x : R3) :
    tsdOp.apply φ (Sum.inr (Sum.inr i)) x = ∑ j, pd j (φ (i, j)) x := by
  simp only [ConstCoeffOp.apply, tsdOp, ConstCoeffOp.applyEntry_ite, ConstCoeffOp.applyEntry_singleton, ConstCoeffOp.applyEntry_nil',
    iterDeriv_singleton, one_mul]
  rw [Fintype.sum_prod_type]
  simp [pd]


theorem tsdOp_formalAdj_apply (ψ : TsdRow → R3 → ℝ) (ij : Ix) (x : R3) :
    tsdOp.formalAdj.apply ψ ij x = ψ (Sum.inl ij) x - ψ (Sum.inl (ij.2, ij.1)) x +
      (if ij.1 = ij.2 then ψ (Sum.inr (Sum.inl ())) x else 0) -
        pd ij.2 (ψ (Sum.inr (Sum.inr ij.1))) x := by
  have hswap : ∀ ab : Ix, (ij = (ab.2, ab.1)) ↔ (ab = (ij.2, ij.1)) := fun ab => by
    obtain ⟨a, b⟩ := ab; obtain ⟨i, j⟩ := ij
    simp only [Prod.mk.injEq]; tauto
  simp only [ConstCoeffOp.apply, ConstCoeffOp.formalAdj, tsdOp, Fintype.sum_sum_type,
    ConstCoeffOp.adjEntry, List.map_append, ConstCoeffOp.applyEntry_append,
    apply_ite (List.map _), List.map_cons, List.map_nil, ConstCoeffOp.applyEntry_ite,
    ConstCoeffOp.applyEntry_singleton, ConstCoeffOp.applyEntry_nil', Finset.sum_add_distrib,
    hswap, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.univ_unique,
    Finset.sum_singleton, List.reverse_nil, List.length_nil, List.reverse_singleton,
    List.length_singleton, iterDeriv_nil, iterDeriv_singleton]
  simp [pd]
  ring


/-! ## Density of smooth TSD fields in `L²(TSD₀)` -/

theorem integral_indicator_mul (hΩ : IsOpen Ω) (f g : R3 → ℝ) :
    ∫ x, Ω.indicator f x * g x = ∫ x, f x * g x ∂volume.restrict Ω := by
  rw [← integral_indicator hΩ.measurableSet]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Ω <;> simp [hx]

/-- The zero extension of a field of `L²(TSD₀)` satisfies the TSD constraints in `𝒟'(ℝ³)`. -/
theorem tsdOp_weak_of_mem_tsd₀ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {B : L2F ℝ Ω Ix}
    (hB : B ∈ tsd₀ Ω hΩ hb) (ψ : TsdRow → R3 → ℝ) (hψ : IsTestField (univ : Set R3) ψ) :
    ∑ ij, ∫ x, Ω.indicator (B ij : R3 → ℝ) x * tsdOp.formalAdj.apply ψ ij x = 0 := by
  obtain ⟨hBt, hB0⟩ := (mem_tsd₀ hΩ hb).1 hB
  have hli : ∀ ij, LocallyIntegrable (Ω.indicator (B ij : R3 → ℝ)) volume := fun ij =>
    ((memLp_indicator_iff_restrict hΩ.measurableSet.nullMeasurableSet).2
      (Lp.memLp (B ij))).locallyIntegrable (by norm_num)
  set u : Ix → R3 → ℝ := fun ij => Ω.indicator (B ij : R3 → ℝ) with hu
  have hψtr : IsTest (univ : Set R3) (ψ (Sum.inr (Sum.inl ()))) := hψ _
  have hψd : ∀ ij : Ix, IsTest (univ : Set R3) (fun x => pd ij.2 (ψ (Sum.inr (Sum.inr ij.1))) x) :=
    fun ij => (hψ _).fderiv_apply _
  have I : ∀ ij {g : R3 → ℝ}, IsTest (univ : Set R3) g → Integrable fun x => u ij x * g x :=
    fun ij g hg => integrable_mul_isTest (hli ij) hg
  have hite : ∀ ij : Ix, IsTest (univ : Set R3)
      (fun x => if ij.1 = ij.2 then ψ (Sum.inr (Sum.inl ())) x else 0) := fun ij => by
    split_ifs
    · exact hψtr
    · exact IsTest.zero
  have e : ∀ ij, ∫ x, u ij x * tsdOp.formalAdj.apply ψ ij x =
      (∫ x, u ij x * ψ (Sum.inl ij) x) - (∫ x, u ij x * ψ (Sum.inl (ij.2, ij.1)) x) +
        (∫ x, u ij x * (if ij.1 = ij.2 then ψ (Sum.inr (Sum.inl ())) x else 0)) -
          (∫ x, u ij x * pd ij.2 (ψ (Sum.inr (Sum.inr ij.1))) x) := by
    intro ij
    have i1 := I ij (hψ (Sum.inl ij))
    have i2 := I ij (hψ (Sum.inl (ij.2, ij.1)))
    have i3 := I ij (hite ij)
    have i4 := I ij (hψd ij)
    have j12 : Integrable fun x => u ij x * ψ (Sum.inl ij) x -
        u ij x * ψ (Sum.inl (ij.2, ij.1)) x := i1.sub i2
    have j123 : Integrable fun x => u ij x * ψ (Sum.inl ij) x -
        u ij x * ψ (Sum.inl (ij.2, ij.1)) x +
          u ij x * (if ij.1 = ij.2 then ψ (Sum.inr (Sum.inl ())) x else 0) := j12.add i3
    have hpt : (fun x => u ij x * tsdOp.formalAdj.apply ψ ij x) = fun x =>
        u ij x * ψ (Sum.inl ij) x - u ij x * ψ (Sum.inl (ij.2, ij.1)) x +
          u ij x * (if ij.1 = ij.2 then ψ (Sum.inr (Sum.inl ())) x else 0) -
            u ij x * pd ij.2 (ψ (Sum.inr (Sum.inr ij.1))) x := by
      funext x; rw [tsdOp_formalAdj_apply]; ring
    rw [hpt, integral_sub j123 i4, integral_add j12 i3, integral_sub i1 i2]
  show ∑ ij, ∫ x, u ij x * tsdOp.formalAdj.apply ψ ij x = 0
  simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  -- the symmetry rows
  have h12 : ∑ ij : Ix, ∫ x, u ij x * ψ (Sum.inl (ij.2, ij.1)) x =
      ∑ ij : Ix, ∫ x, u ij x * ψ (Sum.inl ij) x := by
    refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun ij => ?_
    obtain ⟨i, j⟩ := ij
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk, hu]
    rw [hBt.1 i j]
  -- the trace row
  have h3 : ∑ ij : Ix, ∫ x, u ij x * (if ij.1 = ij.2 then ψ (Sum.inr (Sum.inl ())) x else 0) = 0 := by
    have e3 : ∀ ij : Ix, ∫ x, u ij x * (if ij.1 = ij.2 then ψ (Sum.inr (Sum.inl ())) x else 0) =
        if ij.1 = ij.2 then ∫ x, u ij x * ψ (Sum.inr (Sum.inl ())) x else 0 := fun ij => by
      split_ifs <;> simp
    simp only [e3, Fintype.sum_prod_type, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have htr := hBt.2.1
    have h1 := Lp.coeFn_fun_finsetSum (μ := volume.restrict Ω) Finset.univ (fun i => B (i, i))
    rw [htr] at h1
    have h2 : (fun x => ∑ i, (B (i, i) : R3 → ℝ) x) =ᵐ[volume.restrict Ω] 0 := by
      filter_upwards [h1, Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x hx h0
      rw [← hx, h0]
    have h2' : ∀ᵐ x ∂volume, x ∈ Ω → ∑ i, (B (i, i) : R3 → ℝ) x = 0 :=
      (ae_restrict_iff' hΩ.measurableSet).1 h2
    rw [← integral_finsetSum _ fun i _ => I (i, i) hψtr]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [h2'] with x hx
    rw [← Finset.sum_mul]
    have : ∑ i, u (i, i) x = 0 := by
      by_cases hxΩ : x ∈ Ω
      · simp only [hu, indicator_of_mem hxΩ]; exact hx hxΩ
      · simp [hu, indicator_of_notMem hxΩ]
    rw [this, zero_mul]; rfl
  -- the divergence rows
  have h4 : ∑ ij : Ix, ∫ x, u ij x * pd ij.2 (ψ (Sum.inr (Sum.inr ij.1))) x = 0 := by
    simp only [hu, integral_indicator_mul hΩ]
    exact hB0 (fun i => ψ (Sum.inr (Sum.inr i))) fun i => (hψ _).contDiff.of_le (by simp)
  rw [h12, h3, h4]
  ring


/-- Test fields in the kernel of `tsdOp` lie in `L²(TSD) ∩ H̊(curl)`. -/
theorem testField_mem_of_tsdOp_eq_zero (hΩ : IsOpen Ω) {φ : Ix → R3 → ℝ} (hφ : IsTestField Ω φ)
    (hA : tsdOp.apply φ = 0) :
    testField hφ ∈ tsd Ω ⊓ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain := by
  have hsym : ∀ a b, φ (a, b) = φ (b, a) := fun a b => funext fun x => by
    have := congrFun (congrFun hA (Sum.inl (a, b))) x
    rw [tsdOp_apply_sym] at this
    simpa [sub_eq_zero] using this
  have htr : ∀ x, ∑ i, φ (i, i) x = 0 := fun x => by
    have := congrFun (congrFun hA (Sum.inr (Sum.inl ()))) x
    rwa [tsdOp_apply_tr] at this
  have hdiv : ∀ i x, ∑ j, pd j (φ (i, j)) x = 0 := fun i x => by
    have := congrFun (congrFun hA (Sum.inr (Sum.inr i))) x
    rwa [tsdOp_apply_div] at this
  refine ⟨⟨fun a b => ?_, ?_, fun ψ hψ => ?_⟩,
    (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).testField_mem_minimal_domain hΩ hφ⟩
  · simp only [testField_apply]
    exact toL2_congr _ _ (hsym a b)
  · refine Lp.ext ?_
    filter_upwards [Lp.coeFn_fun_finsetSum (μ := volume.restrict Ω) Finset.univ
        (fun i => testField hφ (i, i)), Lp.coeFn_zero ℝ 2 (volume.restrict Ω),
      ae_all_iff.2 fun i => coeFn_testField hφ (i, i)] with x h1 h0 h2
    rw [h1, h0]
    simp only [Pi.zero_apply]
    rw [Finset.sum_congr rfl fun i _ => h2 i]
    exact htr x
  · rw [inner_grad_testField _ hψ]
    have e : ∀ ij : Ix, ∫ x, testField hφ ij x * pd ij.2 (ψ ij.1) x ∂volume.restrict Ω =
        -∫ x, pd ij.2 (φ ij) x * ψ ij.1 x ∂volume.restrict Ω := fun ij => by
      rw [integral_pd_mul (hφ ij) ((hψ ij.1).contDiff.of_le (by simp)) ij.2, neg_neg]
      exact integral_congr_ae ((coeFn_testField hφ ij).mono fun x hx => by simp only; rw [hx])
    simp only [e, Finset.sum_neg_distrib, neg_eq_zero, Fintype.sum_prod_type]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← integral_finsetSum _ fun j _ => ?_]
    · refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
      simp only [← Finset.sum_mul, hdiv i x, zero_mul, Pi.zero_apply]
    · exact (((hφ (i, j)).fderiv_apply _).continuous.mul (hψ i).continuous).integrable_of_hasCompactSupport
        ((hφ (i, j)).fderiv_apply _).hasCompactSupport.mul_right |>.restrict

/-- **Density of smooth TSD fields in `L²(TSD₀)`** on a bounded open `Ω` star-shaped with respect
to a ball. Thesis: Prop 4.17 -/
theorem tsd₀_le_closure (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {x₀ : R3} {s : ℝ}
    (hs : 0 < s) (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) :
    tsd₀ Ω hΩ hb ≤
      (tsd Ω ⊓ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain).topologicalClosure := by
  intro B hB
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨φ, hφ, hAφ, hd⟩ := exists_isTestField_ker_dist_lt hΩ hb hs hstar tsdOp
    tsdOp_isRowHomogeneous B (tsdOp_weak_of_mem_tsd₀ hΩ hb hB) hε
  exact ⟨testField hφ, testField_mem_of_tsdOp_eq_zero hΩ hφ hAφ, hd⟩

/-- **`cl (L²(TSD) ∩ H̊(curl)) = L²(TSD₀)`** on a bounded open `Ω` star-shaped with respect to a
ball: the density inferred in the proof of thesis Prop 4.17 fails exactly by `L²(TSD₀)`.
Thesis: Prop 4.17 -/
theorem closure_eq_tsd₀ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {x₀ : R3} {s : ℝ}
    (hs : 0 < s) (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) :
    (tsd Ω ⊓ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain).topologicalClosure =
      tsd₀ Ω hΩ hb :=
  le_antisymm (closure_le_tsd₀ hΩ hb) (tsd₀_le_closure hΩ hb hs hstar)

/-- **The obstruction is exactly `L²(TSD) ⊓ L²(TSD₀)ᗮ`** (star-shaped bounded `Ω`). -/
theorem obstruction_eq_tsd₀ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {x₀ : R3} {s : ℝ}
    (hs : 0 < s) (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) :
    obstruction ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain (tsd Ω) =
      tsd Ω ⊓ (tsd₀ Ω hΩ hb)ᗮ := by
  rw [obstruction_eq, closure_eq_tsd₀ hΩ hb hs hstar]

end Feec.Models.BoundedDomain
