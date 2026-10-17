module

public import Feec.Models.BoundedDomain.GradCurl
public import Feec.Domain.Mollify
public import Mathlib.LinearAlgebra.Eigenspace.Basic

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
* **The obstruction is large**: Hessians of harmonic functions lie in it
  (`hessL2_mem_obstruction`); it is infinite-dimensional (`not_finiteDimensional_obstruction`) and
  no finite-dimensional correction restores density
  (`not_tsd_le_closure_sup_finiteDimensional`).
* **Without the boundary condition density holds**: `cl (L²(TSD) ∩ H(curl)) = L²(TSD)` on
  star-shaped domains (`closure_tsd_inf_curl_maximal`), by the expansion form of the constrained
  density theorem, `Feec.Domain.exists_contDiff_ker_on_dist_lt`.
* **The `Ė(0)` argument** (`adjoint_mem_tsd₀_of_propagates`): if a strong solution from
  `(0, E₀, B₀)` keeps `E` in `L²(TSD)`, then `d₁† B₀ ∈ L²(TSD₀)`.
* **The largest propagating constraint space** `K*` (`Feec.ShortHilbertComplex.coreSub`):
  `S₁* ⊆ L²(TSD₀)` (`invariantCore₁_le_tsd₀`), curl-free fields of `S₂` are stationary data in
  `S₂*` (`mem_invariantCore₂_of_curl_eq_zero`, `hessL2_mem_invariantCore₂`), and `S₂*` is
  infinite-dimensional (`not_finiteDimensional_invariantCore₂`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (Prop 4.17, the density gap)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ContDiff Matrix ComplexConjugate LinearPMap
open MeasureTheory Set Filter Topology Feec.Domain

namespace Feec.Models.BoundedDomain

variable {Ω : Set R3}

/-! ## Generalized zero mean -/

/-- **`B n = 0` weakly on `∂Ω`** for `B ∈ L²(TSD) ∩ H̊(curl)` (`Ω` bounded open): for every
`C¹` field `φ` on `ℝ³`, `Σ_{jk} ∫_Ω B_{jk} ∂_k φ_j = 0`. [QuennevilleBelair2015], Prop 4.17 -/
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
`B n = 0` on `∂Ω`). [QuennevilleBelair2015], Prop 4.17 -/
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

instance (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (tsd₀ Ω hΩ hb).HasOrthogonalProjection := by
  have : CompleteSpace (tsd₀ Ω hΩ hb) := (isClosed_tsd₀ hΩ hb).completeSpace_coe
  infer_instance

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
to a ball. [QuennevilleBelair2015], Prop 4.17 -/
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
[QuennevilleBelair2015], Prop 4.17 -/
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

/-! ## `L²(TSD₀)`: gradients, zero mean, the `Ė(0)` argument -/

/-- Gradients of `C¹` fields are orthogonal to `L²(TSD₀)`. -/
theorem gradL2_mem_orthogonal_tsd₀ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {φ : Fin 3 → R3 → ℝ} (hφ : ∀ i, ContDiff ℝ 1 (φ i)) :
    gradL2 hΩ hb hφ ∈ (tsd₀ Ω hΩ hb)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro B hB
  rw [real_inner_comm, inner_gradL2]
  exact ((mem_tsd₀ hΩ hb).1 hB).2 φ hφ

/-- Fields of `L²(TSD₀)` have zero mean (test against the linear fields `φ = x_b e_a`). -/
theorem integral_eq_zero_of_mem_tsd₀ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {B : L2F ℝ Ω Ix} (hB : B ∈ tsd₀ Ω hΩ hb) (a b : Fin 3) :
    ∫ x, B (a, b) x ∂volume.restrict Ω = 0 := by
  set φ : Fin 3 → R3 → ℝ := fun i => if i = a then (fun y : R3 => y b) else 0 with hφd
  have hφ : ∀ i, ContDiff ℝ 1 (φ i) := fun i => by
    simp only [hφd]
    split_ifs
    exacts [contDiff_apply ℝ (fun _ : Fin 3 => ℝ) b, contDiff_const]
  have hpd : ∀ k i x, pd k (φ i) x = if i = a ∧ k = b then 1 else 0 := by
    intro k i x
    by_cases hi : i = a
    · simp [hφd, hi, pd_coord]
    · simp only [hφd, hi, ite_false, false_and]
      simp [pd]
  have e := ((mem_tsd₀ hΩ hb).1 hB).2 φ hφ
  simp only [hpd, mul_ite, mul_one, mul_zero] at e
  rw [Finset.sum_eq_single (a, b) (fun jk _ hjk => by
    have : ¬(jk.1 = a ∧ jk.2 = b) := fun h => hjk (Prod.ext h.1 h.2)
    simp [this]) (by simp)] at e
  simpa using e

/-- `L²(TSD) ⊓ L²(TSD₀)ᗮ` lies in the obstruction of `L²(TSD)` for `H̊(curl)` (equality on
star-shaped domains, `obstruction_eq_tsd₀`). -/
theorem inf_orthogonal_tsd₀_le_obstruction (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    tsd Ω ⊓ (tsd₀ Ω hΩ hb)ᗮ ≤
      obstruction ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain (tsd Ω) :=
  inf_le_inf_left _ (Submodule.orthogonal_le (inf_le_tsd₀ hΩ hb))

section Propagation

-- Over `ℝ` the generic real structure on the window spaces duplicates the inner-product one.
attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-- **Necessary condition for TSD propagation** (the thesis' `Ė(0)` argument, any datum): for
every short complex with `d₁ ⊆ curl_min`, if a strong solution of `U' = L U` from
`(0, E₀, B₀)` keeps its electric field in `L²(TSD)` on `[0, T]`, `T > 0`, then
`d₁† B₀ ∈ L²(TSD₀)` (weakly `(d₁† B₀) n = 0` on `∂Ω`). -/
theorem adjoint_mem_tsd₀_of_propagates (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {W₀ : Type} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] [CompleteSpace W₀]
    (S : ShortHilbertComplex ℝ W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))
    (hd₁ : S.d₁ ≤ (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω) {T : ℝ} (hT : 0 < T)
    {U : ℝ → PiLp 2 (ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))}
    (hU : Evolution.IsStrongSolution S.wave (Icc 0 T) 0 U)
    (h0 : ((U 0 : PiLp 2 (ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))) 0 : W₀) = 0)
    (hK : ∀ t ∈ Icc 0 T,
      ((U t : PiLp 2 (ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))) 1 : L2F ℝ Ω Ix) ∈
        tsd Ω) :
    ∃ hB : ((U 0 : PiLp 2 (ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))) 2 :
        L2F ℝ Ω Ix) ∈ S.d₁†.domain, S.d₁† ⟨_, hB⟩ ∈ tsd₀ Ω hΩ hb := by
  obtain ⟨hB, hm⟩ := S.adjoint_mem_closure_of_propagates hT hU h0 hK
  refine ⟨hB, closure_le_tsd₀ hΩ hb ?_⟩
  exact Submodule.topologicalClosure_mono (inf_le_inf_left _ hd₁.1) hm

end Propagation

/-! ## Hessians of harmonic functions lie in the obstruction -/

/-- The Hessian `(∇²h)_{ij} = ∂_j ∂_i h`. -/
def hessField (h : R3 → ℝ) : Ix → R3 → ℝ := fun ij => pd ij.2 (pd ij.1 h)

/-- The Laplacian `Δh = Σᵢ ∂ᵢ ∂ᵢ h`. -/
def lap (h : R3 → ℝ) (x : R3) : ℝ := ∑ i, pd i (pd i h) x

theorem hessField_eq_gradM (h : R3 → ℝ) : hessField h = gradM fun i => pd i h := rfl

theorem contDiff_hessField {h : R3 → ℝ} (hh : ContDiff ℝ ∞ h) (ij : Ix) :
    ContDiff ℝ ∞ (hessField h ij) :=
  contDiff_pd_top (contDiff_pd_top hh _) _

/-- The `L²(Ω)` class of the Hessian of a smooth function. -/
def hessL2 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {h : R3 → ℝ} (hh : ContDiff ℝ ∞ h) :
    L2F ℝ Ω Ix :=
  smoothField hΩ hb (hessField h) fun ij => (contDiff_hessField hh ij).continuous

theorem hessL2_eq_gradL2 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {h : R3 → ℝ}
    (hh : ContDiff ℝ ∞ h) :
    hessL2 hΩ hb hh = gradL2 hΩ hb (φ := fun i => pd i h)
      (fun i => (contDiff_pd_top hh i).of_le (by simp)) := rfl

/-- **Hessians of functions harmonic on `Ω` lie in `L²(TSD)`**: `∇²h` is symmetric (Schwarz),
trace-free (`Δh = 0`) and divergence-free (`div ∇²h = ∇Δh = 0`) on `Ω`. -/
theorem hessL2_mem_tsd (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {h : R3 → ℝ}
    (hh : ContDiff ℝ ∞ h) (hΔ : ∀ x ∈ Ω, lap h x = 0) : hessL2 hΩ hb hh ∈ tsd Ω := by
  have h2 : ContDiff ℝ 2 h := hh.of_le (by simp)
  refine smoothField_mem_tsd hΩ hb (fun ij => (contDiff_hessField hh ij).of_le (by simp))
    (fun i j x _ => (pd_pd_comm h2 i j x).symm) (fun x hx => hΔ x hx) (fun i x hx => ?_)
  simp only [hessField]
  have e : ∀ j, pd j (pd j (pd i h)) = pd i (pd j (pd j h)) := fun j => by
    have e1 : pd j (pd i h) = pd i (pd j h) := funext fun z => pd_pd_comm h2 j i z
    have h3 : ContDiff ℝ 2 (pd j h) := (contDiff_pd_top hh j).of_le (by simp)
    rw [e1]
    exact funext fun y => pd_pd_comm h3 j i y
  simp only [fun j => congrFun (e j) x]
  have hl : (fun y => ∑ j, pd j (pd j h) y) = lap h := rfl
  rw [← pd_sum _ (fun j _ => ((contDiff_pd_top (contDiff_pd_top hh j) j).differentiable
    (by simp))), hl]
  have hev : lap h =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hΩ.mem_nhds hx) fun y hy => hΔ y hy
  rw [pd, hev.fderiv_eq]
  simp

/-- **Hessians of harmonic functions lie in the obstruction** of `L²(TSD)` for `H̊(curl)`: they
are TSD and, being gradients, orthogonal to `L²(TSD₀) ⊇ L²(TSD) ∩ H̊(curl)`. -/
theorem hessL2_mem_obstruction (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {h : R3 → ℝ}
    (hh : ContDiff ℝ ∞ h) (hΔ : ∀ x ∈ Ω, lap h x = 0) :
    hessL2 hΩ hb hh ∈
      obstruction ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain (tsd Ω) :=
  inf_orthogonal_tsd₀_le_obstruction hΩ hb ⟨hessL2_mem_tsd hΩ hb hh hΔ, by
    rw [hessL2_eq_gradL2]; exact gradL2_mem_orthogonal_tsd₀ hΩ hb _⟩

/-! ## The obstruction is infinite-dimensional -/

/-- `e^{-t x₁} sin(t x₂)`. -/
def expSin (t : ℝ) (x : R3) : ℝ := Real.exp (-t * x 0) * Real.sin (t * x 1)

/-- `e^{-t x₁} cos(t x₂)` (harmonic). -/
def expCos (t : ℝ) (x : R3) : ℝ := Real.exp (-t * x 0) * Real.cos (t * x 1)

theorem pd_expSin (t : ℝ) (k : Fin 3) (x : R3) :
    pd k (expSin t) x = if k = 0 then -t * expSin t x else if k = 1 then t * expCos t x else 0 := by
  have h0 := ((hasFDerivAt_apply (0 : Fin 3) x).const_mul (-t)).exp
  have h1 := ((hasFDerivAt_apply (1 : Fin 3) x).const_mul t).sin
  have h2 : HasFDerivAt (expSin t) _ x := h0.mul h1
  rw [pd_of_hasFDerivAt h2]
  fin_cases k <;> simp [expSin, expCos] <;> ring

theorem pd_expCos (t : ℝ) (k : Fin 3) (x : R3) :
    pd k (expCos t) x =
      if k = 0 then -t * expCos t x else if k = 1 then -t * expSin t x else 0 := by
  have h0 := ((hasFDerivAt_apply (0 : Fin 3) x).const_mul (-t)).exp
  have h1 := ((hasFDerivAt_apply (1 : Fin 3) x).const_mul t).cos
  have h2 : HasFDerivAt (expCos t) _ x := h0.mul h1
  rw [pd_of_hasFDerivAt h2]
  fin_cases k <;> simp [expSin, expCos] <;> ring

theorem contDiff_expSin (t : ℝ) : ContDiff ℝ ∞ (expSin t) := by unfold expSin; fun_prop

theorem contDiff_expCos (t : ℝ) : ContDiff ℝ ∞ (expCos t) := by unfold expCos; fun_prop

theorem differentiable_expSin (t : ℝ) : Differentiable ℝ (expSin t) :=
  (contDiff_expSin t).differentiable (by simp)

theorem differentiable_expCos (t : ℝ) : Differentiable ℝ (expCos t) :=
  (contDiff_expCos t).differentiable (by simp)

theorem pd_expCos_fun (t : ℝ) (k : Fin 3) :
    pd k (expCos t) = fun x =>
      if k = 0 then -t * expCos t x else if k = 1 then -t * expSin t x else 0 :=
  funext (pd_expCos t k)

theorem pd_expSin_fun (t : ℝ) (k : Fin 3) :
    pd k (expSin t) = fun x =>
      if k = 0 then -t * expSin t x else if k = 1 then t * expCos t x else 0 :=
  funext (pd_expSin t k)

theorem pd_const_mul_fun {f : R3 → ℝ} (hf : Differentiable ℝ f) (c : ℝ) (k : Fin 3) :
    pd k (fun x => c * f x) = fun x => c * pd k f x :=
  funext (pd_const_mul hf c k)

/-- `∂₁ (e^{-t x₁} cos(t x₂)) = -t e^{-t x₁} cos(t x₂)`. -/
theorem pd0_expCos (t : ℝ) : pd 0 (expCos t) = fun x => -t * expCos t x := by
  rw [pd_expCos_fun]; simp

/-- `e^{-t x₁} cos(t x₂)` is harmonic. -/
theorem lap_expCos (t : ℝ) (x : R3) : lap (expCos t) x = 0 := by
  simp only [lap, Fin.sum_univ_three, pd_expCos_fun]
  simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq]
  rw [pd_const_mul_fun (differentiable_expCos t), pd_const_mul_fun (differentiable_expSin t),
    pd_expCos_fun, pd_expSin_fun]
  simp [pd]

/-- Smooth matrix fields on `ℝ³`. -/
def smoothFields : Submodule ℝ (Ix → R3 → ℝ) where
  carrier := {Ψ | ∀ ij, ContDiff ℝ ∞ (Ψ ij)}
  zero_mem' := fun _ => contDiff_const
  add_mem' := fun hΨ hΦ ij => (hΨ ij).add (hΦ ij)
  smul_mem' := fun c _ hΨ ij => (hΨ ij).const_smul c

/-- The restriction `Ψ ↦ [Ψ|_Ω] ∈ L²(Ω; ℝ³ˣ³)` of smooth fields. -/
def restrictL2 (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : smoothFields →ₗ[ℝ] L2F ℝ Ω Ix where
  toFun Ψ := smoothField hΩ hb Ψ fun ij => (Ψ.2 ij).continuous
  map_add' Ψ Φ := by
    refine (WithLp.ext_iff 2).2 (funext fun ij => Lp.ext ?_)
    filter_upwards [coeFn_smoothField hΩ hb (Ψ + Φ : smoothFields)
        (fun ij => ((Ψ + Φ).2 ij).continuous) ij,
      coeFn_smoothField hΩ hb Ψ (fun ij => (Ψ.2 ij).continuous) ij,
      coeFn_smoothField hΩ hb Φ (fun ij => (Φ.2 ij).continuous) ij,
      Lp.coeFn_add (smoothField hΩ hb Ψ (fun ij => (Ψ.2 ij).continuous) ij)
        (smoothField hΩ hb Φ (fun ij => (Φ.2 ij).continuous) ij)] with x h1 h2 h3 h4
    simp only [PiLp.add_apply] at h4 ⊢
    rw [h1, h4, Pi.add_apply, h2, h3]
    rfl
  map_smul' c Ψ := by
    refine (WithLp.ext_iff 2).2 (funext fun ij => Lp.ext ?_)
    filter_upwards [coeFn_smoothField hΩ hb (c • Ψ : smoothFields)
        (fun ij => ((c • Ψ).2 ij).continuous) ij,
      coeFn_smoothField hΩ hb Ψ (fun ij => (Ψ.2 ij).continuous) ij,
      Lp.coeFn_smul c (smoothField hΩ hb Ψ (fun ij => (Ψ.2 ij).continuous) ij)] with x h1 h2 h3
    simp only [PiLp.smul_apply, RingHom.id_apply] at h3 ⊢
    rw [h1, h3, Pi.smul_apply, h2]
    rfl

theorem restrictL2_apply (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (Ψ : smoothFields) :
    restrictL2 hΩ hb Ψ = smoothField hΩ hb Ψ fun ij => (Ψ.2 ij).continuous := rfl

/-- `∂₁` acting entrywise on smooth matrix fields. -/
def pd0L : smoothFields →ₗ[ℝ] smoothFields where
  toFun Ψ := ⟨fun ij => pd 0 (Ψ.1 ij), fun ij => contDiff_pd_top (Ψ.2 ij) 0⟩
  map_add' Ψ Φ := by
    refine Subtype.ext (funext fun ij => funext fun x => ?_)
    exact pd_add ((Ψ.2 ij).differentiable (by simp)) ((Φ.2 ij).differentiable (by simp)) 0 x
  map_smul' c Ψ := by
    refine Subtype.ext (funext fun ij => funext fun x => ?_)
    exact pd_const_mul ((Ψ.2 ij).differentiable (by simp)) c 0 x

/-- `∂₁` preserves the kernel of the restriction (fields vanishing on the open `Ω`). -/
theorem pd0L_mem_ker (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (Ψ : smoothFields)
    (hΨ : Ψ ∈ LinearMap.ker (restrictL2 hΩ hb)) :
    pd0L Ψ ∈ LinearMap.ker (restrictL2 hΩ hb) := by
  rw [LinearMap.mem_ker, restrictL2_apply] at hΨ ⊢
  refine smoothField_eq_zero hΩ hb _ fun ij x hx => ?_
  have h0 := eqOn_zero_of_smoothField_eq_zero hΩ hb _ hΨ ij
  have hev : Ψ.1 ij =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hΩ.mem_nhds hx) fun y hy => h0 y hy
  change pd 0 (Ψ.1 ij) x = 0
  rw [pd, hev.fderiv_eq]
  simp

/-- `∂₁ ∇²h = ∇²(∂₁ h)` (Schwarz). -/
theorem pd0_hessField {h : R3 → ℝ} (hh : ContDiff ℝ ∞ h) (ij : Ix) :
    pd 0 (hessField h ij) = hessField (pd 0 h) ij := by
  simp only [hessField]
  funext x
  have e1 : pd 0 (pd ij.1 h) = pd ij.1 (pd 0 h) :=
    funext fun y => pd_pd_comm (hh.of_le (by simp)) 0 ij.1 y
  rw [pd_pd_comm ((contDiff_pd_top hh _).of_le (by simp)) 0 ij.2 x, e1]

theorem hessField_const_mul {h : R3 → ℝ} (hh : ContDiff ℝ ∞ h) (c : ℝ) (ij : Ix) :
    hessField (fun x => c * h x) ij = fun x => c * hessField h ij x := by
  simp only [hessField]
  rw [pd_const_mul_fun (hh.differentiable (by simp)),
    pd_const_mul_fun ((contDiff_pd_top hh _).differentiable (by simp))]

/-- `∇²(e^{-t x₁} cos(t x₂))` as a smooth field. -/
def hessExp (t : ℝ) : smoothFields :=
  ⟨hessField (expCos t), contDiff_hessField (contDiff_expCos t)⟩

theorem pd0L_hessExp (t : ℝ) : pd0L (hessExp t) = (-t) • hessExp t := by
  refine Subtype.ext (funext fun ij => ?_)
  change pd 0 (hessField (expCos t) ij) = fun x => -t * hessField (expCos t) ij x
  rw [pd0_hessField (contDiff_expCos t), pd0_expCos, hessField_const_mul (contDiff_expCos t)]

theorem hessField_expCos_00 (t : ℝ) (x : R3) :
    hessField (expCos t) (0, 0) x = t ^ 2 * expCos t x := by
  simp only [hessField, pd0_expCos]
  rw [pd_const_mul_fun (differentiable_expCos t), pd0_expCos]
  ring

theorem hessField_expCos_01 (t : ℝ) (x : R3) :
    hessField (expCos t) (0, 1) x = t ^ 2 * expSin t x := by
  simp only [hessField, pd0_expCos]
  rw [pd_const_mul_fun (differentiable_expCos t), pd_expCos_fun]
  simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
  ring

theorem restrictL2_hessExp_ne_zero (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) {t : ℝ} (ht : t ≠ 0) : restrictL2 hΩ hb (hessExp t) ≠ 0 := by
  intro h0
  obtain ⟨x, hx⟩ := hne
  rw [restrictL2_apply] at h0
  have a := eqOn_zero_of_smoothField_eq_zero hΩ hb _ h0 (0, 0) x hx
  have b := eqOn_zero_of_smoothField_eq_zero hΩ hb _ h0 (0, 1) x hx
  change hessField (expCos t) (0, 0) x = 0 at a
  change hessField (expCos t) (0, 1) x = 0 at b
  rw [hessField_expCos_00] at a
  rw [hessField_expCos_01] at b
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
  have hex : Real.exp (-t * x 0) ≠ 0 := (Real.exp_pos _).ne'
  simp only [mul_eq_zero, ht2, false_or, expCos, expSin, hex] at a b
  have := Real.sin_sq_add_cos_sq (t * x 1)
  rw [a, b] at this
  norm_num at this

/-- **The Hessians `∇²(e^{-(n+1) x₁} cos((n+1) x₂))` are linearly independent in
`L²(Ω; ℝ³ˣ³)`** on every nonempty bounded open `Ω`: they are eigenvectors of `∂₁` (acting on
smooth fields modulo those vanishing on `Ω`) for distinct eigenvalues. -/
theorem linearIndependent_hessL2_expCos (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) :
    LinearIndependent ℝ (fun n : ℕ => hessL2 hΩ hb (contDiff_expCos ((n : ℝ) + 1))) := by
  set F := restrictL2 hΩ hb
  set N := LinearMap.ker F
  let D : Module.End ℝ (smoothFields ⧸ N) := N.mapQ N (pd0L) fun Ψ hΨ => pd0L_mem_ker hΩ hb Ψ hΨ
  have hli : LinearIndependent ℝ (fun n : ℕ => N.mkQ (hessExp ((n : ℝ) + 1))) := by
    refine Module.End.eigenvectors_linearIndependent' D (fun n : ℕ => -((n : ℝ) + 1))
      (fun m n h => by simpa using h) _ fun n => ?_
    refine Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 ?_, ?_⟩
    · change N.mkQ (pd0L (hessExp ((n : ℝ) + 1))) = _
      rw [pd0L_hessExp, LinearMap.map_smul]
    · rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_ker]
      exact restrictL2_hessExp_ne_zero hΩ hb hne (by positivity)
  have hinj : LinearMap.ker (N.liftQ F le_rfl) = ⊥ := Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  exact hli.map' (N.liftQ F le_rfl) hinj

/-- **`L²(TSD) ⊓ L²(TSD₀)ᗮ` is infinite-dimensional** on every nonempty bounded open `Ω`. -/
theorem not_finiteDimensional_inf_orthogonal_tsd₀ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) : ¬ FiniteDimensional ℝ (tsd Ω ⊓ (tsd₀ Ω hΩ hb)ᗮ : Submodule ℝ _) := by
  intro hfin
  let v : ℕ → (tsd Ω ⊓ (tsd₀ Ω hΩ hb)ᗮ : Submodule ℝ _) := fun n =>
    ⟨_, hessL2_mem_tsd hΩ hb (contDiff_expCos ((n : ℝ) + 1)) (fun x _ => lap_expCos _ x), by
      rw [hessL2_eq_gradL2]; exact gradL2_mem_orthogonal_tsd₀ hΩ hb _⟩
  have hli : LinearIndependent ℝ v :=
    LinearIndependent.of_comp (Submodule.subtype _) (linearIndependent_hessL2_expCos hΩ hb hne)
  exact Module.Finite.not_linearIndependent_of_infinite v hli

/-- **The obstruction of `L²(TSD)` for `H̊(curl)` is infinite-dimensional** on every nonempty
bounded open `Ω ⊆ ℝ³`: it contains the independent Hessians `∇²(e^{-n x₁} cos(n x₂))`.
[QuennevilleBelair2015], Prop 4.17 -/
theorem not_finiteDimensional_obstruction (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) : ¬ FiniteDimensional ℝ
      (obstruction ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain (tsd Ω)) := fun _ =>
  not_finiteDimensional_inf_orthogonal_tsd₀ hΩ hb hne
    (Submodule.finiteDimensional_of_le (inf_orthogonal_tsd₀_le_obstruction hΩ hb))

/-- **No finite-dimensional correction restores density**: for every finite-dimensional
subspace `F`, `L²(TSD) ⊄ cl (L²(TSD) ∩ H̊(curl)) + F`, on every nonempty bounded open `Ω`.
[QuennevilleBelair2015], Prop 4.17 -/
theorem not_tsd_le_closure_sup_finiteDimensional (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (F : Submodule ℝ (L2F ℝ Ω Ix)) [FiniteDimensional ℝ F] :
    ¬ tsd Ω ≤
      (tsd Ω ⊓ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain).topologicalClosure ⊔ F := by
  intro hle
  have hcl := closure_le_tsd₀ hΩ hb
  set P := (tsd₀ Ω hΩ hb)ᗮ.starProjection
  have hob : tsd Ω ⊓ (tsd₀ Ω hΩ hb)ᗮ ≤ F.map (P : L2F ℝ Ω Ix →ₗ[ℝ] L2F ℝ Ω Ix) := by
    intro G hG
    obtain ⟨z, hz, f, hf, rfl⟩ := Submodule.mem_sup.1 (hle hG.1)
    refine ⟨f, hf, ?_⟩
    have hPG : P (z + f) = z + f := Submodule.starProjection_eq_self_iff.2 hG.2
    have hPz : P z = 0 := (Submodule.starProjection_apply_eq_zero_iff _).2
      (Submodule.le_orthogonal_orthogonal _ (hcl hz))
    change P f = z + f
    rw [← hPG, map_add, hPz, zero_add]
  exact not_finiteDimensional_inf_orthogonal_tsd₀ hΩ hb hne
    (Submodule.finiteDimensional_of_le hob)

/-! ## Convex domains -/

/-- A nonempty open convex set is star-shaped with respect to a ball. -/
theorem exists_starBall_of_convex (hΩ : IsOpen Ω) (hc : Convex ℝ Ω) (hne : Ω.Nonempty) :
    ∃ x₀ : R3, ∃ s > 0, ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨s, hs, hsub⟩ := Metric.isOpen_iff.1 hΩ x₀ hx₀
  exact ⟨x₀, s, hs, fun y hy z hz => hc.segment_subset (hsub hz) hy⟩

/-- `cl (L²(TSD) ∩ H̊(curl)) = L²(TSD₀)` on a nonempty bounded open convex `Ω`. -/
theorem closure_eq_tsd₀_of_convex (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hc : Convex ℝ Ω) (hne : Ω.Nonempty) :
    (tsd Ω ⊓ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain).topologicalClosure =
      tsd₀ Ω hΩ hb := by
  obtain ⟨x₀, s, hs, hstar⟩ := exists_starBall_of_convex hΩ hc hne
  exact closure_eq_tsd₀ hΩ hb hs hstar

/-- `cl (L²(TSD) ∩ H̊(curl)) = L²(TSD₀)` on a ball. -/
theorem closure_eq_tsd₀_ball (x₀ : R3) {R : ℝ} (hR : 0 < R) :
    (tsd (Metric.ball x₀ R) ⊓
      ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal (Metric.ball x₀ R)).domain).topologicalClosure =
      tsd₀ (Metric.ball x₀ R) Metric.isOpen_ball Metric.isBounded_ball :=
  closure_eq_tsd₀_of_convex _ _ (convex_ball x₀ R) (Metric.nonempty_ball.2 hR)

/-- The obstruction is exactly `L²(TSD) ⊓ L²(TSD₀)ᗮ` on a nonempty bounded open convex `Ω`. -/
theorem obstruction_eq_tsd₀_of_convex (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hc : Convex ℝ Ω) (hne : Ω.Nonempty) :
    obstruction ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain (tsd Ω) =
      tsd Ω ⊓ (tsd₀ Ω hΩ hb)ᗮ := by
  obtain ⟨x₀, s, hs, hstar⟩ := exists_starBall_of_convex hΩ hc hne
  exact obstruction_eq_tsd₀ hΩ hb hs hstar

/-! ## Density of `L²(TSD) ∩ H(curl)` in `L²(TSD)` -/

/-- A field of `L²(TSD)` satisfies the TSD constraints in `𝒟'(Ω)` (tested against `C_c^∞(Ω)`
only; compare `tsdOp_weak_of_mem_tsd₀`). -/
theorem tsdOp_weak_of_mem_tsd (hΩ : IsOpen Ω) {B : L2F ℝ Ω Ix} (hB : B ∈ tsd Ω)
    (ψ : TsdRow → R3 → ℝ) (hψ : IsTestField Ω ψ) :
    ∑ ij, ∫ x, Ω.indicator (B ij : R3 → ℝ) x * tsdOp.formalAdj.apply ψ ij x = 0 := by
  have hli : ∀ ij, LocallyIntegrable (Ω.indicator (B ij : R3 → ℝ)) volume := fun ij =>
    ((memLp_indicator_iff_restrict hΩ.measurableSet.nullMeasurableSet).2
      (Lp.memLp (B ij))).locallyIntegrable (by norm_num)
  set u : Ix → R3 → ℝ := fun ij => Ω.indicator (B ij : R3 → ℝ) with hu
  have hψu : ∀ r, IsTest (univ : Set R3) (ψ r) := fun r => (hψ r).mono (subset_univ _)
  have hψtr : IsTest (univ : Set R3) (ψ (Sum.inr (Sum.inl ()))) := hψu _
  have hψd : ∀ ij : Ix, IsTest (univ : Set R3) (fun x => pd ij.2 (ψ (Sum.inr (Sum.inr ij.1))) x) :=
    fun ij => (hψu _).fderiv_apply _
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
    have i1 := I ij (hψu (Sum.inl ij))
    have i2 := I ij (hψu (Sum.inl (ij.2, ij.1)))
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
  have h12 : ∑ ij : Ix, ∫ x, u ij x * ψ (Sum.inl (ij.2, ij.1)) x =
      ∑ ij : Ix, ∫ x, u ij x * ψ (Sum.inl ij) x := by
    refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun ij => ?_
    obtain ⟨i, j⟩ := ij
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk, hu]
    rw [hB.1 i j]
  have h3 : ∑ ij : Ix, ∫ x, u ij x * (if ij.1 = ij.2 then ψ (Sum.inr (Sum.inl ())) x else 0) =
      0 := by
    have e3 : ∀ ij : Ix, ∫ x, u ij x * (if ij.1 = ij.2 then ψ (Sum.inr (Sum.inl ())) x else 0) =
        if ij.1 = ij.2 then ∫ x, u ij x * ψ (Sum.inr (Sum.inl ())) x else 0 := fun ij => by
      split_ifs <;> simp
    simp only [e3, Fintype.sum_prod_type, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have htr := hB.2.1
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
  have h4 : ∑ ij : Ix, ∫ x, u ij x * pd ij.2 (ψ (Sum.inr (Sum.inr ij.1))) x = 0 := by
    simp only [hu, integral_indicator_mul hΩ]
    rw [← inner_grad_testField B (fun i => hψ (Sum.inr (Sum.inr i)))]
    exact hB.2.2 (fun i => ψ (Sum.inr (Sum.inr i))) (fun i => hψ (Sum.inr (Sum.inr i)))
  rw [h12, h3, h4]
  ring

/-- **Density of smooth TSD fields in `L²(TSD)`** (no boundary condition) on a bounded open `Ω`
star-shaped with respect to a ball: every `B ∈ L²(TSD)` is an `L²` limit of fields smooth on
`ℝ³`, symmetric, trace-free and divergence-free on `Ω`; these lie in `L²(TSD) ∩ H(curl)`. An
instance of `Feec.Domain.exists_contDiff_ker_on_dist_lt` for `tsdOp`. -/
theorem tsd_le_closure_curl_maximal (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {x₀ : R3}
    {s : ℝ} (hs : 0 < s) (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) :
    tsd Ω ≤ (tsd Ω ⊓
      ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.maximal Ω).domain).topologicalClosure := by
  intro B hB
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨φ, hφ, hAφ, hd⟩ := exists_contDiff_ker_on_dist_lt hΩ hb hs hstar tsdOp
    tsdOp_isRowHomogeneous B (tsdOp_weak_of_mem_tsd hΩ hB) hε
  have hφ1 : ∀ ij, ContDiff ℝ 1 (φ ij) := fun ij => (hφ ij).of_le (by simp)
  have hsym : ∀ a b, ∀ x ∈ Ω, φ (a, b) x = φ (b, a) x := fun a b x hx => by
    have := hAφ (Sum.inl (a, b)) x hx
    rw [tsdOp_apply_sym] at this
    linarith
  have htr : ∀ x ∈ Ω, ∑ i, φ (i, i) x = 0 := fun x hx => by
    have := hAφ (Sum.inr (Sum.inl ())) x hx
    rwa [tsdOp_apply_tr] at this
  have hdiv : ∀ i, ∀ x ∈ Ω, ∑ j, pd j (φ (i, j)) x = 0 := fun i x hx => by
    have := hAφ (Sum.inr (Sum.inr i)) x hx
    rwa [tsdOp_apply_div] at this
  exact ⟨_, ⟨smoothField_mem_tsd hΩ hb hφ1 hsym htr hdiv,
    (smoothField_mem_curl_maximal hΩ hb hφ1).1⟩, hd⟩

/-- **`cl (L²(TSD) ∩ H(curl)) = L²(TSD)`** on a bounded open `Ω` star-shaped with respect to a
ball: without the boundary condition the density inferred in the proof of Prop 4.17 holds.
Compare `closure_eq_tsd₀`: with `H̊(curl)` the closure is the proper subspace `L²(TSD₀)`.
[QuennevilleBelair2015], Prop 4.17 -/
theorem closure_tsd_inf_curl_maximal (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {x₀ : R3}
    {s : ℝ} (hs : 0 < s) (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) :
    (tsd Ω ⊓
      ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.maximal Ω).domain).topologicalClosure =
      tsd Ω :=
  le_antisymm (Submodule.topologicalClosure_minimal _ inf_le_left isClosed_tsd)
    (tsd_le_closure_curl_maximal hΩ hb hs hstar)

theorem closure_tsd_inf_curl_maximal_of_convex (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hc : Convex ℝ Ω) (hne : Ω.Nonempty) :
    (tsd Ω ⊓
      ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.maximal Ω).domain).topologicalClosure =
      tsd Ω := by
  obtain ⟨x₀, s, hs, hstar⟩ := exists_starBall_of_convex hΩ hc hne
  exact closure_tsd_inf_curl_maximal hΩ hb hs hstar

theorem closure_tsd_inf_curl_maximal_ball (x₀ : R3) {R : ℝ} (hR : 0 < R) :
    (tsd (Metric.ball x₀ R) ⊓ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.maximal
      (Metric.ball x₀ R)).domain).topologicalClosure = tsd (Metric.ball x₀ R) :=
  closure_tsd_inf_curl_maximal_of_convex Metric.isOpen_ball Metric.isBounded_ball
    (convex_ball x₀ R) (Metric.nonempty_ball.2 hR)

/-- The `H(curl)` density holds inside `H(curl) ∩ H(div)`, the magnetic component of `D(L)` of
Prop 4.17 (`L²(TSD) ⊆ H(div)`). -/
theorem closure_tsd_inf_curl_maximal_inf_adjoint (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : R3} {s : ℝ} (hs : 0 < s)
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s, segment ℝ z y ⊆ Ω) :
    (tsd Ω ⊓ (((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.maximal Ω).domain ⊓
      (gradCurl ℝ hΩ).d₀†.domain)).topologicalClosure = tsd Ω := by
  have e : tsd Ω ⊓ (((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.maximal Ω).domain ⊓
      (gradCurl ℝ hΩ).d₀†.domain) =
      tsd Ω ⊓ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).formalAdj.maximal Ω).domain := by
    refine le_antisymm (inf_le_inf_left _ inf_le_left) fun B hB => ⟨hB.1, hB.2, ?_⟩
    exact (gradCurl ℝ hΩ).d₀†.ker_le_domain ((mem_tsd_iff_ker hΩ).1 hB.1).2.2
  rw [e, closure_tsd_inf_curl_maximal hΩ hb hs hstar]

/-! ## The largest propagating constraint space `K*` -/

section InvariantCore

-- Over `ℝ` the generic real structure on the window spaces duplicates the inner-product one.
attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

variable {W₀ : Type} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] [CompleteSpace W₀]

/-- **The electric slot of `K*` lies in `L²(TSD₀)`** for every short complex with
`D(d₁) ⊆ H̊(curl)`, `K = {0} × L²(TSD) × S₂`: `D(L) ∩ K*` is dense in `K*`, its electric fields
lie in `L²(TSD) ∩ H̊(curl) ⊆ L²(TSD₀)`, and `L²(TSD₀)` is closed. -/
theorem invariantCore₁_le_tsd₀ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (S : ShortHilbertComplex ℝ W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))
    (hd₁ : S.d₁.domain ≤ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain)
    (S₂ : Submodule ℝ (L2F ℝ Ω Ix)) [S₂.HasOrthogonalProjection] :
    S.invariantCore₁ (tsd Ω) S₂ ≤ tsd₀ Ω hΩ hb := by
  intro u hu
  have hcl := ShortHilbertComplex.mem_closure_wave_domain_inter_coreSub
    (ShortHilbertComplex.mem_invariantCore₁.1 hu)
  let π : PiLp 2 (ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix)) →L[ℝ] L2F ℝ Ω Ix :=
    PiLp.proj 2 (fun i => ShortHilbertComplex.W3 W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix) i) 1
  have := map_mem_closure π.continuous hcl (t := (tsd₀ Ω hΩ hb : Set (L2F ℝ Ω Ix)))
    fun y ⟨hyD, hyK⟩ => by
      obtain ⟨-, h1, -⟩ := ShortHilbertComplex.mem_coreSub_iff.1 hyK
      exact inf_le_tsd₀ hΩ hb ⟨ShortHilbertComplex.invariantCore₁_le h1,
        hd₁ ((S.mem_wave_domain).1 hyD).2.1⟩
  rwa [(isClosed_tsd₀ hΩ hb).closure_eq] at this

/-- `d₁†` maps the magnetic slot of `K*` into `L²(TSD₀)`. -/
theorem adjoint_mem_tsd₀_of_mem_invariantCore₂ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (S : ShortHilbertComplex ℝ W₀ (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))
    (hd₁ : S.d₁.domain ≤ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).minimal Ω).domain)
    (S₂ : Submodule ℝ (L2F ℝ Ω Ix)) [S₂.HasOrthogonalProjection] (ρ : S.d₁†.domain)
    (hρ : (ρ : L2F ℝ Ω Ix) ∈ S.invariantCore₂ (tsd Ω) S₂) : S.d₁† ρ ∈ tsd₀ Ω hΩ hb :=
  invariantCore₁_le_tsd₀ hΩ hb S hd₁ S₂ (ShortHilbertComplex.adjoint_mem_invariantCore₁ ρ hρ)

/-- **Curl-free magnetic fields are stationary data**: for the grad–curl complex, if `B ∈ S₂` has
weak curl `0` (`⟪B, curl Φ⟫ = 0` for every test field `Φ`), then `B ∈ D(d₁†)`, `d₁† B = 0`, and
`B ∈ S₂*`. -/
theorem mem_invariantCore₂_of_curl_eq_zero (hΩ : IsOpen Ω) (S₁ S₂ : Submodule ℝ (L2F ℝ Ω Ix))
    {B : L2F ℝ Ω Ix} (hB : B ∈ S₂)
    (hc : ∀ (Φ : Ix → R3 → ℝ) (hΦ : IsTestField Ω Φ),
      ⟪B, testField ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).isTestField_apply hΦ)⟫_ℝ = 0) :
    B ∈ (gradCurl ℝ hΩ).invariantCore₂ S₁ S₂ := by
  have key : ∀ (Φ : Ix → R3 → ℝ) (hΦ : IsTestField Ω Φ), ⟪(0 : L2F ℝ Ω Ix), testField hΦ⟫_ℝ =
      ⟪B, testField ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).isTestField_apply hΦ)⟫_ℝ :=
    fun Φ hΦ => by rw [inner_zero_left, hc Φ hΦ]
  have hmem := ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).mem_adjoint_minimal_domain_iff hΩ).2 ⟨0, key⟩
  exact ShortHilbertComplex.mem_invariantCore₂_of_eq_zero (S := gradCurl ℝ hΩ) ⟨B, hmem⟩ hB
    ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).adjoint_minimal_apply_eq hΩ _ key)

/-- **Hessians of harmonic functions are stationary magnetic data**: `∇²h ∈ S₂*` for
`S₂ = L²(TSD)` (`curl ∇²h = 0`). -/
theorem hessL2_mem_invariantCore₂ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (S₁ : Submodule ℝ (L2F ℝ Ω Ix)) {h : R3 → ℝ} (hh : ContDiff ℝ ∞ h)
    (hΔ : ∀ x ∈ Ω, lap h x = 0) : hessL2 hΩ hb hh ∈ (gradCurl ℝ hΩ).invariantCore₂ S₁ (tsd Ω) := by
  obtain ⟨hmem, e⟩ := smoothField_mem_adjoint hΩ hb (gradCurl ℝ hΩ) le_rfl
    (fun ij => (contDiff_hessField hh ij).of_le (by simp))
  refine ShortHilbertComplex.mem_invariantCore₂_of_eq_zero (S := gradCurl ℝ hΩ) ⟨_, hmem⟩
    (hessL2_mem_tsd hΩ hb hh hΔ) ?_
  rw [e]
  refine smoothField_eq_zero hΩ hb _ fun ij x _ => ?_
  rw [hessField_eq_gradM]
  exact curlM_gradM (fun i => (contDiff_pd_top hh i).of_le (by simp)) ij x

/-- **The stationary part of `K*` is infinite-dimensional**: for the grad–curl complex on a
nonempty bounded open `Ω`, `S₂*` (with `S₂ = L²(TSD)`) contains the independent harmonic Hessians
`∇²(e^{-n x₁} cos(n x₂))`. -/
theorem not_finiteDimensional_invariantCore₂ (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (S₁ : Submodule ℝ (L2F ℝ Ω Ix)) :
    ¬ FiniteDimensional ℝ ((gradCurl ℝ hΩ).invariantCore₂ S₁ (tsd Ω)) := by
  intro hfin
  let v : ℕ → (gradCurl ℝ hΩ).invariantCore₂ S₁ (tsd Ω) := fun n =>
    ⟨_, hessL2_mem_invariantCore₂ hΩ hb S₁ (contDiff_expCos ((n : ℝ) + 1))
      (fun x _ => lap_expCos _ x)⟩
  have hli : LinearIndependent ℝ v :=
    LinearIndependent.of_comp (Submodule.subtype _) (linearIndependent_hessL2_expCos hΩ hb hne)
  exact Module.Finite.not_linearIndependent_of_infinite v hli

end InvariantCore

end Feec.Models.BoundedDomain
