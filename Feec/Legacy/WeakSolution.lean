module

public import Feec.Legacy.WaveGroup
public import Feec.Legacy.ErrorEstimate

/-!
# Remaining Ch. 4 results with their existence hypotheses discharged

**Status.** Part of `Feec.Legacy`, the real-scalar short-complex development (built on
`Feec.Legacy.HilbertComplex2`) that the cube models and some counterexamples still use. It
keeps only what those modules need and the results that have no home in the general layers
yet; everything else moved there (see `docs/migration/map.tsv`).

`Feec.Legacy.WaveGroup` discharges, via Stone's theorem (`Feec.Legacy.stoneGroup`), the existence
hypotheses (`WellPosedHom`, `WellPosedExistence`, `WellPosedClassical`, `UnitaryGroupGenerator`)
of Thm 4.3, Cor 4.5, Thm 4.6 (classical form), Thm 4.7, Props 4.16–4.18 and of the
bounded-domain counterexample to Prop 4.17. This module covers the remaining sites. Each fact is
stated once; former names are kept as corollaries or aliases.

* `Feec.Evolution.IsStrongSolution.mem_of_isReducing`: the kernel-constraint corollary after Cor 4.5
  (`Feec.constraint_ker_exists`), forcing in `ForcingThm43`.
* Semi-discrete convergence (§4.6): `HilbertComplex2.exists_isWeakSol_of_waveOp_mem` (for
  `ξ₀ ∈ D(L²)` the exact solution exists in the class `C¹([0,T]; V)` assumed by Thm 4.14, via
  the graph-norm differentiability lemmas `UnitaryGroupGenerator.continuous_graph`,
  `UnitaryGroupGenerator.hasDerivAt_graph` and the bound `norm_toV_le`) and
  `HilbertComplex2.tendstoUniformlyOn_discreteSol` (`ξₕ → ξ` uniformly in `W` on `[0,T]` for
  every `ξ₀ ∈ D(L²)`, the exact solution no longer assumed), with `AlgSegment.isWeakSol_unique`
  (energy uniqueness of weak solutions in `C¹([0,T]; V)`).
* Constraints: `Constraints.existsUnique_classicalSolution_mem_Kc` (abstract Props 4.17/4.19
  with existence and the thesis' regularity), `Constraints.waveGroup_mem_Kc_of_nonneg` (the
  Stone group of `-L` maps `D(L) ∩ K` into `K` for `t ≥ 0`), `Constraints.waveGroup_mem_Kc`
  (for all `t ∈ ℝ`, via time reversal).

The torus results already have unconditional forms in their own modules
(`Feec.Models.Torus.GradCurl.tsd_existsUnique`, `Feec.Models.Torus.GradCurl.waveGroup_mem`,
`Feec.Models.Torus.SymCurl.tsd_existsUnique`, `Feec.Models.Torus.SymCurl.waveGroup_mem`). The Ch. 6
discrete existence results (`prop_6_2_exists`) were never conditional. For the continuous
Ch. 6 problem (6.1), the abstract `Feec.ContData` carries no Hilbert-complex structure, so
existence is not stated for it; the concrete complex (5.1) is built as a `HilbertComplex2` on
bounded domains in `Feec.Legacy.BoundedBGG` (existence and uniqueness: `bggComplex_divFree_propagates`) and on
`ℝ³` in `Feec.Legacy.WholeBGG` (`bggWhole_verdict`). The full forcing class of Thm 4.3,
`C([0,T]; X) ∩ (W^{1,1}(0,T; X) ∪ L¹(0,T; D(L)))`, is covered by
`LinearPMap.IsSkewAdjoint.existsUnique_classicalSolution` (`Feec.Evolution.Forcing`).

Thesis gap: Thm 4.14 assumes the exact solution in `C¹([0,T]; V)` without saying for which data
it exists; `exists_isWeakSol_of_waveOp_mem` shows `ξ₀ ∈ D(L²)` suffices. For `ξ₀ ∈ D(L)` alone
the `C¹(V)` solution can fail to exist (`Feec.Legacy.FredholmCE.cxK1_exists_not_isWeakSol`), but the
convergence claimed after Thm 4.14 still holds, for `D(L)` data with `ξₕ(0) = Πₕ ξ₀` and for `W`
data with `ξₕ(0) → ξ₀` (`HilbertComplex2.convergence_domL_weakSolution`,
`HilbertComplex2.convergence_W_exists` in `Feec.Legacy.ErrorEstimateDomain`), without a rate.

## References

* [QuennevilleBelair2015], §4.3 (Thm 4.3, Cor 4.5 and the kernel remark after it), §4.4
  (Thm 4.6, (4.7)/(4.8), Thm 4.7), §4.6 (Thm 4.14 and convergence), §4.10–4.11
  (Props 4.16–4.19)
* [Pazy1983], §1.2 (Thm 2.4, regularity of orbits), §1.10 (Stone's theorem), §4.2 (Duhamel's
  formula)
* [Arnold2018] (Hilbert complexes and the Hodge wave operator)
-/

open scoped RealInnerProductSpace LinearPMap
open Set

@[expose] public noncomputable section

namespace Feec.Legacy

section GraphDeriv

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {A : E →ₗ.[ℝ] E}

/-- Orbits of a unitary group are continuous in any space `V` into which `D(A)` maps by a linear
map bounded by the graph norm, `‖Φ z‖ ≤ c (‖z‖ + ‖A z‖)` (auxiliary; `A (S t x) = S t (A x)`,
cf. [Pazy1983, §1.2, Thm 2.4]). -/
theorem UnitaryGroupGenerator.continuous_graph (G : UnitaryGroupGenerator A)
    (Φ : A.domain →ₗ[ℝ] V) (c : ℝ) (hΦ : ∀ z, ‖Φ z‖ ≤ c * (‖(z : E)‖ + ‖A z‖))
    (x : A.domain) : Continuous fun s => Φ ⟨G.S s x, G.mem_domain_apply x s⟩ := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Filter.Tendsto (fun s => c * (‖G.S s x - G.S t x‖ + ‖G.S s (A x) - G.S t (A x)‖))
      (nhds t) (nhds 0) := by
    have a := (tendsto_iff_norm_sub_tendsto_zero.1 ((G.continuous_apply (x : E)).tendsto t))
    have b := (tendsto_iff_norm_sub_tendsto_zero.1 ((G.continuous_apply (A x)).tendsto t))
    simpa using (a.add b).const_mul c
  refine squeeze_zero (fun _ => norm_nonneg _) (fun s => ?_) h1
  rw [← map_sub]
  refine (hΦ _).trans (le_of_eq ?_)
  rw [LinearPMap.map_sub, G.apply_comm, G.apply_comm]
  rfl

/-- Orbits of points `x ∈ D(A)` with `A x ∈ D(A)` are differentiable in any space `V` into which
`D(A)` maps by a linear map bounded by the graph norm: `(d/dt) Φ(S t x) = Φ(S t (A x))`
(auxiliary; [Pazy1983, §1.2, Thm 2.4 (c)] applied to `x` and to `A x`). -/
theorem UnitaryGroupGenerator.hasDerivAt_graph (G : UnitaryGroupGenerator A)
    (Φ : A.domain →ₗ[ℝ] V) (c : ℝ) (hΦ : ∀ z, ‖Φ z‖ ≤ c * (‖(z : E)‖ + ‖A z‖))
    (x y : A.domain) (hxy : A x = y) (t : ℝ) :
    HasDerivAt (fun s => Φ ⟨G.S s x, G.mem_domain_apply x s⟩)
      (Φ ⟨G.S t y, G.mem_domain_apply y t⟩) t := by
  rw [hasDerivAt_iff_isLittleO]
  have hx := hasDerivAt_iff_isLittleO.1 (G.hasDerivAt_apply x t)
  have hy := hasDerivAt_iff_isLittleO.1 (G.hasDerivAt_apply y t)
  rw [hxy] at hx
  have hsum := (hx.norm_left.add hy.norm_left).const_mul_left c
  refine Asymptotics.IsBigO.trans_isLittleO (Asymptotics.IsBigO.of_bound 1
    (Filter.Eventually.of_forall fun s => ?_)) hsum
  rw [one_mul, Real.norm_eq_abs]
  set z : A.domain := ⟨G.S s x, G.mem_domain_apply x s⟩ - ⟨G.S t x, G.mem_domain_apply x t⟩
    - (s - t) • ⟨G.S t y, G.mem_domain_apply y t⟩ with hz
  have hΦz : Φ ⟨G.S s x, G.mem_domain_apply x s⟩ - Φ ⟨G.S t x, G.mem_domain_apply x t⟩
      - (s - t) • Φ ⟨G.S t y, G.mem_domain_apply y t⟩ = Φ z := by
    rw [hz, map_sub, map_sub, map_smul]
  have hAz : A z = G.S s y - G.S t y - (s - t) • G.S t (A y) := by
    rw [hz, LinearPMap.map_sub, LinearPMap.map_sub, LinearPMap.map_smul, G.apply_comm,
      G.apply_comm, G.apply_comm, hxy]
  have hz' : (z : E) = G.S s x - G.S t x - (s - t) • G.S t y := rfl
  rw [hΦz]
  refine (hΦ z).trans (le_trans ?_ (le_abs_self _))
  rw [hAz, hz']

end GraphDeriv

namespace AlgSegment

open HilbertComplex2 (Tot tot)

variable {X0 X1 X2 : Type*}
  [NormedAddCommGroup X0] [InnerProductSpace ℝ X0]
  [NormedAddCommGroup X1] [InnerProductSpace ℝ X1]
  [NormedAddCommGroup X2] [InnerProductSpace ℝ X2]
  {C : AlgSegment X0 X1 X2}

/-- **Uniqueness of weak solutions in `C¹([0,T]; V)`** (`IsWeakSol`, the class of Thm 4.14):
two weak solutions with the same initial value agree on `[0,T]`. Energy proof (thesis l.2120):
testing (4.8) for both with `ψ = ξ₁ − ξ₂` gives `d/dt ‖ξ₁ − ξ₂‖_W² = −2a(ξ₁ − ξ₂, ξ₁ − ξ₂) = 0`,
then the energy inequality `norm_le_norm_zero_of_inner_deriv_nonpos`; the `W`-norm is definite
on `V`. The continuous counterpart of
`AlgSegment.discrete_solution_unique`.
See [QuennevilleBelair2015, §4.4, l.2120 and §4.6]. -/
theorem isWeakSol_unique {T : ℝ} {ξ₁ ξ₁' ξ₂ ξ₂' : ℝ → C.VSp}
    (h₁ : C.IsWeakSol T ξ₁ ξ₁') (h₂ : C.IsWeakSol T ξ₂ ξ₂') (h0 : ξ₁ 0 = ξ₂ 0) :
    ∀ t ∈ Icc 0 T, ξ₁ t = ξ₂ t := by
  obtain ⟨c₁, -, d₁, e₁⟩ := h₁
  obtain ⟨c₂, -, d₂, e₂⟩ := h₂
  set e : ℝ → Tot X0 X1 X2 := fun t => C.toW (ξ₁ t - ξ₂ t) with he
  have hec : ContinuousOn e (Icc 0 T) := C.toW.continuous.comp_continuousOn (c₁.sub c₂)
  have hed : ∀ t ∈ Ico 0 T, HasDerivWithinAt e (C.toW (ξ₁' t - ξ₂' t)) (Ici t) t :=
    fun t ht => C.toW.hasFDerivAt.comp_hasDerivWithinAt t ((d₁ t ht).sub (d₂ t ht))
  have key := norm_le_norm_zero_of_inner_deriv_nonpos hec hed (fun t ht => by
    have E1 := e₁ t ht (ξ₁ t - ξ₂ t)
    have E2 := e₂ t ht (ξ₁ t - ξ₂ t)
    have hs := C.aL_self (ξ₁ t - ξ₂ t)
    simp only [he, map_sub, inner_sub_left, inner_sub_right, LinearMap.sub_apply] at E1 E2 hs ⊢
    have r1 := real_inner_comm (C.toW (ξ₁ t)) (C.toW (ξ₁' t))
    have r2 := real_inner_comm (C.toW (ξ₁ t)) (C.toW (ξ₂' t))
    have r3 := real_inner_comm (C.toW (ξ₂ t)) (C.toW (ξ₁' t))
    have r4 := real_inner_comm (C.toW (ξ₂ t)) (C.toW (ξ₂' t))
    linarith)
  intro t ht
  have h := key t ht
  simp only [he, h0, sub_self, map_zero, norm_zero] at h
  have : C.toW (ξ₁ t - ξ₂ t) = C.toW 0 := by
    rw [map_zero]; exact norm_le_zero_iff.1 h
  exact sub_eq_zero.1 (C.toW_injective this)

end AlgSegment

namespace HilbertComplex2

variable {W0 W1 W2 : Type*}
  [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
  (H : HilbertComplex2 W0 W1 W2)

/-- **Thesis Thm 4.6**, full statement, unconditional: for every Hilbert complex of length 2,
`L` is densely defined and skew-adjoint, and every `ξ₀ ∈ D(L)` has a strong solution of
`ξ' = -Lξ`, `ξ(0) = ξ₀` on `[0,T]`, which is unique and conserves energy.
Corollary of the classical form `HilbertComplex2.existsUnique_classicalSolution_neg_waveOp`.
See [QuennevilleBelair2015, Thm 4.6]. -/
theorem existsUnique_strongSolution_neg_waveOp (T : ℝ) {ξ₀ : Tot W0 W1 W2}
    (h0 : ξ₀ ∈ H.waveOp.domain) :
    Dense (H.waveOp.domain : Set (Tot W0 W1 W2)) ∧ IsSkewAdjoint H.waveOp ∧
      ∃ ξ, IsStrongSolution (-H.waveOp) T ξ₀ 0 ξ ∧
        (∀ ξ', IsStrongSolution (-H.waveOp) T ξ₀ 0 ξ' → EqOn ξ' ξ (Icc 0 T)) ∧
        ∀ t ∈ Icc 0 T, ‖ξ t‖ = ‖ξ₀‖ := by
  obtain ⟨ξ, hξ, huniq, hnorm⟩ := H.existsUnique_classicalSolution_neg_waveOp T h0
  exact ⟨H.dense_domL, H.waveOp_isSkewAdjoint, ξ, hξ.toIsStrongSolution, huniq, hnorm⟩

/-- **Thesis Thm 4.7, second bullet** (weak ⇒ strong): a weak solution of (4.7)/(4.8) with
initial value in `D(L)` is a strong solution of (4.4). Corollary of
`HilbertComplex2.isClassicalSolution_of_isWeakSolution`.
See [QuennevilleBelair2015, Thm 4.7]. -/
theorem isStrongSolution_of_isWeakSolution {T : ℝ} {ξ₀ : Tot W0 W1 W2}
    (h0 : ξ₀ ∈ H.waveOp.domain) {ξ : ℝ → Tot W0 W1 W2} (hξ : H.IsWeakSolution T ξ₀ ξ) :
    IsStrongSolution (-H.waveOp) T ξ₀ 0 ξ :=
  (H.isClassicalSolution_of_isWeakSolution h0 hξ).toIsStrongSolution

/-- **Existence and uniqueness of weak solutions** of the Hodge wave equation (4.7)/(4.8)
(Thesis §4.4), unconditional: for every Hilbert complex and every `ξ₀ ∈ D(L)` there is a weak
solution in the thesis' class `C⁰([0,T]; V) ∩ C¹([0,T]; W)`, and every weak solution with the
same initial value agrees with it on `[0,T]`. Combines `existsUnique_classicalSolution_neg_waveOp`,
`isClassicalWeakSolution_of_isClassicalSolution` and `weak_unique`.
See [QuennevilleBelair2015, §4.4, (4.7)–(4.8) and Thm 4.7]. -/
theorem existsUnique_classicalWeakSolution (T : ℝ) {ξ₀ : Tot W0 W1 W2}
    (h0 : ξ₀ ∈ H.waveOp.domain) :
    ∃ ξ, H.IsClassicalWeakSolution T ξ₀ ξ ∧
      ∀ ξ', H.IsWeakSolution T ξ₀ ξ' → EqOn ξ' ξ (Icc 0 T) := by
  obtain ⟨ξ, hξ, -, -⟩ := H.existsUnique_classicalSolution_neg_waveOp T h0
  have hw := H.isClassicalWeakSolution_of_isClassicalSolution hξ
  exact ⟨ξ, hw, fun ξ' hξ' => H.weak_unique hξ' hw.toIsWeakSolution⟩

/-! ### The exact solution in `C¹([0,T]; V)` and convergence of the semi-discrete method -/

open AlgSegment in
/-- The inclusion `D(L) → V = V⁰ × V¹ × W²` of the domain of the Hodge wave operator into the
space `V` of the weak form, `(σ, u, ρ) ↦ (σ, u, ρ)` (auxiliary; `V` carries the graph norm of
`Feec.Legacy.AlgSegment.VSp` for the segment `H.toAlgSegment`). -/
def toV : H.domL →ₗ[ℝ] H.toAlgSegment.VSp where
  toFun x := H.toAlgSegment.mkV (H.pr0 x) (H.prV1 x) (tot W0 W1 W2 x).2.2
  map_add' x y := by
    rw [mkV_add, ← map_add, ← map_add]
    rfl
  map_smul' r x := by
    rw [mkV_smul, ← map_smul, ← map_smul]
    rfl

/-- The `V`-norm is controlled by the graph norm of `L`: `‖x‖_V ≤ ‖x‖_W + ‖L x‖_W` on `D(L)`.
Uses `d0 σ ⟂ d1* ρ` (`norm_embed`). Cf. [QuennevilleBelair2015, Thm 4.7, proof]. -/
theorem norm_toV_le (x : H.domL) :
    ‖H.toV x‖ ≤ ‖(x : Tot W0 W1 W2)‖ + ‖H.waveOp ⟨x.1, x.2⟩‖ := by
  have hV : ‖H.toV x‖ ^ 2 = ‖(tot W0 W1 W2 x).1‖ ^ 2 + ‖H.d0 (H.pr0 x)‖ ^ 2 +
      ‖(tot W0 W1 W2 x).2.1‖ ^ 2 + ‖H.d1 (H.prV1 x)‖ ^ 2 + ‖(tot W0 W1 W2 x).2.2‖ ^ 2 :=
    H.toAlgSegment.norm_mkV_sq _ _ _
  have hx := tot_norm_sq (x : Tot W0 W1 W2)
  have hL := tot_norm_sq (H.waveOp ⟨x.1, x.2⟩)
  rw [tot_waveOp, norm_neg, norm_neg, H.norm_embed] at hL
  have e0 : H.pr0 ⟨x.1, x.2⟩ = H.pr0 x := rfl
  have e1 : H.prV1 ⟨x.1, x.2⟩ = H.prV1 x := rfl
  rw [e0, e1] at hL
  have ha := norm_nonneg (x : Tot W0 W1 W2)
  have hb := norm_nonneg (H.waveOp ⟨x.1, x.2⟩)
  have hc := norm_nonneg (H.toV x)
  nlinarith [sq_nonneg ‖H.d0† (H.prV1s ⟨x.1, x.2⟩)‖, sq_nonneg ‖H.d1† (H.prV2s ⟨x.1, x.2⟩)‖]

open AlgSegment in
/-- The weak form (4.8) at one time: if `w = -L z` (both in `D(L)`), then
`(w, ψ)_W + a(z, ψ) = 0` for every `ψ ∈ V` (auxiliary; the computation of
`isWeakSolution_of_isStrongSolution`). See [QuennevilleBelair2015, Thm 4.7, proof]. -/
theorem weak_identity (z w : H.domL) (hw : (w : Tot W0 W1 W2) = -H.waveOp ⟨z.1, z.2⟩)
    (ψ : H.toAlgSegment.VSp) :
    ⟪H.toAlgSegment.toW (H.toV w), H.toAlgSegment.toW ψ⟫ + H.toAlgSegment.aL (H.toV z) ψ = 0 := by
  induction ψ using VSp.induction with
  | h τ v μ =>
  change ⟪H.toAlgSegment.toW (H.toAlgSegment.mkV _ _ _), H.toAlgSegment.toW (H.toAlgSegment.mkV τ v μ)⟫
    + H.toAlgSegment.aL (H.toAlgSegment.mkV _ _ _) (H.toAlgSegment.mkV τ v μ) = 0
  rw [inner_toW_mkV, aL_mkV, toAlgSegment_a]
  have hc := congrArg (tot W0 W1 W2) hw
  rw [_root_.map_neg, tot_waveOp] at hc
  have h0 : ((H.pr0 w : H.d0.domain) : W0) = H.d0† (H.prV1s ⟨z.1, z.2⟩) := by
    rw [coe_pr0, hc]; simp
  have h1 : ((H.prV1 w : H.d1.domain) : W1) =
      -(H.d0 (H.pr0 ⟨z.1, z.2⟩) + H.d1† (H.prV2s ⟨z.1, z.2⟩)) := by
    rw [coe_prV1, hc]; simp
  have h2 : (tot W0 W1 W2 w).2.2 = H.d1 (H.prV1 ⟨z.1, z.2⟩) := by
    rw [hc]; simp
  have a0 := LinearPMap.adjoint_isFormalAdjoint H.dense0 (H.prV1s ⟨z.1, z.2⟩) τ
  have a1 := LinearPMap.adjoint_isFormalAdjoint H.dense1 (H.prV2s ⟨z.1, z.2⟩) v
  simp only [coe_prV1s, coe_prV2s] at a0 a1
  have e0 : H.pr0 ⟨z.1, z.2⟩ = H.pr0 z := rfl
  have e1 : H.prV1 ⟨z.1, z.2⟩ = H.prV1 z := rfl
  simp only [e0, e1] at h1 h2
  change ⟪((H.pr0 w : H.d0.domain) : W0), (τ : W0)⟫ + ⟪((H.prV1 w : H.d1.domain) : W1), (v : W1)⟫
    + ⟪(tot W0 W1 W2 w).2.2, μ⟫ + (-⟪((H.prV1 z : H.d1.domain) : W1), H.d0 τ⟫
      + ⟪H.d0 (H.pr0 z), (v : W1)⟫ + ⟪(tot W0 W1 W2 z).2.2, H.d1 v⟫
      - ⟪H.d1 (H.prV1 z), μ⟫) = 0
  rw [h0, h1, h2, inner_neg_left, inner_add_left, a0, a1, coe_prV1]
  ring

/-- **Existence of the exact solution required by Thm 4.14**, unconditional: for every Hilbert
complex and every `ξ₀ ∈ D(L²)` (`ξ₀ ∈ D(L)`, `L ξ₀ ∈ D(L)`), there is a weak solution
`ξ ∈ C¹([0,T]; V)` of (4.8) in the sense of `Feec.Legacy.AlgSegment.IsWeakSol` (the class used by
`Feec.Legacy.AlgSegment.semidiscrete_error_bound` and `Feec.Legacy.AlgSegment.convergence_exists`) with `ξ(0) = ξ₀`; it is the
orbit `e^{-tL} ξ₀` of the Stone group, read in `V` (the last conjunct), and it is the only
such weak solution on `[0,T]` (`AlgSegment.isWeakSol_unique`).

Thesis gap: Thm 4.14 assumes `ξ ∈ C¹([0,T]; V)` without saying for which data this holds;
`D(L²)` is a sufficient condition (the derivative `-e^{-tL} L ξ₀` is continuous in the graph
norm of `L`, which controls the `V`-norm, `norm_toV_le`). It is not claimed to be necessary:
`C¹(V)` only needs `t ↦ L ξ(t)` continuous into `V`. The thesis' Thm 4.3 regularity
`C⁰(D(L)) ∩ C¹(W)` does not by itself supply `ξ̇ ∈ C⁰(V)`: for `ξ₀ ∈ D(L)` alone it can fail
(`Feec.Legacy.FredholmCE.cxK1_exists_not_isWeakSol`, `Feec.Legacy.FredholmCE.cxK1_convergence_without_C1` in
`Feec.Legacy.ErrorEstimateDomain`).
See [QuennevilleBelair2015, §4.6, Thm 4.14]; cf. [Pazy1983, §1.2, Thm 2.4]. -/
theorem exists_isWeakSol_of_waveOp_mem (T : ℝ) (x : H.domL)
    (hx : (H.waveOp ⟨x.1, x.2⟩ : Tot W0 W1 W2) ∈ H.domL) :
    ∃ ξ ξ' : ℝ → H.toAlgSegment.VSp, ξ 0 = H.toV x ∧ H.toAlgSegment.IsWeakSol T ξ ξ' ∧
      ∀ t, ξ t = H.toV ⟨H.waveGroup.S t x, H.waveGroup.mem_domain_apply ⟨x.1, x.2⟩ t⟩ := by
  set G := H.waveGroup
  let x' : (-H.waveOp).domain := ⟨x.1, x.2⟩
  let y' : (-H.waveOp).domain := ⟨-(H.waveOp ⟨x.1, x.2⟩ : Tot W0 W1 W2), H.domL.neg_mem hx⟩
  have hxy : (-H.waveOp) x' = y' := rfl
  have hΦ : ∀ z : (-H.waveOp).domain,
      ‖H.toV z‖ ≤ 1 * (‖(z : Tot W0 W1 W2)‖ + ‖(-H.waveOp) z‖) := fun z => by
    rw [one_mul, LinearPMap.neg_apply, norm_neg]
    exact H.norm_toV_le z
  refine ⟨fun s => H.toV ⟨G.S s x', G.mem_domain_apply x' s⟩,
    fun s => H.toV ⟨G.S s y', G.mem_domain_apply y' s⟩, ?_, ⟨?_, ?_, ?_, ?_⟩, fun t => rfl⟩
  · change H.toV ⟨G.S 0 x', _⟩ = H.toV x
    congr 1
    apply Subtype.ext
    change G.S 0 (x : Tot W0 W1 W2) = x
    rw [G.map_zero]; rfl
  · exact (G.continuous_graph H.toV 1 hΦ x').continuousOn
  · exact (G.continuous_graph H.toV 1 hΦ y').continuousOn
  · exact fun t _ => (G.hasDerivAt_graph H.toV 1 hΦ x' y' hxy t).hasDerivWithinAt
  · intro t _ ψ
    refine H.weak_identity ⟨G.S t x', G.mem_domain_apply x' t⟩
      ⟨G.S t y', G.mem_domain_apply y' t⟩ ?_ ψ
    have h := G.apply_comm x' t
    rw [LinearPMap.neg_apply, hxy] at h
    exact h.symm

/-- **Convergence of the semi-discrete method (4.10)**, unconditional on the exact solution:
for every Hilbert complex, every family of finite-dimensional subcomplexes `Vₕ` satisfying the
density hypothesis, and every `ξ₀ ∈ D(L²)`, the exact weak solution `ξ ∈ C¹([0,T]; V)` with
`ξ(0) = ξ₀` exists (`exists_isWeakSol_of_waveOp_mem`) and is unique on `[0,T]`
(`AlgSegment.isWeakSol_unique`), the discrete solutions with
`ξₕ(0) = Πₕ ξ₀` exist, and `ξₕ → ξ` in `W`, uniformly on `[0,T]`.
`Feec.Legacy.AlgSegment.convergence_exists` with its hypothesis "`ξ` is a weak solution in
`C¹([0,T]; V)`" discharged by Stone's theorem.
See [QuennevilleBelair2015, §4.6, Thm 4.14 and the convergence remark after it]. -/
theorem tendstoUniformlyOn_discreteSol {ι : Type*} {l : Filter ι} {S : ι → H.toAlgSegment.Sub}
    [∀ h, FiniteDimensional ℝ (S h).toV] (hd : H.toAlgSegment.DensityHyp l S) (T : ℝ)
    (x : H.domL) (hx : (H.waveOp ⟨x.1, x.2⟩ : Tot W0 W1 W2) ∈ H.domL) :
    ∃ ξ ξ' : ℝ → H.toAlgSegment.VSp, ξ 0 = H.toV x ∧ H.toAlgSegment.IsWeakSol T ξ ξ' ∧
      (∀ ζ ζ' : ℝ → H.toAlgSegment.VSp, H.toAlgSegment.IsWeakSol T ζ ζ' → ζ 0 = H.toV x →
        EqOn ζ ξ (Icc 0 T)) ∧
      ∃ ξh ξh' : ι → ℝ → H.toAlgSegment.VSp,
        (∀ h, H.toAlgSegment.IsDiscreteSol (S h) T (ξh h) (ξh' h)) ∧
        (∀ h, ξh h 0 = H.toAlgSegment.ellProj (S h) (H.toV x)) ∧
        TendstoUniformlyOn (fun h t => H.toAlgSegment.toW (ξh h t))
          (fun t => H.toAlgSegment.toW (ξ t)) l (Icc 0 T) := by
  obtain ⟨ξ, ξ', h0, hξ, -⟩ := H.exists_isWeakSol_of_waveOp_mem T x hx
  obtain ⟨ξh, ξh', hs, hi, hc⟩ := AlgSegment.convergence_exists hd hξ
  exact ⟨ξ, ξ', h0, hξ, fun ζ ζ' hζ hζ0 => AlgSegment.isWeakSol_unique hζ hξ (hζ0.trans h0.symm),
    ξh, ξh', hs, fun h => h0 ▸ hi h, hc⟩

end HilbertComplex2

namespace Constraints

open HilbertComplex2

variable {W0 W1 W2 : Type*}
  [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
  {H : HilbertComplex2 W0 W1 W2}

variable {S1 : Submodule ℝ W1} {S2 : Submodule ℝ W2}
  [S1.HasOrthogonalProjection] [S2.HasOrthogonalProjection]

/-- **Thesis Props 4.17/4.19, abstract, with existence**, unconditional: for
`K = {0} × S1 × S2` with closed `S1 ⊆ ker d0*`, `d1 (V1 ∩ S1) ⊆ S2`, `d1* (V2* ∩ S2) ⊆ S1`, and
under the projection hypothesis `P_K D(L) ⊆ D(L)`, data `(0, E₀, B₀) ∈ D(L)` with `E₀ ∈ S1`,
`B₀ ∈ S2` have a solution of (4.14) in `C⁰([0,T]; D(L)) ∩ C¹([0,T]; W)`, unique among strong
solutions, that stays in `K`, and its `(E, B)` components solve the reduced system (4.15).
`Constraints.Kc_propagates` (which quantifies over given solutions) together with
`HilbertComplex2.existsUnique_classicalSolution_neg_waveOp`.

The projection hypothesis is not removable (`propagates_iff_projKc_mem_domL`), and it fails for
the thesis' complex on every nonempty bounded domain
(`BoundedDomain.thesisComplex_tsd_not_propagates`).
See [QuennevilleBelair2015, §4.10, Prop 4.17; §4.11, Prop 4.19]. -/
theorem existsUnique_classicalSolution_mem_Kc (hS1 : S1 ≤ H.d0†.ker)
    (hPD : ∀ x ∈ H.domL, projKc W0 S1 S2 x ∈ H.domL)
    (hd1 : ∀ u : H.d1.domain, (u : W1) ∈ S1 → H.d1 u ∈ S2)
    (hd1s : ∀ ρ : H.d1†.domain, (ρ : W2) ∈ S2 → H.d1† ρ ∈ S1) (T : ℝ) {E₀ : W1} {B₀ : W2}
    (hE₀ : E₀ ∈ S1) (hB₀ : B₀ ∈ S2) (hD : ini W0 E₀ B₀ ∈ H.domL) :
    ∃ U, IsClassicalSolution (-H.waveOp) T (ini W0 E₀ B₀) 0 U ∧
      (∀ t ∈ Icc 0 T, U t ∈ Kc W0 S1 S2) ∧
      IsReducedSolution H T E₀ B₀ (fun t => (tot W0 W1 W2 (U t)).2.1)
        (fun t => (tot W0 W1 W2 (U t)).2.2) ∧
      ∀ U', IsStrongSolution (-H.waveOp) T (ini W0 E₀ B₀) 0 U' → EqOn U' U (Icc 0 T) := by
  obtain ⟨U, hU, huniq, -⟩ := H.existsUnique_classicalSolution_neg_waveOp T hD
  obtain ⟨hK, hR⟩ := Kc_propagates hS1 hPD hd1 hd1s hE₀ hB₀ hU.toIsStrongSolution
  exact ⟨U, hU, hK, hR, huniq⟩

end Constraints

end Feec.Legacy
