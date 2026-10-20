module

public import Feec.ForMathlib.LinearPMap.Reducing
public import Feec.Semigroup.Stone

/-!
# The domain of the square of an operator

For `A : E →ₗ.[𝕜] E`, `LinearPMap.domainSq A = D(A²) = {x ∈ D(A) | A x ∈ D(A)}`, a subspace of
`E`. For a skew-adjoint `A` on a Hilbert space it is dense, and dense in every reducing subspace.
It is the natural core of orbit-consistency arguments for the wave group: for `x ∈ D(A²)`, the
orbit `t ↦ e^{tA} x` is `C¹` with values in `D(A)` for the graph norm.

## Main results

* `LinearPMap.mem_domainSq`, `LinearPMap.domainSq_le_domain`.
* `LinearPMap.IsSkewAdjoint.exists_mem_domain_sq_lt`: the resolvent means `J_n = c²(c² − A²)⁻¹`
  of Stone's theorem map into `D(A²)` and converge strongly to `1`.
* `LinearPMap.IsSkewAdjoint.dense_domainSq`: `D(A²)` is dense.
* `LinearPMap.IsSkewAdjoint.subset_closure_domainSq_inf`: `D(A²) ∩ K` is dense in every reducing
  `K` (`P_K` maps `D(A²)` into `D(A²) ∩ K`).

## References

* [K.-J. Engel, R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*][EngelNagel2000],
  §II.1 (cores and powers of generators)
* [T. Cazenave, A. Haraux, *An Introduction to Semilinear Evolution Equations*][CazenaveHaraux1998],
  Cor. 2.4.9 (Stone's theorem)
-/

open Set Filter Topology

@[expose] public noncomputable section

namespace LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {A : E →ₗ.[𝕜] E}

/-- `D(A²) = {x ∈ D(A) | A x ∈ D(A)}`. -/
def domainSq (A : E →ₗ.[𝕜] E) : Submodule 𝕜 E :=
  (A.domain.comap A.toFun).map A.domain.subtype

theorem mem_domainSq {x : E} : x ∈ A.domainSq ↔ ∃ hx : x ∈ A.domain, A ⟨x, hx⟩ ∈ A.domain := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hAx⟩
    exact ⟨⟨x, hx⟩, hAx, rfl⟩

theorem domainSq_le_domain : A.domainSq ≤ A.domain := fun _ hx => (mem_domainSq.1 hx).1

/-- A reducing projection maps `D(A²)` into `D(A²)`. -/
theorem IsReducing.starProjection_mem_domainSq {K : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    (hK : A.IsReducing K) {y : E} (hy : y ∈ A.domainSq) : K.starProjection y ∈ A.domainSq := by
  obtain ⟨hy1, hy2⟩ := mem_domainSq.1 hy
  refine mem_domainSq.2 ⟨hK.proj_mem ⟨y, hy1⟩, ?_⟩
  rw [hK.comm ⟨y, hy1⟩]
  have := hK.proj_mem ⟨_, hy2⟩
  exact this

variable [CompleteSpace E]

/-- **`D(A²)` is dense** for a skew-adjoint `A`, quantitatively: the resolvent means
`J_n = c²(c² − A²)⁻¹` of Stone's theorem map into `D(A²)` and converge strongly to `1`
(`Feec.Stone.tendsto_approxJ`). -/
theorem IsSkewAdjoint.exists_mem_domain_sq_lt (hA : A.IsSkewAdjoint) (x : E) {ε : ℝ}
    (hε : 0 < ε) : ∃ (y : E) (hy : y ∈ A.domain), A ⟨y, hy⟩ ∈ A.domain ∧ ‖x - y‖ < ε := by
  obtain ⟨n, hn⟩ := ((Feec.Stone.tendsto_approxJ hA x).eventually
    (Metric.ball_mem_nhds x hε)).exists
  have hn' : ‖x - Feec.Stone.approxJ A n x‖ < ε := by
    rw [← dist_eq_norm, dist_comm]; exact hn
  set c : ℝ := Feec.Stone.scale n
  have hR1 := Feec.Stone.isResolvent_res hA (Feec.Stone.scale_ne_zero n)
  have hR2 := Feec.Stone.isResolvent_res hA (Feec.Stone.neg_scale_ne_zero n)
  set R1 := Feec.Stone.res A (Feec.Stone.scale n)
  set R2 := Feec.Stone.res A (-Feec.Stone.scale n)
  have p1 : R1 x ∈ A.domain := hR1.mem_domain x
  have p2 : R2 x ∈ A.domain := hR2.mem_domain x
  have hJ : Feec.Stone.approxJ A n x = ((c / 2 : ℝ) : 𝕜) • (R1 x - R2 x) := rfl
  have hy : Feec.Stone.approxJ A n x ∈ A.domain := by
    rw [hJ]; exact A.domain.smul_mem _ (A.domain.sub_mem p1 p2)
  refine ⟨_, hy, ?_, hn'⟩
  have e0 : (⟨Feec.Stone.approxJ A n x, hy⟩ : A.domain) =
      ((c / 2 : ℝ) : 𝕜) • ((⟨R1 x, p1⟩ : A.domain) - ⟨R2 x, p2⟩) := Subtype.ext hJ
  have e1 : A ⟨R1 x, p1⟩ = ((c : ℝ) : 𝕜) • R1 x - x := by
    have h := hR1.sub_apply x
    calc A ⟨R1 x, p1⟩ = ((c : ℝ) : 𝕜) • R1 x - (((c : ℝ) : 𝕜) • R1 x - A ⟨R1 x, p1⟩) := by
          abel
      _ = ((c : ℝ) : 𝕜) • R1 x - x := by rw [h]
  have e2 : A ⟨R2 x, p2⟩ = ((-c : ℝ) : 𝕜) • R2 x - x := by
    have h := hR2.sub_apply x
    calc A ⟨R2 x, p2⟩ = ((-c : ℝ) : 𝕜) • R2 x - (((-c : ℝ) : 𝕜) • R2 x - A ⟨R2 x, p2⟩) := by
          abel
      _ = ((-c : ℝ) : 𝕜) • R2 x - x := by rw [h]
  rw [e0, LinearPMap.map_smul, LinearPMap.map_sub, e1, e2]
  have e3 : ((c : ℝ) : 𝕜) • R1 x - x - (((-c : ℝ) : 𝕜) • R2 x - x) =
      ((c : ℝ) : 𝕜) • R1 x + ((c : ℝ) : 𝕜) • R2 x := by
    rw [RCLike.ofReal_neg, neg_smul]; abel
  rw [e3]
  exact A.domain.smul_mem _ (A.domain.add_mem (A.domain.smul_mem _ p1) (A.domain.smul_mem _ p2))

/-- **`D(A²)` is dense** for a skew-adjoint `A`. -/
theorem IsSkewAdjoint.dense_domainSq (hA : A.IsSkewAdjoint) : Dense (A.domainSq : Set E) := by
  refine Metric.dense_iff.2 fun x r hr => ?_
  obtain ⟨y, hy, hAy, hxy⟩ := hA.exists_mem_domain_sq_lt x hr
  refine ⟨y, ?_, mem_domainSq.2 ⟨hy, hAy⟩⟩
  rw [Metric.mem_ball, dist_comm, dist_eq_norm]
  exact hxy

/-- **`D(A²) ∩ K` is dense in a reducing `K`**: the projection `P_K` maps the dense `D(A²)` into
`D(A²) ∩ K` and fixes `K`. -/
theorem IsSkewAdjoint.subset_closure_domainSq_inf (hA : A.IsSkewAdjoint) {K : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] (hK : A.IsReducing K) :
    (K : Set E) ⊆ _root_.closure ((A.domainSq ⊓ K : Submodule 𝕜 E) : Set E) := by
  intro k hk
  have hP : MapsTo K.starProjection (A.domainSq : Set E) ((A.domainSq ⊓ K : Submodule 𝕜 E) :
      Set E) := fun y hy =>
    ⟨hK.starProjection_mem_domainSq hy, K.starProjection_apply_mem y⟩
  have hk' : K.starProjection k = k := (K.starProjection_eq_self_iff).2 hk
  rw [← hk']
  exact map_mem_closure K.starProjection.continuous (hA.dense_domainSq k) hP

end LinearPMap
