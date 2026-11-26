module

public import Feec.HilbertComplex.Approximation.ConformingFamily
public import Feec.HilbertComplex.Reweight

/-!
# Conforming families of a reweighted complex

For weights `a i : W i ≃L[𝕜] W' i` with uniformly bounded condition numbers, a conforming family
`Vₕ` of `H` gives the conforming family `a Vₕ` of `H.conj a`, with the projections `a πₕ a⁻¹`.

## Main definitions

* `Subcomplex.conj`, `Subcomplex.CochainProjection.conj`: the subcomplex `a Vₕ` and `a π a⁻¹`.
* `ConformingFamily.conj`: the conforming family `a Vₕ` of `H.conj a`.
* `SubcomplexFamily.Jackson.conj`: its Jackson estimate.
-/

open Filter Topology Metric

@[expose] public noncomputable section

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W W' : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace 𝕜 (W' i)]
  [∀ i, CompleteSpace (W' i)] {H : HilbertComplex 𝕜 c W} (a : ∀ i, W i ≃L[𝕜] W' i)

/-- **The image of a subcomplex** under the weights, `a Vₕ`, a subcomplex of `H.conj a`. -/
abbrev Subcomplex.conj (S : H.Subcomplex) : (H.conj a).Subcomplex where
  V i := (S.V i).map (a i : W i →ₗ[𝕜] W' i)
  le_domain i j := by
    rintro _ ⟨x, hx, rfl⟩
    exact LinearPMap.apply_mem_conj_domain.2 (S.le_domain i j hx)
  mapsTo i j := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨_, S.mapsTo i j x hx, (LinearPMap.conj_apply_apply ⟨x, S.le_domain i j hx⟩).symm⟩

/-- **The conjugated cochain projection** `a π a⁻¹` onto `a Vₕ`. -/
def Subcomplex.CochainProjection.conj {S : H.Subcomplex} (P : S.CochainProjection) :
    (S.conj a).CochainProjection where
  π i := (a i : W i →ₗ[𝕜] W' i) ∘ₗ P.π i ∘ₗ ((a i).symm : W' i →ₗ[𝕜] W i)
  mem i x := Submodule.mem_map_of_mem (P.mem i _)
  proj i := by
    rintro _ ⟨x, hx, rfl⟩
    simp [P.proj i x hx]
  comm i j x := by
    change (H.d i j).conj (a i) (a j) ⟨a i (P.π i ((a i).symm x)), _⟩ =
      a j (P.π j ((a j).symm (a j (H.d i j ⟨(a i).symm x, x.2⟩))))
    rw [LinearPMap.conj_apply_apply ⟨_, S.le_domain i j (P.mem i _)⟩,
      ContinuousLinearEquiv.symm_apply_apply]
    exact congrArg (a j) (P.comm i j ⟨(a i).symm x, x.2⟩)

theorem Subcomplex.CochainProjection.conj_π_apply {S : H.Subcomplex}
    (P : S.CochainProjection) (i : ι) (x : W' i) :
    (P.conj a).π i x = a i (P.π i ((a i).symm x)) := rfl

theorem Subcomplex.CochainProjection.norm_conj_π_le {S : H.Subcomplex} (P : S.CochainProjection)
    {i : ι} {C : ℝ} (hC : 0 ≤ C) (hP : ∀ x, ‖P.π i x‖ ≤ C * ‖x‖) (x : W' i) :
    ‖(P.conj a).π i x‖ ≤
      ‖(a i : W i →L[𝕜] W' i)‖ * ‖((a i).symm : W' i →L[𝕜] W i)‖ * C * ‖x‖ := by
  rw [conj_π_apply]
  calc ‖a i (P.π i ((a i).symm x))‖
      ≤ ‖(a i : W i →L[𝕜] W' i)‖ * (C * (‖((a i).symm : W' i →L[𝕜] W i)‖ * ‖x‖)) :=
        (a i : W i →L[𝕜] W' i).le_opNorm_of_le ((hP _).trans
          (mul_le_mul_of_nonneg_left (((a i).symm : W' i →L[𝕜] W i).le_opNorm x) hC))
    _ = _ := by ring

namespace ConformingFamily

variable {κ : Type*}

/-- The conforming family `a Vₕ` of `H.conj a`, for weights with bounded condition numbers. -/
def conj (F : ConformingFamily H κ)
    (ha : ∃ M, ∀ i, ‖(a i : W i →L[𝕜] W' i)‖ * ‖((a i).symm : W' i →L[𝕜] W i)‖ ≤ M) :
    ConformingFamily (H.conj a) κ where
  l := F.l
  V h := (F.V h).conj a
  π h := (F.π h).conj a
  bound_π := by
    obtain ⟨M, hM⟩ := ha
    refine ⟨M * F.projBound, fun h i x => ?_⟩
    have hC := zero_le_one.trans F.one_le_projBound
    refine ((F.π h).norm_conj_π_le a hC (F.norm_π_le h i) x).trans ?_
    gcongr
    exact hM i
  approx i w := by
    refine (tendsto_infDist_submodule_iff _ w).2 fun ε hε => ?_
    have hn : 0 < ‖(a i : W i →L[𝕜] W' i)‖ + 1 := by positivity
    filter_upwards [F.eventually_exists_lt i ((a i).symm w) (div_pos hε hn)] with h ⟨v, hv, hlt⟩
    refine ⟨a i v, Submodule.mem_map_of_mem hv, ?_⟩
    calc ‖w - a i v‖ = ‖(a i : W i →L[𝕜] W' i) ((a i).symm w - v)‖ := by simp
      _ ≤ ‖(a i : W i →L[𝕜] W' i)‖ * (ε / (‖(a i : W i →L[𝕜] W' i)‖ + 1)) :=
          (a i : W i →L[𝕜] W' i).le_opNorm_of_le hlt.le
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ hn]
          nlinarith

variable {a} {ha : ∃ M, ∀ i, ‖(a i : W i →L[𝕜] W' i)‖ * ‖((a i).symm : W' i →L[𝕜] W i)‖ ≤ M}

theorem norm_conj_π_le (F : ConformingFamily H κ) (h : κ) (i : ι) (x : W' i) :
    ‖((F.conj a ha).π h).π i x‖ ≤
      ‖(a i : W i →L[𝕜] W' i)‖ * ‖((a i).symm : W' i →L[𝕜] W i)‖ * F.projBound * ‖x‖ :=
  (F.π h).norm_conj_π_le a (zero_le_one.trans F.one_le_projBound) (F.norm_π_le h i) x

/-- The Jackson estimate of the reweighted family, with the constants scaled by the weights. -/
def _root_.Feec.HilbertComplex.SubcomplexFamily.Jackson.conj {F : ConformingFamily H κ} {ρ : Type*} (J : F.Jackson ρ) :
    (F.conj a ha).Jackson ρ where
  meshSize := J.meshSize
  meshSize_nonneg := J.meshSize_nonneg
  tendsto_meshSize := J.tendsto_meshSize
  Reg s i L x := J.Reg s i L ((a i).symm x)
  ord := J.ord
  B s i := max ‖(a i : W i →L[𝕜] W' i)‖ ‖(a (c.next i) : W (c.next i) →L[𝕜] W' (c.next i))‖ *
    J.B s i
  B_nonneg s i := mul_nonneg ((norm_nonneg _).trans (le_max_left _ _)) (J.B_nonneg s i)
  jackson s h i L x hL hx := by
    obtain ⟨v, hv, h1, h2⟩ := J.jackson s h i ((a i).symm x) hL hx
    have hB : 0 ≤ J.B s i * (L * J.meshSize h ^ J.ord s) :=
      (norm_nonneg _).trans h1
    refine ⟨a i v, Submodule.mem_map_of_mem hv, ?_, fun j hxj => ?_⟩
    · calc ‖x - a i v‖ = ‖(a i : W i →L[𝕜] W' i) ((a i).symm x - v)‖ := by simp
        _ ≤ ‖(a i : W i →L[𝕜] W' i)‖ * (J.B s i * (L * J.meshSize h ^ J.ord s)) :=
            (a i : W i →L[𝕜] W' i).le_opNorm_of_le h1
        _ ≤ _ := by rw [mul_assoc]; gcongr; exact le_max_left _ _
    by_cases hij : c.Rel i j
    · obtain rfl := c.next_eq' hij
      have hxj' : (a i).symm x ∈ (H.d i (c.next i)).domain := hxj
      change ‖a (c.next i) (H.d i (c.next i) ⟨(a i).symm (x - a i v), _⟩)‖ ≤ _
      calc _ ≤ ‖(a (c.next i) : W (c.next i) →L[𝕜] W' (c.next i))‖ *
              (J.B s i * (L * J.meshSize h ^ J.ord s)) :=
            (a (c.next i) : W (c.next i) →L[𝕜] W' (c.next i)).le_opNorm_of_le (by
              refine le_of_eq_of_le (congrArg norm (LinearPMap.apply_congr' _ _ _ ?_))
                (h2 (c.next i) hxj')
              simp)
        _ ≤ _ := by rw [mul_assoc]; gcongr; exact le_max_right _ _
    · rw [LinearPMap.apply_eq_zero_of_eq_zero ((H.conj a).shape i j hij), norm_zero]
      rw [mul_assoc]; exact mul_nonneg ((norm_nonneg _).trans (le_max_left _ _)) hB

end ConformingFamily

end Feec.HilbertComplex
