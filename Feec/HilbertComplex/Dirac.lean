module

public import Feec.HilbertComplex.Window

/-!
# The Dirac operator `d + d†` and the wave operator `d − d†`

For a closed densely defined `T` with `T T = 0`, `T − T†` on `D(T) ∩ D(T†)` is skew-adjoint; for the
total differential of a finite Hilbert complex this is the wave operator `L = 𝐝 − 𝐝*`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap Set

@[expose] public noncomputable section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem orthogonal_le_topologicalClosure_of_dense (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    {D : Set E} (hD : Dense D) (M : Submodule 𝕜 E)
    (hM : ∀ v ∈ D, v - K.starProjection v ∈ M) : Kᗮ ≤ M.topologicalClosure := by
  intro k hk
  set Q : E →L[𝕜] E := ContinuousLinearMap.id 𝕜 E - K.starProjection
  have hQk : Q k = k := by
    simp [Q, (Submodule.starProjection_apply_eq_zero_iff K).2 hk]
  have : Q k ∈ closure (Q '' D) := by
    apply image_closure_subset_closure_image Q.continuous
    exact ⟨k, hD.closure_eq ▸ mem_univ k, rfl⟩
  rw [hQk] at this
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  refine closure_mono ?_ this
  rintro _ ⟨v, hv, rfl⟩
  exact hM v hv

end Submodule

namespace LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] {T : E →ₗ.[𝕜] E}

section Nilpotent

variable (hT : Dense (T.domain : Set E)) (hc : T.IsClosed)
  (hmaps : ∀ x : T.domain, (T x : E) ∈ T.domain) (hcomp : ∀ x : T.domain, T ⟨T x, hmaps x⟩ = 0)
include hT hc hcomp

theorem dense_domain_inf_adjoint : Dense ((T.domain ⊓ T†.domain : Submodule 𝕜 E) : Set E) := by
  have ha : T.kerᗮ ≤ T†.ker := Feec.Operator.orthogonal_ker_le_ker_adjoint hT hmaps hcomp
  have hb : T†.kerᗮ ≤ T.ker := Feec.Operator.orthogonal_ker_adjoint_le_ker hT hc hmaps hcomp
  set M := T.domain ⊓ T†.domain
  have : CompleteSpace T†.ker := (isClosed_ker (adjoint_isClosed hT)).completeSpace_coe
  have : CompleteSpace T.ker := (isClosed_ker hc).completeSpace_coe
  set K := T†.kerᗮ
  have hK : Kᗮ = T†.ker := Submodule.orthogonal_orthogonal _
  set K' := T.kerᗮ
  have hK' : K'ᗮ = T.ker := Submodule.orthogonal_orthogonal _
  have h1 : T†.ker ≤ M.topologicalClosure := by
    rw [← hK]
    refine Submodule.orthogonal_le_topologicalClosure_of_dense K hT M fun v hv => ?_
    have hP : K.starProjection v ∈ T.domain := T.ker_le_domain (hb (K.starProjection_apply_mem v))
    have hQ : v - K.starProjection v ∈ Kᗮ := K.sub_starProjection_mem_orthogonal v
    rw [hK] at hQ
    exact Submodule.mem_inf.2 ⟨T.domain.sub_mem hv hP, T†.ker_le_domain hQ⟩
  have h2 : T.ker ≤ M.topologicalClosure := by
    rw [← hK']
    refine Submodule.orthogonal_le_topologicalClosure_of_dense K'
      (dense_adjoint_domain T hT hc) M fun w hw => ?_
    have hP : K'.starProjection w ∈ T†.domain :=
      T†.ker_le_domain (ha (K'.starProjection_apply_mem w))
    have hQ : w - K'.starProjection w ∈ K'ᗮ := K'.sub_starProjection_mem_orthogonal w
    rw [hK'] at hQ
    exact Submodule.mem_inf.2 ⟨T.ker_le_domain hQ, T†.domain.sub_mem hw hP⟩
  rw [Submodule.dense_iff_topologicalClosure_eq_top, eq_top_iff]
  calc (⊤ : Submodule 𝕜 E) = K ⊔ Kᗮ := Submodule.sup_orthogonal_of_hasOrthogonalProjection.symm
    _ ≤ M.topologicalClosure := sup_le (hb.trans h2) (hK ▸ h1)

theorem mem_domain_inf_adjoint_of_inner {s : 𝕜} (hs : s ≠ 0) {x z : E}
    (h : ∀ v : (T.domain ⊓ T†.domain : Submodule 𝕜 E),
      ⟪z, (v : E)⟫_𝕜 = ⟪x, T ⟨v, v.2.1⟩⟫_𝕜 + s * ⟪x, T† ⟨v, v.2.2⟩⟫_𝕜) :
    x ∈ T.domain ⊓ T†.domain := by
  have ha : T.kerᗮ ≤ T†.ker := Feec.Operator.orthogonal_ker_le_ker_adjoint hT hmaps hcomp
  have hb : T†.kerᗮ ≤ T.ker := Feec.Operator.orthogonal_ker_adjoint_le_ker hT hc hmaps hcomp
  have : CompleteSpace T†.ker := (isClosed_ker (adjoint_isClosed hT)).completeSpace_coe
  have : CompleteSpace T.ker := (isClosed_ker hc).completeSpace_coe
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · -- `x ∈ D(T)` via `T†† = T`, projecting onto `N(T)ᗮ ⊆ N(T†)`
    set K' := T.kerᗮ
    have hK' : K'ᗮ = T.ker := Submodule.orthogonal_orthogonal _
    have hg : (x, (starRingEnd 𝕜 s⁻¹) • (z - K'.starProjection z)) ∈ T.graph := by
      rw [mem_graph_iff_of_isClosed hT hc]
      intro u
      have hp : K'.starProjection (u : E) ∈ T†.ker := ha (K'.starProjection_apply_mem _)
      set p : T†.domain := ⟨_, T†.ker_le_domain hp⟩
      set q := u - p
      have hq : (q : E) ∈ T.ker := by rw [← hK']; exact K'.sub_starProjection_mem_orthogonal _
      have hTq : T† q = T† u := by
        rw [LinearPMap.map_sub, (coe_mem_ker_iff (x := p)).1 hp, sub_zero]
      have hq' : (q : E) ∈ T.domain ⊓ T†.domain := ⟨T.ker_le_domain hq, q.2⟩
      have e := h ⟨q, hq'⟩
      rw [(coe_mem_ker_iff (x := ⟨(q : E), hq'.1⟩)).1 hq, inner_zero_right, zero_add,
        show T† ⟨(q : E), hq'.2⟩ = T† u from hTq] at e
      have e' : ⟪x, T† u⟫_𝕜 = s⁻¹ * ⟪z - K'.starProjection z, (u : E)⟫_𝕜 := by
        rw [inner_sub_left, Submodule.inner_starProjection_left_eq_right, ← inner_sub_right]
        change _ = s⁻¹ * ⟪z, (q : E)⟫_𝕜
        rw [e, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
      rw [← inner_conj_symm, e', map_mul, inner_conj_symm, inner_smul_right]
    exact mem_domain_of_mem_graph hg
  · -- `x ∈ D(T†)`, projecting onto `N(T†)ᗮ ⊆ N(T)`
    set K := T†.kerᗮ
    have hK : Kᗮ = T†.ker := Submodule.orthogonal_orthogonal _
    refine mem_adjoint_domain_of_exists x ⟨z - K.starProjection z, fun v => ?_⟩
    have hp : K.starProjection (v : E) ∈ T.ker := hb (K.starProjection_apply_mem _)
    set p : T.domain := ⟨_, T.ker_le_domain hp⟩
    set q := v - p
    have hq : (q : E) ∈ T†.ker := by rw [← hK]; exact K.sub_starProjection_mem_orthogonal _
    have hTq : T q = T v := by rw [LinearPMap.map_sub, (coe_mem_ker_iff (x := p)).1 hp, sub_zero]
    have hq' : (q : E) ∈ T.domain ⊓ T†.domain := ⟨q.2, T†.ker_le_domain hq⟩
    have e := h ⟨q, hq'⟩
    rw [(coe_mem_ker_iff (x := ⟨(q : E), hq'.2⟩)).1 hq, inner_zero_right, mul_zero, add_zero,
      show T ⟨(q : E), hq'.1⟩ = T v from hTq] at e
    rw [← e, inner_sub_left, Submodule.inner_starProjection_left_eq_right, ← inner_sub_right]
    rfl

/-- `T − T†` is skew-adjoint for closed densely defined `T` with `T T = 0`. -/
theorem isSkewAdjoint_sub_adjoint : (T - T†).IsSkewAdjoint := by
  have hD : Dense ((T - T†).domain : Set E) := dense_domain_inf_adjoint hT hc hmaps hcomp
  refine (isSkewAdjoint_iff hD).2 ⟨fun x y => ?_, fun x hx => ?_⟩
  · rw [sub_apply, sub_apply, inner_sub_left, inner_sub_right]
    have h1 := adjoint_isFormalAdjoint hT ⟨y, y.2.2⟩ ⟨x, x.2.1⟩
    have h2 := adjoint_isFormalAdjoint hT ⟨x, x.2.2⟩ ⟨y, y.2.1⟩
    have h3 : ⟪T ⟨x, x.2.1⟩, (y : E)⟫_𝕜 = ⟪(x : E), T† ⟨y, y.2.2⟩⟫_𝕜 := by
      rw [← inner_conj_symm, ← h1, inner_conj_symm]
    rw [h3, h2]; ring
  · have key := adjoint_isFormalAdjoint hD ⟨x, hx⟩
    refine mem_domain_inf_adjoint_of_inner hT hc hmaps hcomp (s := -1) (by norm_num)
      (z := (T - T†)† ⟨x, hx⟩) fun v => ?_
    rw [key v, sub_apply, inner_sub_right]; ring

end Nilpotent

end LinearPMap

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 c W) [Fintype ι]

/-- The Dirac operator `D = 𝐝 + 𝐝*` of a finite Hilbert complex, on `PiLp 2 W`. -/
def dirac : PiLp 2 W →ₗ.[𝕜] PiLp 2 W := H.totalD + H.dual.totalD

/-- The wave operator `L = 𝐝 − 𝐝*` of a finite Hilbert complex. [QuennevilleBelair2015], (4.5) -/
def wave : PiLp 2 W →ₗ.[𝕜] PiLp 2 W := H.totalD - H.dual.totalD

theorem wave_eq : H.wave = H.totalD - H.totalD† := by rw [adjoint_totalD]; rfl

theorem mem_wave_domain {x : PiLp 2 W} : x ∈ H.wave.domain ↔
    (∀ i j, x i ∈ (H.d i j).domain) ∧ ∀ i j, x j ∈ ((H.d i j)†).domain :=
  ⟨fun h => ⟨h.1, fun i j => h.2 j i⟩, fun h => ⟨h.1, fun j i => h.2 i j⟩⟩

theorem wave_apply (x : H.wave.domain) (j : ι) :
    (H.wave x) j = ∑ i, H.d i j ⟨(x : PiLp 2 W) i, x.2.1 i j⟩ -
      ∑ k, (H.d j k)† ⟨(x : PiLp 2 W) k, x.2.2 k j⟩ := by
  exact congrArg₂ (fun a b => a - b) (H.totalD_apply ⟨x, x.2.1⟩ j)
    (H.dual.totalD_apply ⟨x, x.2.2⟩ j)

theorem dense_wave_domain : Dense (H.wave.domain : Set (PiLp 2 W)) := by
  rw [wave_eq]
  exact dense_domain_inf_adjoint H.dense_totalDomain H.isClosed_totalD H.totalD_mapsTo
    H.totalD_comp_totalD

/-- **The wave operator of every finite Hilbert complex is skew-adjoint**, `L† = -L`.
[QuennevilleBelair2015], Thm 4.6 (adapted) -/
theorem isSkewAdjoint_wave : H.wave.IsSkewAdjoint := by
  rw [wave_eq]
  exact isSkewAdjoint_sub_adjoint H.dense_totalDomain H.isClosed_totalD H.totalD_mapsTo
    H.totalD_comp_totalD

/-! ### Window complexes `W₀ → W₁ → W₂` -/

section Fin3

variable {W : Fin 3 → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)]
  [∀ i, CompleteSpace (W i)] (H : HilbertComplex 𝕜 ComplexShape.fin3 W)

theorem wave_apply_fin3_zero (x : H.wave.domain) :
    (H.wave x) 0 = -(H.d 0 1)† ⟨(x : PiLp 2 W) 1, x.2.2 1 0⟩ := by
  rw [wave_apply, Fin.sum_univ_three, Fin.sum_univ_three,
    H.apply_eq_zero_of_not_rel (i := 0) (j := 0) (by simp),
    H.apply_eq_zero_of_not_rel (i := 1) (j := 0) (by simp),
    H.apply_eq_zero_of_not_rel (i := 2) (j := 0) (by simp),
    adjoint_apply_eq_zero_of_eq_zero (H.shape 0 0 (by simp)),
    adjoint_apply_eq_zero_of_eq_zero (H.shape 0 2 (by simp))]
  simp

theorem wave_apply_fin3_one (x : H.wave.domain) :
    (H.wave x) 1 = H.d 0 1 ⟨(x : PiLp 2 W) 0, x.2.1 0 1⟩ -
      (H.d 1 2)† ⟨(x : PiLp 2 W) 2, x.2.2 2 1⟩ := by
  rw [wave_apply, Fin.sum_univ_three, Fin.sum_univ_three,
    H.apply_eq_zero_of_not_rel (i := 1) (j := 1) (by simp),
    H.apply_eq_zero_of_not_rel (i := 2) (j := 1) (by simp),
    adjoint_apply_eq_zero_of_eq_zero (H.shape 1 0 (by simp)),
    adjoint_apply_eq_zero_of_eq_zero (H.shape 1 1 (by simp))]
  simp

theorem wave_apply_fin3_two (x : H.wave.domain) :
    (H.wave x) 2 = H.d 1 2 ⟨(x : PiLp 2 W) 1, x.2.1 1 2⟩ := by
  rw [wave_apply, Fin.sum_univ_three, Fin.sum_univ_three,
    H.apply_eq_zero_of_not_rel (i := 0) (j := 2) (by simp),
    H.apply_eq_zero_of_not_rel (i := 2) (j := 2) (by simp),
    adjoint_apply_eq_zero_of_eq_zero (H.shape 2 0 (by simp)),
    adjoint_apply_eq_zero_of_eq_zero (H.shape 2 1 (by simp)),
    adjoint_apply_eq_zero_of_eq_zero (H.shape 2 2 (by simp))]
  simp

theorem mem_wave_domain_fin3 {x : PiLp 2 W} (h0 : x 0 ∈ (H.d 0 1).domain)
    (h1 : x 1 ∈ (H.d 1 2).domain) (h1' : x 1 ∈ ((H.d 0 1)†).domain)
    (h2 : x 2 ∈ ((H.d 1 2)†).domain) : x ∈ H.wave.domain := by
  have htop : ∀ {i j : Fin 3}, ¬ ComplexShape.fin3.Rel i j → ∀ v, v ∈ (H.d i j).domain :=
    fun h v => H.domain_eq_top_of_not_rel h ▸ Submodule.mem_top
  have htop' : ∀ {i j : Fin 3}, ¬ ComplexShape.fin3.Rel i j → ∀ v, v ∈ ((H.d i j)†).domain :=
    fun h v => by rw [H.shape _ _ h, adjoint_zero]; exact Submodule.mem_top
  refine (mem_wave_domain _).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact htop (by simp) _
    · exact h0
    · exact htop (by simp) _
    · exact htop (by simp) _
    · exact htop (by simp) _
    · exact h1
    · exact htop (by simp) _
    · exact htop (by simp) _
    · exact htop (by simp) _
  · fin_cases i <;> fin_cases j
    · exact htop' (by simp) _
    · exact h1'
    · exact htop' (by simp) _
    · exact htop' (by simp) _
    · exact htop' (by simp) _
    · exact h2
    · exact htop' (by simp) _
    · exact htop' (by simp) _
    · exact htop' (by simp) _

end Fin3

end Feec.HilbertComplex
