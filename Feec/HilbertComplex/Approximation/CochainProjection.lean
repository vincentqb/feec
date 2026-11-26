module

public import Feec.HilbertComplex.Approximation.Subcomplex

/-!
# Cochain projections and the discrete Poincaré inequality

Cochain projections onto a subcomplex of a Hilbert complex, and the discrete Poincaré inequality
they give when bounded in `W` or in the graph norm.

## Main results

* `CochainProjection.norm_le_of_forall_inner_eq_zero`: discrete Poincaré, `π` bounded in `W`.
* `CochainProjection.norm_le_of_forall_inner_eq_zero_of_graph`: the same, graph-norm bound.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap

@[expose] public noncomputable section

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex 𝕜 c W}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace Subcomplex

variable (S : H.Subcomplex)

/-- A **cochain projection** onto `S`: linear projections `πⁱ : Wⁱ → Vₕⁱ` with `d πⁱ = πʲ d`. -/
structure CochainProjection where
  /-- the projections -/
  π : ∀ i, W i →ₗ[𝕜] W i
  mem : ∀ i x, π i x ∈ S.V i
  proj : ∀ i x, x ∈ S.V i → π i x = x
  comm : ∀ i j (x : (H.d i j).domain),
    H.d i j ⟨π i x, S.le_domain i j (mem i x)⟩ = π j (H.d i j x)

namespace CochainProjection

variable {S} (P : S.CochainProjection)

theorem mem_cyclesW {i : ι} {x : W i} (hx : x ∈ H.cycles i) : P.π i x ∈ S.cyclesW i := by
  refine S.mem_cyclesW_iff.2 ⟨P.mem i x, ?_⟩
  obtain ⟨y, rfl, hy⟩ := mem_ker_iff.1 hx
  refine mem_ker_iff.2 ⟨⟨_, S.le_domain i _ (P.mem i y)⟩, rfl, ?_⟩
  rw [P.comm, hy, _root_.map_zero]

private theorem exists_norm_le {i j : ι} (hij : c.Rel i j) {x : W i} (hx : x ∈ S.V i)
    (hxo : ∀ y ∈ S.cyclesW i, ⟪y, x⟫ = 0) :
    ∃ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ ∧
      H.d i j z = H.d i j ⟨x, S.le_domain i j hx⟩ ∧ ‖x‖ ≤ ‖P.π i z‖ := by
  set xd : (H.d i j).domain := ⟨x, S.le_domain i j hx⟩
  have hw : (H.cycles i).starProjection x ∈ (H.d i j).ker := by
    rw [← H.cycles_eq hij]; exact Submodule.starProjection_apply_mem _ _
  obtain ⟨wd, hwd, hw0⟩ := mem_ker_iff.1 hw
  set zd := xd - wd
  have hz : (zd : W i) = x - (H.cycles i).starProjection x := by
    simp only [zd, Submodule.coe_sub, hwd]; rfl
  have hdz : H.d i j zd = H.d i j xd := by
    rw [LinearPMap.map_sub, hw0, sub_zero]
  refine ⟨zd, hz ▸ Submodule.sub_starProjection_mem_orthogonal x, hdz, ?_⟩
  -- `x - π z` is a discrete cycle
  have he : x - P.π i zd ∈ S.cyclesW i := by
    refine S.mem_cyclesW_iff.2 ⟨(S.V i).sub_mem hx (P.mem i _), ?_⟩
    rw [H.cycles_eq hij]
    refine mem_ker_iff.2 ⟨xd - ⟨_, S.le_domain i j (P.mem i zd)⟩, rfl, ?_⟩
    rw [LinearPMap.map_sub, P.comm, hdz, P.proj j _ (S.mapsTo i j x hx), sub_self]
  have h0 := hxo _ he
  rw [inner_sub_left, sub_eq_zero] at h0
  have h1 : ‖x‖ ^ 2 ≤ ‖P.π i zd‖ * ‖x‖ := by
    rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), h0]
    exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  rcases (norm_nonneg x).eq_or_lt with h | h
  · rw [← h]; exact norm_nonneg _
  · exact le_of_mul_le_mul_right (by nlinarith) h

/-- **Discrete Poincaré inequality**: `‖x‖ ≤ C c_P ‖d x‖` on `Vₕⁱ ⊥ 𝔷ₕⁱ` when `‖π‖ ≤ C` in `W`
([AFW2010], Thm 3.6). -/
theorem norm_le_of_forall_inner_eq_zero {i j : ι} (hij : c.Rel i j) {cP C : ℝ}
    (hP : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    (hC : 0 ≤ C) (hπ : ∀ x, ‖P.π i x‖ ≤ C * ‖x‖) {x : W i} (hx : x ∈ S.V i)
    (hxo : ∀ y ∈ S.cyclesW i, ⟪y, x⟫ = 0) :
    ‖x‖ ≤ C * cP * ‖H.d i j ⟨x, S.le_domain i j hx⟩‖ := by
  obtain ⟨z, hzo, hdz, hle⟩ := P.exists_norm_le hij hx hxo
  calc ‖x‖ ≤ ‖P.π i z‖ := hle
    _ ≤ C * ‖(z : W i)‖ := hπ z
    _ ≤ C * (cP * ‖H.d i j z‖) := by gcongr; exact hP z hzo
    _ = _ := by rw [hdz]; ring

/-- **Discrete Poincaré inequality** for `π` bounded by `C` in the graph norm:
`‖x‖ ≤ C √(1 + c_P²) ‖d x‖` on `Vₕⁱ ⊥ 𝔷ₕⁱ`. -/
theorem norm_le_of_forall_inner_eq_zero_of_graph {i j : ι} (hij : c.Rel i j) {cP C : ℝ}
    (hP : ∀ z : (H.d i j).domain, (z : W i) ∈ (H.cycles i)ᗮ → ‖(z : W i)‖ ≤ cP * ‖H.d i j z‖)
    (hC : 0 ≤ C) (hπ : ∀ x : (H.d i j).domain, ‖P.π i x‖ ^ 2 +
      ‖H.d i j ⟨P.π i x, S.le_domain i j (P.mem i x)⟩‖ ^ 2 ≤ C ^ 2 * (‖(x : W i)‖ ^ 2 + ‖H.d i j x‖ ^ 2))
    {x : W i} (hx : x ∈ S.V i) (hxo : ∀ y ∈ S.cyclesW i, ⟪y, x⟫ = 0) :
    ‖x‖ ≤ C * √(1 + cP ^ 2) * ‖H.d i j ⟨x, S.le_domain i j hx⟩‖ := by
  obtain ⟨z, hzo, hdz, hle⟩ := P.exists_norm_le hij hx hxo
  set D := ‖H.d i j ⟨x, S.le_domain i j hx⟩‖
  have hz : ‖(z : W i)‖ ^ 2 ≤ cP ^ 2 * D ^ 2 := by
    have h1 := hP z hzo
    rw [hdz] at h1
    have := norm_nonneg (z : W i)
    nlinarith
  have hsq : ‖P.π i z‖ ^ 2 ≤ (C * √(1 + cP ^ 2) * D) ^ 2 := by
    have h2 := hπ z
    rw [hdz] at h2
    have h3 : ‖P.π i z‖ ^ 2 ≤ C ^ 2 * (cP ^ 2 * D ^ 2 + D ^ 2) := by
      nlinarith [sq_nonneg ‖H.d i j ⟨P.π i z, S.le_domain i j (P.mem i z)⟩‖, sq_nonneg C]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith
  exact hle.trans (abs_le_of_sq_le_sq' hsq (by positivity)).2

end CochainProjection

end Subcomplex

end Feec.HilbertComplex
