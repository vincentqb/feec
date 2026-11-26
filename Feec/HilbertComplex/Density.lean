module

public import Feec.HilbertComplex.Short
public import Feec.ForMathlib.LinearPMap.Reducing

/-!
# Density of `D(d) ∩ N(d†)` in `N(d†)`

In every Hilbert complex `D(d j k) ∩ N((d i j)†)` is dense in `N((d i j)†)`, and in every finite one
`D(d j k) ∩ D((d i j)†)` is dense.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap

@[expose] public noncomputable section

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 c W)

theorem starProjection_ker_adjoint_mem_domain (i j k : ι) {u : W j}
    (hu : u ∈ (H.d j k).domain) :
    haveI := hasOrthogonalProjection_ker _ (adjoint_isClosed (H.dense i j))
    ((H.d i j)†).ker.starProjection u ∈ (H.d j k).domain := by
  have := hasOrthogonalProjection_ker _ (adjoint_isClosed (H.dense i j))
  have h1 := ((H.d i j)†).ker.sub_starProjection_mem_orthogonal u
  have h2 := (H.d j k).ker_le_domain (H.orthogonal_ker_adjoint_le_ker i j k h1)
  have e : ((H.d i j)†).ker.starProjection u = u - (u - ((H.d i j)†).ker.starProjection u) := by
    abel
  rw [e]
  exact (H.d j k).domain.sub_mem hu h2

/-- **Density in `N(d†)`**: `D(d j k) ∩ N((d i j)†)` is dense in `N((d i j)†)`.
[QuennevilleBelair2015], proof of Prop 4.17 (adapted) -/
theorem mem_closure_domain_inter_ker_adjoint (i j k : ι) {v : W j} (hv : v ∈ ((H.d i j)†).ker) :
    v ∈ closure (((H.d j k).domain : Set (W j)) ∩ ((H.d i j)†).ker) := by
  have := hasOrthogonalProjection_ker _ (adjoint_isClosed (H.dense i j))
  have := map_mem_closure ((H.d i j)†).ker.starProjection.continuous (H.dense j k v)
    (t := ((H.d j k).domain : Set (W j)) ∩ ((H.d i j)†).ker) fun u hu =>
      ⟨H.starProjection_ker_adjoint_mem_domain i j k hu,
        ((H.d i j)†).ker.starProjection_apply_mem u⟩
  rwa [(((H.d i j)†).ker.starProjection_eq_self_iff).2 hv] at this

/-- **`D(d j k) ∩ D((d i j)†)` is dense** in every finite Hilbert complex. -/
theorem dense_domain_inf_adjoint [Fintype ι] (i j k : ι) :
    Dense (((H.d j k).domain ⊓ ((H.d i j)†).domain : Submodule 𝕜 (W j)) : Set (W j)) := by
  classical
  have hsurj : Function.Surjective fun x : PiLp 2 W => x j := fun y =>
    ⟨WithLp.toLp 2 (Pi.single j y), by simp⟩
  refine (hsurj.denseRange.dense_image (PiLp.continuous_apply 2 W j)
    H.dense_wave_domain).mono ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨(H.mem_wave_domain.1 hx).1 j k, (H.mem_wave_domain.1 hx).2 i j⟩

end Feec.HilbertComplex

namespace Feec.ShortHilbertComplex

universe u

variable {𝕜 : Type*} [RCLike 𝕜] {W₀ W₁ W₂ : Type u}
  [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [CompleteSpace W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [CompleteSpace W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace 𝕜 W₂] [CompleteSpace W₂]
  (S : ShortHilbertComplex 𝕜 W₀ W₁ W₂)

/-- **Density in `N(d₀†)`** for a short complex: `D(d₁) ∩ N(d₀†)` is dense in `N(d₀†)`.
[QuennevilleBelair2015], proof of Prop 4.17 (adapted) -/
theorem mem_closure_domain_inter_ker_adjoint {v : W₁} (hv : v ∈ (S.d₀†).ker) :
    v ∈ closure ((S.d₁.domain : Set W₁) ∩ (S.d₀†).ker) :=
  S.toHilbertComplex.mem_closure_domain_inter_ker_adjoint 0 1 2 hv

theorem dense_domain_inf_adjoint :
    Dense ((S.d₁.domain ⊓ S.d₀†.domain : Submodule 𝕜 W₁) : Set W₁) :=
  S.toHilbertComplex.dense_domain_inf_adjoint 0 1 2

end Feec.ShortHilbertComplex
