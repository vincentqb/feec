module

public import Feec.HilbertComplex.Short
public import Feec.ForMathlib.LinearPMap.Reducing

/-!
# The literal density hypothesis of Prop 4.17 holds in every Hilbert complex

In every Hilbert complex, `D(d j k) ∩ N((d i j)†)` is dense in `N((d i j)†)`
(`HilbertComplex.mem_closure_domain_inter_ker_adjoint`): the projection onto `N((d i j)†)`
maps `D(d j k)` into `D(d j k)`, because `N((d i j)†)ᗮ = cl R(d i j) ⊆ N(d j k)`, and it is
continuous with dense source. For the thesis' complex `H̊¹ → H̊(curl) → L²` this is the density of
`H̊(curl) ∩ H(div, 0)` in `H(div, 0)` stated in the proof of Prop 4.17, which is therefore true
on every domain (`Feec.Models.BoundedDomain.dense_curl_inter_divFree`). In a short complex,
`D(d₁) ∩ D(d₀†)`, the middle components of `D(L)`, is dense in `W₁`
(`ShortHilbertComplex.dense_domain_inf_adjoint`).

What fails is the inference drawn from it in the thesis: that `H̊(curl) ∩ L²(TSD)` is dense in
`L²(TSD)` (`Feec.Counterexamples.BoundedDomainTSD.not_dense_tsd_inter`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.10 (proof of Prop 4.17)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap

@[expose] public noncomputable section

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 c W)

/-- `P_{N((d i j)†)}` maps `D(d j k)` into itself: `u - P u ∈ N((d i j)†)ᗮ ⊆ N(d j k)`. -/
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

/-- **The literal density hypothesis holds in every Hilbert complex**: `D(d j k) ∩ N((d i j)†)`
is dense in `N((d i j)†)`. [QuennevilleBelair2015], Prop 4.17 -/
theorem mem_closure_domain_inter_ker_adjoint (i j k : ι) {v : W j} (hv : v ∈ ((H.d i j)†).ker) :
    v ∈ closure (((H.d j k).domain : Set (W j)) ∩ ((H.d i j)†).ker) := by
  have := hasOrthogonalProjection_ker _ (adjoint_isClosed (H.dense i j))
  have := map_mem_closure ((H.d i j)†).ker.starProjection.continuous (H.dense j k v)
    (t := ((H.d j k).domain : Set (W j)) ∩ ((H.d i j)†).ker) fun u hu =>
      ⟨H.starProjection_ker_adjoint_mem_domain i j k hu,
        ((H.d i j)†).ker.starProjection_apply_mem u⟩
  rwa [(((H.d i j)†).ker.starProjection_eq_self_iff).2 hv] at this

end Feec.HilbertComplex

namespace Feec.ShortHilbertComplex

universe u

variable {𝕜 : Type*} [RCLike 𝕜] {W₀ W₁ W₂ : Type u}
  [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [CompleteSpace W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [CompleteSpace W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace 𝕜 W₂] [CompleteSpace W₂]
  (S : ShortHilbertComplex 𝕜 W₀ W₁ W₂)

/-- **The literal density hypothesis of Prop 4.17** for a short complex: `D(d₁) ∩ N(d₀†)` is
dense in `N(d₀†)`. [QuennevilleBelair2015], Prop 4.17 -/
theorem mem_closure_domain_inter_ker_adjoint {v : W₁} (hv : v ∈ (S.d₀†).ker) :
    v ∈ closure ((S.d₁.domain : Set W₁) ∩ (S.d₀†).ker) :=
  S.toHilbertComplex.mem_closure_domain_inter_ker_adjoint 0 1 2 hv

/-- **`D(d₁) ∩ D(d₀†)` is dense**: it contains the middle components of the dense `D(L)`
(`Feec.HilbertComplex.dense_wave_domain`). -/
theorem dense_domain_inf_adjoint :
    Dense ((S.d₁.domain ⊓ S.d₀†.domain : Submodule 𝕜 W₁) : Set W₁) := by
  have hsurj : Function.Surjective fun x : PiLp 2 (W3 W₀ W₁ W₂) => (x 1 : W₁) := fun y =>
    ⟨WithLp.toLp 2 (Pi.single (M := W3 W₀ W₁ W₂) 1 y), rfl⟩
  refine (hsurj.denseRange.dense_image (PiLp.continuous_apply 2 _ 1)
    S.toHilbertComplex.dense_wave_domain).mono ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨-, h1, h1', -⟩ := S.mem_wave_domain.1 hx
  exact ⟨h1, h1'⟩

end Feec.ShortHilbertComplex
