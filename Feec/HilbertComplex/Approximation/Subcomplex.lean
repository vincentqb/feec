module

public import Feec.HilbertComplex.Hodge

/-!
# Subcomplexes of a Hilbert complex

Subcomplexes `Vₕⁱ ⊆ D(d)` with `d Vₕⁱ ⊆ Vₕʲ`. A finite-dimensional subcomplex is a Hilbert complex,
with its discrete cycles, boundaries and harmonic forms.

## Main definitions

* `Subcomplex`, `Subcomplex.toHilbertComplex`: subcomplexes, and the discrete complex.
* `Subcomplex.cyclesW`, `boundariesW`, `harmonicW`: discrete cycles, boundaries, harmonic forms.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open LinearPMap

@[expose] public noncomputable section

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 c W)

/-- A subcomplex: subspaces `Vₕⁱ ⊆ D(d i j)` with `d Vₕⁱ ⊆ Vₕʲ`. [QuennevilleBelair2015], §4.6 -/
structure Subcomplex where
  /-- the discrete spaces -/
  V : ∀ i, Submodule 𝕜 (W i)
  le_domain : ∀ i j, V i ≤ (H.d i j).domain
  mapsTo : ∀ i j (x : W i) (hx : x ∈ V i), (H.d i j ⟨x, le_domain i j hx⟩ : W j) ∈ V j

namespace Subcomplex

variable {H} (S : H.Subcomplex)

/-- The point `x ∈ Vₕⁱ` as a point of `D(d i j)`. -/
def toDomain (i j : ι) (x : S.V i) : (H.d i j).domain := ⟨x, S.le_domain i j x.2⟩

@[simp] theorem coe_toDomain (i j : ι) (x : S.V i) : (S.toDomain i j x : W i) = x := rfl

theorem toDomain_add (i j : ι) (x y : S.V i) :
    S.toDomain i j (x + y) = S.toDomain i j x + S.toDomain i j y := rfl

theorem toDomain_smul (i j : ι) (a : 𝕜) (x : S.V i) :
    S.toDomain i j (a • x) = a • S.toDomain i j x := rfl

/-- The discrete differential `Vₕⁱ → Vₕʲ` as a linear map. -/
def dLin (i j : ι) : S.V i →ₗ[𝕜] S.V j where
  toFun x := ⟨H.d i j (S.toDomain i j x), S.mapsTo i j x x.2⟩
  map_add' x y := Subtype.ext (by
    change H.d i j (S.toDomain i j (x + y)) = H.d i j (S.toDomain i j x) + H.d i j (S.toDomain i j y)
    rw [toDomain_add, LinearPMap.map_add])
  map_smul' a x := Subtype.ext (by
    change H.d i j (S.toDomain i j (a • x)) = a • H.d i j (S.toDomain i j x)
    rw [toDomain_smul, LinearPMap.map_smul])

@[simp] theorem coe_dLin_apply (i j : ι) (x : S.V i) :
    (S.dLin i j x : W j) = H.d i j (S.toDomain i j x) := rfl

theorem dLin_eq_zero_of_not_rel {i j : ι} (h : ¬ c.Rel i j) : S.dLin i j = 0 :=
  LinearMap.ext fun _ => Subtype.ext (H.apply_eq_zero_of_not_rel h _)

theorem dLin_comp_dLin (i j k : ι) (x : S.V i) : S.dLin j k (S.dLin i j x) = 0 :=
  Subtype.ext (by
    rw [coe_dLin_apply, ZeroMemClass.coe_zero]
    exact H.d_comp_d i j k (S.toDomain i j x))

/-! ### Discrete cycles, boundaries and harmonic forms in `W` -/

/-- The discrete cycles `𝔷ₕⁱ = Vₕⁱ ∩ 𝔷ⁱ`. -/
def cyclesW (i : ι) : Submodule 𝕜 (W i) := S.V i ⊓ H.cycles i

/-- The discrete boundaries `𝔅ₕⁱ = d Vₕ^{prev i}`. -/
def boundariesW (i : ι) : Submodule 𝕜 (W i) :=
  LinearMap.range ((S.V i).subtype ∘ₗ S.dLin (c.prev i) i)

/-- The discrete harmonic forms `ℌₕⁱ = 𝔷ₕⁱ ∩ (𝔅ₕⁱ)ᗮ`. -/
def harmonicW (i : ι) : Submodule 𝕜 (W i) := S.cyclesW i ⊓ (S.boundariesW i)ᗮ

theorem mem_cyclesW_iff {i : ι} {x : W i} : x ∈ S.cyclesW i ↔ x ∈ S.V i ∧ x ∈ H.cycles i :=
  Iff.rfl

theorem cyclesW_le (i : ι) : S.cyclesW i ≤ S.V i := inf_le_left

theorem cyclesW_le_cycles (i : ι) : S.cyclesW i ≤ H.cycles i := inf_le_right

theorem boundariesW_le_V (i : ι) : S.boundariesW i ≤ S.V i := by
  rintro _ ⟨y, rfl⟩; exact (S.dLin _ i y).2

theorem boundariesW_le (i : ι) : S.boundariesW i ≤ H.boundaries i := by
  rintro _ ⟨y, rfl⟩
  exact ⟨S.toDomain _ i y, rfl⟩

theorem boundariesW_le_cyclesW (i : ι) : S.boundariesW i ≤ S.cyclesW i := fun _ hx =>
  ⟨S.boundariesW_le_V i hx, H.boundaries_le_cycles i (S.boundariesW_le i hx)⟩

theorem harmonicW_le_cyclesW (i : ι) : S.harmonicW i ≤ S.cyclesW i := inf_le_left

theorem harmonicW_le_V (i : ι) : S.harmonicW i ≤ S.V i := (S.harmonicW_le_cyclesW i).trans
  (S.cyclesW_le i)

theorem mem_harmonicW_iff {i : ι} {x : W i} :
    x ∈ S.harmonicW i ↔ x ∈ S.V i ∧ x ∈ H.cycles i ∧ ∀ b ∈ S.boundariesW i, ⟪b, x⟫_𝕜 = 0 := by
  rw [harmonicW, Submodule.mem_inf, Submodule.mem_orthogonal, mem_cyclesW_iff, and_assoc]

variable [∀ i, FiniteDimensional 𝕜 (S.V i)]

/-- The discrete differential `dₕ : Vₕⁱ → Vₕʲ`, a bounded operator. -/
def dh (i j : ι) : S.V i →L[𝕜] S.V j :=
  ⟨S.dLin i j, LinearMap.continuous_of_finiteDimensional _⟩

/-- A finite-dimensional subcomplex as a Hilbert complex. [QuennevilleBelair2015], §4.6 -/
def toHilbertComplex : HilbertComplex 𝕜 c (fun i => S.V i) where
  d i j := (S.dh i j : S.V i →ₗ[𝕜] S.V j).toPMap ⊤
  shape i j h := by
    have h0 : (S.dh i j : S.V i →ₗ[𝕜] S.V j) = 0 := S.dLin_eq_zero_of_not_rel h
    rw [h0]; rfl
  dense _ _ := by simp
  closed i j := ContinuousLinearMap.isClosed_toPMap_top (S.dh i j)
  mapsTo _ _ _ _ := Submodule.mem_top
  d_comp_d i j k x := S.dLin_comp_dLin i j k x

theorem mem_cycles_iff {i : ι} {x : S.V i} :
    x ∈ S.toHilbertComplex.cycles i ↔ (x : W i) ∈ H.cycles i := by
  rw [cycles, cycles, mem_ker_iff, mem_ker_iff]
  constructor
  · rintro ⟨y, rfl, hy⟩
    refine ⟨S.toDomain i _ y, rfl, ?_⟩
    have h1 : (S.dh i (c.next i) (y : S.V i) : W (c.next i)) = 0 := by
      rw [show S.dh i (c.next i) (y : S.V i) = 0 from hy]; rfl
    exact h1
  · rintro ⟨y, hy, hy0⟩
    refine ⟨⟨x, Submodule.mem_top⟩, rfl, Subtype.ext ?_⟩
    change H.d i (c.next i) (S.toDomain i _ x) = 0
    rw [show S.toDomain i (c.next i) x = y from Subtype.ext hy]
    exact hy0

theorem mem_boundaries_iff {i : ι} {x : S.V i} :
    x ∈ S.toHilbertComplex.boundaries i ↔ (x : W i) ∈ S.boundariesW i := by
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, hy⟩
    exact ⟨⟨y, Submodule.mem_top⟩, Subtype.ext hy⟩

theorem mem_harmonic_iff {i : ι} {x : S.V i} :
    x ∈ S.toHilbertComplex.harmonic i ↔ (x : W i) ∈ S.harmonicW i := by
  rw [S.toHilbertComplex.mem_harmonic_iff, S.mem_cycles_iff, Submodule.mem_orthogonal,
    harmonicW, Submodule.mem_inf, Submodule.mem_orthogonal]
  refine ⟨fun ⟨hz, h⟩ => ⟨⟨x.2, hz⟩, fun b hb => ?_⟩,
    fun ⟨⟨_, hz⟩, h⟩ => ⟨hz, fun b hb => h _ (S.mem_boundaries_iff.1 hb)⟩⟩
  have hbV : b ∈ S.V i := S.boundariesW_le_V i hb
  exact h ⟨b, hbV⟩ (S.mem_boundaries_iff.2 hb)

instance (i : ι) : FiniteDimensional 𝕜 (S.cyclesW i) :=
  Submodule.finiteDimensional_of_le (S.cyclesW_le i)

instance (i : ι) : FiniteDimensional 𝕜 (S.harmonicW i) :=
  Submodule.finiteDimensional_of_le (S.harmonicW_le_V i)

instance (i : ι) : FiniteDimensional 𝕜 (S.boundariesW i) :=
  Submodule.finiteDimensional_of_le (S.boundariesW_le_V i)

end Subcomplex

end Feec.HilbertComplex
