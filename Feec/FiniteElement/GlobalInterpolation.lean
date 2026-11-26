module

public import Feec.FiniteElement.SmoothedProjection
public import Feec.FiniteElement.WhitneyInterpolation
public import Feec.ForMathlib.LinearPMap.Basic

/-!
# The global interpolation error in `HΛ(Ω)` and `H̊Λ(Ω)`

The finite element subcomplex approximates a `C¹` form `w` in the graph norm to within the `L²`
errors of the canonical interpolant `Π_h` on `w` and `dw` ([Arnold2018], Ch. 7).

## Main results

* `LocalElement.exists_mem_maximalSubcomplexOfEq_le`: the interpolation error in `HΛ(Ω)`.
* `LocalElement.exists_mem_minimalSubcomplexOfEq_le`: the interpolation error in `H̊Λ(Ω)`.

## References

* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public noncomputable section

open MeasureTheory Set

/-! ## Transport of subcomplexes along an equality of domains -/

namespace Feec.Domain.ConstCoeffComplex

variable {n : ℕ} (C : ConstCoeffComplex (Fin n → ℝ) ℝ)

/-- A subcomplex of the maximal complex on `Ω`, as one of the maximal complex on `Ω' = Ω`. -/
def maximalSubcomplexOfEq {Ω Ω' : Set (Fin n → ℝ)} (h : Ω = Ω') (hΩ : IsOpen Ω)
    (hΩ' : IsOpen Ω') (S : (C.maximalComplex hΩ).Subcomplex) :
    (C.maximalComplex hΩ').Subcomplex := by
  subst h; exact S

theorem finiteDimensional_maximalSubcomplexOfEq {Ω Ω' : Set (Fin n → ℝ)} (h : Ω = Ω')
    (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (S : (C.maximalComplex hΩ).Subcomplex)
    [hS : ∀ k, FiniteDimensional ℝ (S.V k)] (k : ℤ) :
    FiniteDimensional ℝ ((C.maximalSubcomplexOfEq h hΩ hΩ' S).V k) := by
  subst h; exact hS k

/-- A commuting map into `S`, transported along `Ω = Ω'`. -/
def commutingMapOfEq {Ω Ω' : Set (Fin n → ℝ)} (h : Ω = Ω') (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    {S : (C.maximalComplex hΩ).Subcomplex} (Q : S.CommutingMap) :
    (C.maximalSubcomplexOfEq h hΩ hΩ' S).CommutingMap := by
  subst h; exact Q

/-- A subcomplex of the minimal complex on `Ω`, as one of the minimal complex on `Ω' = Ω`. -/
def minimalSubcomplexOfEq {Ω Ω' : Set (Fin n → ℝ)} (h : Ω = Ω') (hΩ : IsOpen Ω)
    (hΩ' : IsOpen Ω') (S : (C.minimalComplex hΩ).Subcomplex) :
    (C.minimalComplex hΩ').Subcomplex := by
  subst h; exact S

theorem finiteDimensional_minimalSubcomplexOfEq {Ω Ω' : Set (Fin n → ℝ)} (h : Ω = Ω')
    (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (S : (C.minimalComplex hΩ).Subcomplex)
    [hS : ∀ k, FiniteDimensional ℝ (S.V k)] (k : ℤ) :
    FiniteDimensional ℝ ((C.minimalSubcomplexOfEq h hΩ hΩ' S).V k) := by
  subst h; exact hS k

/-- A commuting map into a subcomplex of the minimal complex, transported along `Ω = Ω'`. -/
def commutingMapOfEqMin {Ω Ω' : Set (Fin n → ℝ)} (h : Ω = Ω') (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    {S : (C.minimalComplex hΩ).Subcomplex} (Q : S.CommutingMap) :
    (C.minimalSubcomplexOfEq h hΩ hΩ' S).CommutingMap := by
  subst h; exact Q

theorem maximalSubcomplexOfEq_induction {Ω Ω' : Set (Fin n → ℝ)} (h : Ω = Ω') (hΩ : IsOpen Ω)
    (hΩ' : IsOpen Ω') (S : (C.maximalComplex hΩ).Subcomplex)
    (P : ∀ Θ : Set (Fin n → ℝ), ∀ hΘ : IsOpen Θ, (C.maximalComplex hΘ).Subcomplex → Prop)
    (hP : P Ω hΩ S) : P Ω' hΩ' (C.maximalSubcomplexOfEq h hΩ hΩ' S) := by
  subst h; exact hP

theorem minimalSubcomplexOfEq_induction {Ω Ω' : Set (Fin n → ℝ)} (h : Ω = Ω') (hΩ : IsOpen Ω)
    (hΩ' : IsOpen Ω') (S : (C.minimalComplex hΩ).Subcomplex)
    (P : ∀ Θ : Set (Fin n → ℝ), ∀ hΘ : IsOpen Θ, (C.minimalComplex hΘ).Subcomplex → Prop)
    (hP : P Ω hΩ S) : P Ω' hΩ' (C.minimalSubcomplexOfEq h hΩ hΩ' S) := by
  subst h; exact hP

end Feec.Domain.ConstCoeffComplex

namespace Feec.Domain

variable {n : ℕ} {Ω : Set (Fin n → ℝ)}

/-- `HΛ(Ω)`, the maximal `L²` de Rham complex of an open `Ω ⊆ ℝⁿ`. -/
abbrev maximalDeRham (hΩ : IsOpen Ω) :
    HilbertComplex ℝ (ComplexShape.up ℤ) fun k => L2F ℝ Ω (formIdx n k) :=
  (deRham ℝ n).maximalComplex hΩ

/-- `H̊Λ(Ω)`, the minimal `L²` de Rham complex of an open `Ω ⊆ ℝⁿ`. -/
abbrev minimalDeRham (hΩ : IsOpen Ω) :
    HilbertComplex ℝ (ComplexShape.up ℤ) fun k => L2F ℝ Ω (formIdx n k) :=
  (deRham ℝ n).minimalComplex hΩ

end Feec.Domain

theorem Feec.Mesh.SimplicialMesh.notMem_domain_of_mem_frontier {n : ℕ}
    (M : Feec.Mesh.SimplicialMesh n) (hΩo : IsOpen M.domain) {x : Fin n → ℝ}
    (hx : x ∈ frontier (closure M.domain)) : x ∉ M.domain := fun hxΩ =>
  hx.2 (interior_maximal subset_closure hΩo hxΩ)

namespace Feec.FiniteElement.LocalElement

open Feec.Domain Feec.Mesh Feec.ExteriorFibre

variable {n : ℕ} (E : LocalElement n) (M : SimplicialMesh n)

theorem globalInterp_mem_globalSpace₀ (k : ℕ) {w : contForms n}
    (h : ∀ x ∈ frontier (closure M.domain), (w : FormField n) x = 0) :
    (E.globalInterp M k w : E.Piecewise M k) ∈ E.globalSpace₀ M k := by
  refine ⟨(E.globalInterp M k w).2, fun T F hF hFT g hg i => ?_⟩
  rw [localDof_globalInterp _ _ _ _ _ _ (hg.trans hFT)]
  have h0 : E.dof g k i w = E.dof g k i 0 := E.dof_congr i fun x hx V _ => by
    rw [h x (hF.2.2 (convexHull_mono (Finset.coe_subset.2 hg) hx))]
    rfl
  rw [h0, map_zero]

theorem glue_globalInterp_mem_maximal [NeZero n] (hΩo : IsOpen M.domain) (k : ℕ)
    (w : c1Forms n) :
    ∃ h : E.glue M k (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w) :
        E.Piecewise M k) ∈ ((extDerivOp ℝ n k).maximal M.domain).domain,
      (extDerivOp ℝ n k).maximal M.domain ⟨_, h⟩ =
        E.glue M ((k : ℤ) + 1) (E.globalInterp M (k + 1) (extDerivC1 w) :
          E.Piecewise M (k + 1)) := by
  obtain ⟨h, hval⟩ := E.glue_mem_maximal M hΩo k
    (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w))
  refine ⟨h, hval.trans ?_⟩
  have h1 : E.dPiecewise M k (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w) :
      E.Piecewise M k) = (E.dGlobal M k (E.globalInterp M k
        (Submodule.inclusion c1Forms_le_contForms w)) : E.Piecewise M (k + 1)) := rfl
  rw [h1, ← LocalElement.globalInterp_extDeriv]

variable [NeZero n] {Ω : Set (Fin n → ℝ)} (hΩ : M.domain = Ω) (hM : IsOpen M.domain)
  (hΩo : IsOpen Ω) (hb : Bornology.IsBounded Ω)

/-- If `‖w - Π_h w‖ ≤ A` and `‖dw - Π_h dw‖ ≤ A'` in `L²` for a `C¹` `k`-form `w`, then some
`v ∈ Vₕᵏ` has `‖w - v‖ ≤ A` and `‖dw - dv‖ ≤ A'` in `HΛ(Ω)` ([Arnold2018], Ch. 7). -/
theorem exists_mem_maximalSubcomplexOfEq_le (k : ℕ) {w : FormField n} (hw : ContDiff ℝ 1 w)
    {A A' : ℝ}
    (hA : ‖formL2 hM.measurableSet M.isBounded_domain k ⟨w, hw.continuous⟩ -
      E.glue M k (E.globalInterp M k ⟨w, hw.continuous⟩ : E.Piecewise M k)‖ ≤ A)
    (hA' : ‖formL2 hM.measurableSet M.isBounded_domain (k + 1 : ℕ)
        ⟨extDeriv w, continuous_extDeriv hw⟩ -
      E.glue M (k + 1 : ℕ) (E.globalInterp M (k + 1) ⟨extDeriv w, continuous_extDeriv hw⟩ :
        E.Piecewise M (k + 1))‖ ≤ A') :
    ∃ v : L2F ℝ Ω (formIdx n k),
      v ∈ ((deRham ℝ n).maximalSubcomplexOfEq hΩ hM hΩo (E.subcomplex M hM)).V k ∧
      ‖formL2 hΩo.measurableSet hb k ⟨w, hw.continuous⟩ - v‖ ≤ A ∧
      ∃ hv : v ∈ ((maximalDeRham hΩo).d k (k + 1)).domain,
        ‖formL2 hΩo.measurableSet hb ((k : ℤ) + 1) ⟨extDeriv w, continuous_extDeriv hw⟩ -
          (maximalDeRham hΩo).d k (k + 1) ⟨v, hv⟩‖ ≤ A' := by
  subst hΩ
  set u := E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms ⟨w, hw⟩)
  obtain ⟨hmem, hval⟩ := E.glue_globalInterp_mem_maximal M hM k ⟨w, hw⟩
  have hd : (maximalDeRham hΩo).d k (k + 1) = (extDerivOp ℝ n k).maximal M.domain :=
    deRham_maximalComplex_d hΩo (k : ℤ)
  refine ⟨E.glue M k (u : E.Piecewise M k), ⟨u, rfl⟩, hA, hd ▸ hmem, ?_⟩
  rw [LinearPMap.apply_eq_of_eq' hd]
  have e : (extDerivOp ℝ n k).maximal M.domain ⟨E.glue M k (u : E.Piecewise M k), hmem⟩ =
      E.glue M (k + 1 : ℕ) (E.globalInterp M (k + 1) ⟨extDeriv w, continuous_extDeriv hw⟩ :
        E.Piecewise M (k + 1)) := hval
  erw [e]
  exact hA'

/-- If `‖w - Π_h w‖ ≤ A`, `‖dw - Π_h dw‖ ≤ A'` in `L²`, `w` vanishes outside `Ω` and `Ω` is strictly
star-shaped, then some `v ∈ V̊ₕᵏ` has `‖w - v‖ ≤ A` and `‖dw - dv‖ ≤ A'` in `H̊Λ(Ω)`. -/
theorem exists_mem_minimalSubcomplexOfEq_le (x₀ : Fin n → ℝ)
    (hstar : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₀ + t • (x - x₀) ∈ M.domain)
    (k : ℕ) {w : FormField n} (hw : ContDiff ℝ 1 w) (hsupp : ∀ x ∉ Ω, w x = 0) {A A' : ℝ}
    (hA : ‖formL2 hM.measurableSet M.isBounded_domain k ⟨w, hw.continuous⟩ -
      E.glue M k (E.globalInterp M k ⟨w, hw.continuous⟩ : E.Piecewise M k)‖ ≤ A)
    (hA' : ‖formL2 hM.measurableSet M.isBounded_domain (k + 1 : ℕ)
        ⟨extDeriv w, continuous_extDeriv hw⟩ -
      E.glue M (k + 1 : ℕ) (E.globalInterp M (k + 1) ⟨extDeriv w, continuous_extDeriv hw⟩ :
        E.Piecewise M (k + 1))‖ ≤ A') :
    ∃ v : L2F ℝ Ω (formIdx n k),
      v ∈ ((deRham ℝ n).minimalSubcomplexOfEq hΩ hM hΩo (E.subcomplexMin M hM x₀ hstar)).V k ∧
      ‖formL2 hΩo.measurableSet hb k ⟨w, hw.continuous⟩ - v‖ ≤ A ∧
      ∃ hv : v ∈ ((minimalDeRham hΩo).d k (k + 1)).domain,
        ‖formL2 hΩo.measurableSet hb ((k : ℤ) + 1) ⟨extDeriv w, continuous_extDeriv hw⟩ -
          (minimalDeRham hΩo).d k (k + 1) ⟨v, hv⟩‖ ≤ A' := by
  subst hΩ
  set u := E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms ⟨w, hw⟩)
  have hu₀ : (u : E.Piecewise M k) ∈ E.globalSpace₀ M k := E.globalInterp_mem_globalSpace₀ M k
    fun x hx => hsupp x (M.notMem_domain_of_mem_frontier hM hx)
  obtain ⟨hmem, hval⟩ := E.glue_mem_minimal M hM x₀ hstar k ⟨_, hu₀⟩
  have hd : (minimalDeRham hΩo).d k (k + 1) = (extDerivOp ℝ n k).minimal M.domain :=
    deRham_minimalComplex_d hΩo (k : ℤ)
  refine ⟨E.glue M k (u : E.Piecewise M k), ⟨⟨_, hu₀⟩, rfl⟩, hA, hd ▸ hmem, ?_⟩
  rw [LinearPMap.apply_eq_of_eq' hd]
  have h1 : E.dPiecewise M k (u : E.Piecewise M k) = (E.dGlobal M k u : E.Piecewise M (k + 1)) :=
    rfl
  have e : (extDerivOp ℝ n k).minimal M.domain ⟨E.glue M k (u : E.Piecewise M k), hmem⟩ =
      E.glue M (k + 1 : ℕ) (E.globalInterp M (k + 1) ⟨extDeriv w, continuous_extDeriv hw⟩ :
        E.Piecewise M (k + 1)) := by
    rw [hval]
    change E.glue M ((k : ℤ) + 1) (E.dPiecewise M k (u : E.Piecewise M k)) = _
    rw [h1, ← LocalElement.globalInterp_extDeriv]
    rfl
  erw [e]
  exact hA'

end Feec.FiniteElement.LocalElement
