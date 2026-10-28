module

public import Feec.Algebra.Koszul

/-!
# Vector proxies in three dimensions

On `R³` (index type `Fin 3`), `0`-, `1`-, `2`-, `3`-forms are identified with scalar and vector
fields: `f = ω_∅`, `v_i = ω_{i}`, `u = (ω_{12}, -ω_{02}, ω_{01})`, `g = ω_{012}` (`vec1`, `vec2`,
`vol`, for coefficients in any additive group). Under these identifications the exterior
derivative is `grad`, `curl`, `div`, and the Koszul differential of polynomial forms is `x ·`,
`· × x`, `· x`:

* `vec1_coordD`, `vec2_coordD`, `vol_coordD`: `d = grad, curl, div` for the coordinate exterior
  derivative `(dω)_s = Σ_{j ∈ s} ε(j, s) ∂_j ω_{s ∖ j}` of any partial derivatives `∂_j`
  (`coordD`); the polynomial case `vec1_extDeriv`, `vec2_extDeriv`, `vol_extDeriv`, and the case
  of smooth fields on `Ω ⊆ ℝ³`, which identifies the `L²` de Rham complex with
  `H¹ → H(curl) → H(div) → L²` (`Feec.Domain.deRhamVec_maximalComplex_eq_map`) and Maxwell's
  equations with their vector form (`Feec.Instances.Maxwell.vec_maxwellFEEC`);
* `koszul_empty` (`κ v = x · v`), `vec1_koszul` (`κ u = u × x`), `vec2_koszul` (`κ g = g x`).

These are the 3D formulas of [AFW2006], §3 used for the Nédélec spaces `P_r⁻Λ¹`, `P_r⁻Λ²` in
thesis §4.10 (`P_r⁻Λ¹ = P_{r-1}³ ⊕ H_{r-1}³ × x`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.7, §4.10
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §2 (vector proxies), §3

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset MvPolynomial

@[expose] public noncomputable section

namespace Feec.Koszul.Proxy3

open ExteriorFibre

variable {R : Type*} [CommRing R]

/-- Polynomial vector fields on `R³`. -/
abbrev PolyVec (R : Type*) [CommRing R] := Fin 3 → MvPolynomial (Fin 3) R

/-- The gradient of a polynomial. -/
def grad (f : MvPolynomial (Fin 3) R) : PolyVec R := fun i => pderiv i f

/-- The curl of a polynomial vector field. -/
def curl (v : PolyVec R) : PolyVec R :=
  ![pderiv 1 (v 2) - pderiv 2 (v 1), pderiv 2 (v 0) - pderiv 0 (v 2),
    pderiv 0 (v 1) - pderiv 1 (v 0)]

/-- The divergence of a polynomial vector field. -/
def div (v : PolyVec R) : MvPolynomial (Fin 3) R := ∑ i, pderiv i (v i)

/-- The position field `x`. -/
def pos : PolyVec R := fun i => X i

/-- The cross product of polynomial vector fields. -/
def cross (u v : PolyVec R) : PolyVec R :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

/-! ### Proxies for any coefficients and any partial derivatives

The identifications `d = grad, curl, div` are the combinatorics of the formula
`(dω)_s = Σ_{j ∈ s} ε(j, s) ∂_j ω_{s ∖ j}` in three dimensions: they hold for coefficients in any
additive group `M` and any maps `∂ : Fin 3 → M → M` (`vec1_coordD`, `vec2_coordD`,
`vol_coordD`). Polynomial forms (`∂_j` the formal partial derivatives, below) and smooth
`L²` fields (`∂_j` the coordinate derivatives, `Feec.Domain.VectorProxy`) are the two
instances. -/

section Coefficients

variable {M : Type*} [AddCommGroup M] (D : Fin 3 → M → M)

/-- The coordinate exterior derivative of a family of coefficients `ω : Finset (Fin 3) → M`
for the partial derivatives `D`: `(dω)_s = Σ_{j ∈ s} ε(j, s) D_j ω_{s ∖ j}`. -/
def coordD (ω : Finset (Fin 3) → M) (s : Finset (Fin 3)) : M :=
  ∑ j ∈ s, (sgn j s : ℤ) • D j (ω (s.erase j))

/-- The gradient `(D_i f)_i`. -/
def gradOf (f : M) : Fin 3 → M := fun i => D i f

/-- The curl `(D₁ v₂ - D₂ v₁, D₂ v₀ - D₀ v₂, D₀ v₁ - D₁ v₀)`. -/
def curlOf (v : Fin 3 → M) : Fin 3 → M :=
  ![D 1 (v 2) - D 2 (v 1), D 2 (v 0) - D 0 (v 2), D 0 (v 1) - D 1 (v 0)]

/-- The divergence `Σᵢ D_i v_i`. -/
def divOf (v : Fin 3 → M) : M := ∑ i, D i (v i)

/-- The proxy of a `1`-form: `v_i = ω_{i}`. -/
def vec1 (ω : Finset (Fin 3) → M) : Fin 3 → M := fun i => ω {i}

/-- The proxy of a `2`-form: `u = (ω_{12}, -ω_{02}, ω_{01})`. -/
def vec2 (ω : Finset (Fin 3) → M) : Fin 3 → M := ![ω {1, 2}, -ω {0, 2}, ω {0, 1}]

/-- The proxy of a `3`-form: `g = ω_{012}`. -/
def vol (ω : Finset (Fin 3) → M) : M := ω {0, 1, 2}

/-- The sign of the proxy of a `2`-form: `u = (ω_{12}, -ω_{02}, ω_{01})`. -/
def vec2Sign (k : Fin 3) : ℤ := if k = 1 then -1 else 1

theorem vec2Sign_mul_self (k : Fin 3) : vec2Sign k * vec2Sign k = 1 := by
  unfold vec2Sign; split_ifs <;> rfl

/-- The proxy of a `2`-form is the signed complement: `vec2 w k = ±w_{{k}ᶜ}`. -/
theorem vec2_apply (w : Finset (Fin 3) → M) (k : Fin 3) :
    vec2 w k = vec2Sign k • w {k}ᶜ := by
  fin_cases k <;> simp [vec2, vec2Sign] <;> rfl

/-- `d = grad` on `0`-forms, for any partial derivatives. [AFW2006], §2 -/
theorem vec1_coordD (ω : Finset (Fin 3) → M) : vec1 (coordD D ω) = gradOf D (ω ∅) := by
  funext i
  simp [vec1, gradOf, coordD, sgn, Finset.filter_singleton]

/-- `d = curl` on `1`-forms, for any partial derivatives. [AFW2006], §2 -/
theorem vec2_coordD (ω : Finset (Fin 3) → M) : vec2 (coordD D ω) = curlOf D (vec1 ω) := by
  funext i
  fin_cases i <;> simp [vec2, vec1, curlOf, coordD, sgn, Finset.filter_insert,
    Finset.filter_singleton, Finset.erase_insert_eq_erase, Finset.erase_insert_of_ne,
    Finset.erase_singleton] <;> abel

/-- `d = div` on `2`-forms, for partial derivatives commuting with `-`. [AFW2006], §2 -/
theorem vol_coordD (hD : ∀ j m, D j (-m) = -D j m) (ω : Finset (Fin 3) → M) :
    vol (coordD D ω) = divOf D (vec2 ω) := by
  simp [vol, vec2, divOf, Fin.sum_univ_three, coordD, sgn, Finset.filter_insert,
    Finset.filter_singleton, Finset.erase_insert_eq_erase, Finset.erase_insert_of_ne,
    Finset.erase_singleton, hD]
  abel

end Coefficients

/-! ### Polynomial forms -/

/-- The exterior derivative of polynomial forms is the coordinate exterior derivative of the
formal partial derivatives. -/
theorem extDeriv_eq_coordD (ω : PolyForm R (Fin 3)) :
    extDeriv ω = coordD (fun j => ⇑(pderiv j)) ω := by
  funext s
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [zsmul_eq_mul, sgn, sgn]
  push_cast
  rfl

/-- `d = grad` on `0`-forms. [QuennevilleBelair2015], §4.10 -/
theorem vec1_extDeriv (ω : PolyForm R (Fin 3)) : vec1 (extDeriv ω) = grad (ω ∅) := by
  rw [extDeriv_eq_coordD, vec1_coordD]; rfl

/-- `d = curl` on `1`-forms. [QuennevilleBelair2015], §4.10 -/
theorem vec2_extDeriv (ω : PolyForm R (Fin 3)) : vec2 (extDeriv ω) = curl (vec1 ω) := by
  rw [extDeriv_eq_coordD, vec2_coordD]; rfl

/-- `d = div` on `2`-forms. [QuennevilleBelair2015], §4.10 -/
theorem vol_extDeriv (ω : PolyForm R (Fin 3)) : vol (extDeriv ω) = div (vec2 ω) := by
  rw [extDeriv_eq_coordD, vol_coordD _ fun j m => (pderiv j).toLinearMap.map_neg m]; rfl

private theorem compl_0 : ({0} : Finset (Fin 3))ᶜ = {1, 2} := by decide
private theorem compl_1 : ({1} : Finset (Fin 3))ᶜ = {0, 2} := by decide
private theorem compl_2 : ({2} : Finset (Fin 3))ᶜ = {0, 1} := by decide
private theorem compl_12 : ({1, 2} : Finset (Fin 3))ᶜ = {0} := by decide
private theorem compl_02 : ({0, 2} : Finset (Fin 3))ᶜ = {1} := by decide
private theorem compl_01 : ({0, 1} : Finset (Fin 3))ᶜ = {2} := by decide
private theorem ins_10 : (insert 1 {0} : Finset (Fin 3)) = {0, 1} := by decide
private theorem ins_20 : (insert 2 {0} : Finset (Fin 3)) = {0, 2} := by decide
private theorem ins_21 : (insert 2 {1} : Finset (Fin 3)) = {1, 2} := by decide
private theorem ins_0_12 : (insert 0 {1, 2} : Finset (Fin 3)) = {0, 1, 2} := by decide
private theorem ins_1_02 : (insert 1 {0, 2} : Finset (Fin 3)) = {0, 1, 2} := by decide
private theorem ins_2_01 : (insert 2 {0, 1} : Finset (Fin 3)) = {0, 1, 2} := by decide

/-- `κ = x ·` on `1`-forms. [QuennevilleBelair2015], §4.10 -/
theorem koszul_empty (ω : PolyForm R (Fin 3)) : koszul ω ∅ = ∑ i, pos i * vec1 ω i := by
  simp [koszul_apply, pos, vec1, Fin.sum_univ_three, sgn]

/-- `κ = · × x` on `2`-forms. [QuennevilleBelair2015], §4.10 -/
theorem vec1_koszul (ω : PolyForm R (Fin 3)) : vec1 (koszul ω) = cross (vec2 ω) pos := by
  funext i
  fin_cases i <;> simp [vec1, vec2, cross, pos, koszul_apply, compl_0, compl_1, compl_2, sgn,
    Finset.filter_singleton, ins_10, ins_20, ins_21] <;> ring

/-- `κ = · x` on `3`-forms. [QuennevilleBelair2015], §4.10 -/
theorem vec2_koszul (ω : PolyForm R (Fin 3)) : vec2 (koszul ω) = fun i => vol ω * pos i := by
  funext i
  fin_cases i
  · show koszul ω {1, 2} = ω {0, 1, 2} * X 0
    rw [koszul_apply, compl_12, sum_singleton, ins_0_12]
    simp [sgn, Finset.filter_insert, Finset.filter_singleton, mul_comm]
  · show -koszul ω {0, 2} = ω {0, 1, 2} * X 1
    rw [koszul_apply, compl_02, sum_singleton, ins_1_02]
    simp [sgn, Finset.filter_insert, Finset.filter_singleton, mul_comm]
  · show koszul ω {0, 1} = ω {0, 1, 2} * X 2
    rw [koszul_apply, compl_01, sum_singleton, ins_2_01]
    simp [sgn, Finset.filter_insert, Finset.filter_singleton, mul_comm]

end Feec.Koszul.Proxy3
