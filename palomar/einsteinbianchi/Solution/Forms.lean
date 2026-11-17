module

public import Solution.Defs
public import Feec.Domain.DeRham

/-!
# The `L²` de Rham complexes of the challenge are those of `Feec`

The challenge's `L²(Ω; Λᵏ)` is `Feec`'s `L2F ℝ Ω (formIdx n k)` (`rfl`), its graphs of `d` and
of `dᵗ` on test forms are the test graphs of `Feec.Domain.extDerivOp` and of its formal adjoint
(`testGraph_eq`, `codiffGraph_eq`), so `dMin` and `dMax` are `Feec`'s minimal and maximal
realizations of the exterior derivative (`dMin_eq`, `dMax_eq`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3–§3.5, §4, §5
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 6, 7

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace ContDiff
open Filter Topology Set LinearPMap MeasureTheory Feec.Domain

@[expose] public noncomputable section

namespace FEEC

variable {n : ℕ}

theorem sgn_eq (j : Fin n) (s : Finset (Fin n)) : sgn j s = Feec.ExteriorFibre.sgn j s := rfl

/-- `(d φ')_t = (d φ)_t` when `φ'` reads the `k`-coefficients of the form field `φ`. -/
theorem extDerivOp_apply_eq {k : ℤ} (φ : FormField n) (φ' : formIdx n k → (Fin n → ℝ) → ℝ)
    (h : ∀ s x, φ' s x = φ x s.1) (t : formIdx n (k + 1)) (x : Fin n → ℝ) :
    (extDerivOp ℝ n k).apply φ' t x = extDeriv φ x t.1 := by
  rw [extDerivOp_apply]
  unfold extD extDeriv
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [formExt_of_card φ' (card_erase_of_formIdx t hj)]
  have : φ' ⟨t.1.erase j, card_erase_of_formIdx t hj⟩ = fun y => φ y (t.1.erase j) :=
    funext fun y => h _ y
  rw [this]
  rfl

/-- `(dᵗ ψ')_r = (dᵗ ψ)_r` when `ψ'` reads the `(k + 1)`-coefficients of the form field `ψ`. -/
theorem formalAdj_apply_eq {k : ℤ} (ψ : FormField n) (ψ' : formIdx n (k + 1) → (Fin n → ℝ) → ℝ)
    (h : ∀ s x, ψ' s x = ψ x s.1) (r : formIdx n k) (x : Fin n → ℝ) :
    (extDerivOp ℝ n k).formalAdj.apply ψ' r x = codiff ψ x r.1 := by
  rw [formalAdj_extDerivOp_apply]
  unfold extDAdj codiff
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ∉ r.1 := Finset.mem_compl.1 hj
  rw [formExt_of_card ψ' (card_insert_of_formIdx r hj')]
  have : ψ' ⟨insert j r.1, card_insert_of_formIdx r hj'⟩ = fun y => ψ y (insert j r.1) :=
    funext fun y => h _ y
  rw [this]
  rfl

theorem isTest_of {Ω : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ} (h : IsTestFn Ω f) : IsTest Ω f :=
  ⟨h.1, h.2.1, h.2.2⟩

theorem isTestFn_of {Ω : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ} (h : IsTest Ω f) : IsTestFn Ω f :=
  ⟨h.contDiff, h.hasCompactSupport, h.tsupport_subset⟩

/-- A family indexed by the `k`-subsets as a form field (zero off degree `k`). -/
def toField {k : ℤ} (φ' : formIdx n k → (Fin n → ℝ) → ℝ) : FormField n :=
  fun x s => formExt (fun t => φ' t x) s

theorem toField_apply {k : ℤ} (φ' : formIdx n k → (Fin n → ℝ) → ℝ) (s : formIdx n k)
    (x : Fin n → ℝ) : toField φ' x s.1 = φ' s x := formExt_val _ s

theorem isTestFn_toField {Ω : Set (Fin n → ℝ)} {k : ℤ} {φ' : formIdx n k → (Fin n → ℝ) → ℝ}
    (hφ : IsTestField Ω φ') (s : Finset (Fin n)) : IsTestFn Ω fun x => toField φ' x s := by
  by_cases hs : (s.card : ℤ) = k
  · have : (fun x => toField φ' x s) = φ' ⟨s, hs⟩ := funext fun x => formExt_of_card _ hs
    rw [this]; exact isTestFn_of (hφ _)
  · have : (fun x => toField φ' x s) = 0 := funext fun x => by simp [toField, formExt, hs]
    rw [this]; exact isTestFn_of IsTest.zero

/-- **The graph of `d` on test forms is `Feec`'s test graph of `extDerivOp`.** -/
theorem testGraph_eq (Ω : Set (Fin n → ℝ)) (k : ℤ) :
    testGraph Ω k = (extDerivOp ℝ n k).testGraph Ω := by
  unfold testGraph
  convert Submodule.span_eq ((extDerivOp ℝ n k).testGraph Ω) using 2
  ext p
  constructor
  · rintro ⟨φ, hφ, h1, h2⟩
    set φ' : formIdx n k → (Fin n → ℝ) → ℝ := fun s x => φ x s.1
    have hφ' : IsTestField Ω φ' := fun s => isTest_of (hφ s.1)
    refine ⟨φ', hφ', Prod.ext (PiLp.ext fun s => Lp.ext ?_) (PiLp.ext fun t => Lp.ext ?_)⟩
    · filter_upwards [h1 s, coeFn_testField hφ' s] with x hx hx'
      rw [hx]; exact hx'.symm
    · filter_upwards [h2 t, coeFn_testField ((extDerivOp ℝ n k).isTestField_apply hφ') t]
        with x hx hx'
      rw [hx, hx', extDerivOp_apply_eq φ φ' (fun _ _ => rfl)]
  · rintro ⟨φ', hφ', rfl⟩
    refine ⟨toField φ', isTestFn_toField hφ', fun s => ?_, fun t => ?_⟩
    · filter_upwards [coeFn_testField hφ' s] with x hx
      rw [hx, toField_apply]
    · filter_upwards [coeFn_testField ((extDerivOp ℝ n k).isTestField_apply hφ') t] with x hx
      rw [hx, extDerivOp_apply_eq (toField φ') φ' (fun s y => (toField_apply φ' s y).symm)]

/-- **The graph of `dᵗ` on test forms is `Feec`'s test graph of the formal adjoint.** -/
theorem codiffGraph_eq (Ω : Set (Fin n → ℝ)) (k : ℤ) :
    codiffGraph Ω k = (extDerivOp ℝ n k).formalAdj.testGraph Ω := by
  unfold codiffGraph
  convert Submodule.span_eq ((extDerivOp ℝ n k).formalAdj.testGraph Ω) using 2
  ext p
  constructor
  · rintro ⟨ψ, hψ, h1, h2⟩
    set ψ' : formIdx n (k + 1) → (Fin n → ℝ) → ℝ := fun s x => ψ x s.1
    have hψ' : IsTestField Ω ψ' := fun s => isTest_of (hψ s.1)
    refine ⟨ψ', hψ', Prod.ext (PiLp.ext fun s => Lp.ext ?_) (PiLp.ext fun t => Lp.ext ?_)⟩
    · filter_upwards [h1 s, coeFn_testField hψ' s] with x hx hx'
      rw [hx]; exact hx'.symm
    · filter_upwards [h2 t,
        coeFn_testField ((extDerivOp ℝ n k).formalAdj.isTestField_apply hψ') t] with x hx hx'
      rw [hx, hx', formalAdj_apply_eq ψ ψ' (fun _ _ => rfl)]
  · rintro ⟨ψ', hψ', rfl⟩
    refine ⟨toField ψ', isTestFn_toField hψ', fun s => ?_, fun t => ?_⟩
    · filter_upwards [coeFn_testField hψ' s] with x hx
      rw [hx, toField_apply]
    · filter_upwards [coeFn_testField ((extDerivOp ℝ n k).formalAdj.isTestField_apply hψ') t]
        with x hx
      rw [hx, formalAdj_apply_eq (toField ψ') ψ' (fun s y => (toField_apply ψ' s y).symm)]

/-- **`dMin` is `Feec`'s minimal exterior derivative.** -/
theorem dMin_eq (Ω : Set (Fin n → ℝ)) (k : ℤ) : dMin Ω k = (extDerivOp ℝ n k).minimal Ω := by
  unfold dMin ConstCoeffOp.minimal
  rw [testGraph_eq]

/-- **`dMax` is `Feec`'s maximal (weak) exterior derivative.** -/
theorem dMax_eq (Ω : Set (Fin n → ℝ)) (k : ℤ) : dMax Ω k = (extDerivOp ℝ n k).maximal Ω := by
  unfold dMax codiffMin ConstCoeffOp.maximal ConstCoeffOp.minimal
  rw [codiffGraph_eq]

/-- `T x = T' x` along `T = T'`. -/
theorem LinearPMap.apply_of_eq' {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] {T T' : E →ₗ.[ℝ] F} (h : T = T') (x : T.domain) :
    T x = T' ⟨x, h ▸ x.2⟩ := by
  subst h; rfl

/-- The operator `T` acting componentwise on vectors: `vecOp` of the constant family `T`. -/
abbrev vecOpC {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (T : E →ₗ.[ℝ] F) :
    PiLp 2 (fun _ : Fin n => E) →ₗ.[ℝ] PiLp 2 (fun _ : Fin n => F) :=
  FEEC.vecOp fun _ => T

end FEEC
