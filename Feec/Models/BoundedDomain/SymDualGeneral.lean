module

public import Feec.Models.BoundedDomain.SymCurl
public import Feec.Domain.Affine

/-!
# The complex (4.16), its dual and `L²(TSD)` under affine changes of variables

Let `T x = a x + b` (`a ≠ 0`), `Ω' ⊆ ℝ³` open and `Ω = T⁻¹ Ω'`. The pull-back `P u = u ∘ T`
(`Feec.Domain.pullF`) maps symmetric fields to symmetric fields and trace-free fields to
trace-free fields, so it restricts to scaled unitaries `L²(Ω'; S) ≃ L²(Ω; S)` (`pullSym`),
`L²(Ω'; T) ≃ L²(Ω; T)` (`pullTr`) and `L²(Ω') ≃ L²(Ω)` (`pullL`), all with
`⟪P u, P v⟫ = |a|⁻³ ⟪u, v⟫`. By the chain rule for the constrained realizations
(`Feec.Domain.ConstCoeffOp.minimalVia_pull`), `sym curl` (order one) and `div div` (order two)
transport with the factors `a` and `a²`:

* `symCurlDivDiv_d₀_pull`, `symCurlDivDiv_d₁_pull`: the complex
  `H̊(sym curl, T) → H̊(div div, S) → L²` on `Ω` is the conjugate of the one on `Ω'`;
* `hessCurlMax_d₀_pull`, `hessCurlMax_d₁_pull` (by duality, `LinearPMap.adjoint_conjScaled`):
  so is the complex (4.16) with the boundary conditions printed in Prop 4.19,
  `H² → H(curl, S) → L²(T)`, with its adjoints (`adjoint_hessCurlMax_d₀_pull`,
  `adjoint_hessCurlMax_d₁_pull`);
* `pullF_mem_tsd_iff`, `pullSym_mem_tsdS_iff`, `pullTr_mem_tsdT_iff`: `L²(TSD)` is invariant
  (the weak divergence transports with the factor `a`).

The wave operator of (4.16) is **not** conjugate to a multiple of the one on `Ω'` (the orders
`2` and `1` of its differentials differ, so no rescaling of time absorbs both factors); these
statements transport the individual operators and suffice for the boundary obstructions of
`Feec.Counterexamples.EveryBallSymTSD`.

## Main results

* `pullSym`, `pullTr`, `pullL` and `inner_pullSym`, `inner_pullTr`, `inner_pullL`.
* **`hessCurlMax_d₁_pull`**, **`adjoint_hessCurlMax_d₀_pull`**,
  **`adjoint_hessCurlMax_d₁_pull`**, **`pullF_mem_tsd_iff`**.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.11 ((4.16)–(4.18), Prop 4.19)
* [H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*][Brezis2011],
  §9.2 (change of variables in Sobolev spaces)
-/

@[expose] public noncomputable section

open scoped InnerProductSpace LinearPMap
open Set MeasureTheory Feec.Domain

namespace Feec.Models.BoundedDomain

/-! ### Operators of order one and two -/

theorem isHomogeneous_symCurlOp {𝕜 : Type*} [RCLike 𝕜] :
    (symCurlOp : ConstCoeffOp R3 𝕜 Ix Ix).IsHomogeneous 1 := by
  intro j i t ht
  simp only [symCurlOp, ConstCoeffOp.postComp, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨k, -, t', ht', rfl⟩ := ht
  simp only [curlOp] at ht'
  split_ifs at ht' <;> simp_all

theorem isHomogeneous_divdivOp {𝕜 : Type*} [RCLike 𝕜] :
    (divdivOp 3 : ConstCoeffOp R3 𝕜 Ix Unit).IsHomogeneous 2 := by
  intro j i t ht
  simp only [divdivOp, List.mem_singleton] at ht
  subst ht; rfl

theorem isHomogeneous_gradOp33 {𝕜 : Type*} [RCLike 𝕜] :
    (gradOp 3 3 : ConstCoeffOp R3 𝕜 (Fin 3) Ix).IsHomogeneous 1 := by
  intro j i t ht
  simp only [gradOp] at ht
  split_ifs at ht <;> simp_all

/-! ### The pull-backs -/

/-- An isomorphism mapping `S` into `T` with inverse mapping `T` into `S` restricts to `S ≃ T`. -/
def restrictCLE {𝕜 X Y : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (e : X ≃L[𝕜] Y) (S : Submodule 𝕜 X)
    (T : Submodule 𝕜 Y) (h₁ : ∀ x ∈ S, e x ∈ T) (h₂ : ∀ y ∈ T, e.symm y ∈ S) : S ≃L[𝕜] T where
  toFun x := ⟨e x.1, h₁ x.1 x.2⟩
  invFun y := ⟨e.symm y.1, h₂ y.1 y.2⟩
  map_add' x y := Subtype.ext (_root_.map_add e x.1 y.1)
  map_smul' c x := Subtype.ext (_root_.map_smul e c x.1)
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

section Pull

variable {𝕜 : Type*} [RCLike 𝕜] {a : ℝ} (ha : a ≠ 0) (b : R3) {Ω Ω' : Set R3}
  (hΩ' : IsOpen Ω') (hT : aff a b ⁻¹' Ω' = Ω)
include ha hΩ' hT

omit ha in
theorem isOpen_of_aff : IsOpen Ω := hT ▸ hΩ'.preimage (continuous_aff a b)

/-- `P` on matrix fields. -/
abbrev pullM : L2F 𝕜 Ω' Ix ≃L[𝕜] L2F 𝕜 Ω Ix := pullF ha b hΩ'.measurableSet hT Ix

theorem pullM_apply (u : L2F 𝕜 Ω' Ix) (ij : Ix) :
    pullM ha b hΩ' hT u ij = pull ha b hΩ'.measurableSet hT (u ij) := rfl

theorem pullM_symm_apply (u : L2F 𝕜 Ω Ix) (ij : Ix) :
    (pullM ha b hΩ' hT).symm u ij = pull (inv_ne_zero ha) (-(a⁻¹ • b))
      (measurableSet_of_aff b hΩ'.measurableSet hT) (preimage_inv_of_aff ha b hT) (u ij) := by
  rw [pullF_symm_apply]; rfl

theorem pullM_mem_symSub {u : L2F 𝕜 Ω' Ix} (hu : u ∈ symSub 𝕜 Ω') :
    pullM ha b hΩ' hT u ∈ symSub 𝕜 Ω := fun i j => by
  rw [pullM_apply, pullM_apply, (mem_symSub.1 hu) i j]

theorem pullM_symm_mem_symSub {u : L2F 𝕜 Ω Ix} (hu : u ∈ symSub 𝕜 Ω) :
    (pullM ha b hΩ' hT).symm u ∈ symSub 𝕜 Ω' := fun i j => by
  rw [pullM_symm_apply, pullM_symm_apply, (mem_symSub.1 hu) i j]

theorem pullM_mem_trSub {u : L2F 𝕜 Ω' Ix} (hu : u ∈ trSub 𝕜 Ω') :
    pullM ha b hΩ' hT u ∈ trSub 𝕜 Ω := by
  rw [mem_trSub]
  simp only [pullM_apply]
  rw [← map_sum, mem_trSub.1 hu, _root_.map_zero]

theorem pullM_symm_mem_trSub {u : L2F 𝕜 Ω Ix} (hu : u ∈ trSub 𝕜 Ω) :
    (pullM ha b hΩ' hT).symm u ∈ trSub 𝕜 Ω' := by
  rw [mem_trSub]
  simp only [pullM_symm_apply]
  rw [← map_sum, mem_trSub.1 hu, _root_.map_zero]

/-- **The pull-back of symmetric fields** `L²(Ω'; S) ≃ L²(Ω; S)`. -/
def pullSym : symSub 𝕜 Ω' ≃L[𝕜] symSub 𝕜 Ω :=
  restrictCLE (pullM (𝕜 := 𝕜) ha b hΩ' hT) (symSub 𝕜 Ω') (symSub 𝕜 Ω) (fun _ hu => pullM_mem_symSub ha b hΩ' hT hu)
    (fun _ hu => pullM_symm_mem_symSub ha b hΩ' hT hu)

/-- **The pull-back of trace-free fields** `L²(Ω'; T) ≃ L²(Ω; T)`. -/
def pullTr : trSub 𝕜 Ω' ≃L[𝕜] trSub 𝕜 Ω :=
  restrictCLE (pullM (𝕜 := 𝕜) ha b hΩ' hT) (trSub 𝕜 Ω') (trSub 𝕜 Ω) (fun _ hu => pullM_mem_trSub ha b hΩ' hT hu)
    (fun _ hu => pullM_symm_mem_trSub ha b hΩ' hT hu)

/-- **The pull-back of scalar fields** `L²(Ω') ≃ L²(Ω)`. -/
def pullL : L2 𝕜 Ω' ≃L[𝕜] L2 𝕜 Ω :=
  ContinuousLinearEquiv.equivOfInverse (pull ha b hΩ'.measurableSet hT)
    (pull (inv_ne_zero ha) (-(a⁻¹ • b)) (measurableSet_of_aff b hΩ'.measurableSet hT)
      (preimage_inv_of_aff ha b hT))
    (pull_pull ha (inv_ne_zero ha) hΩ'.measurableSet _ hT _ (aff_inv' ha b))
    (pull_pull (inv_ne_zero ha) ha _ hΩ'.measurableSet _ hT (aff_inv ha b))

@[simp] theorem coe_pullSym (u : symSub 𝕜 Ω') :
    ((pullSym ha b hΩ' hT u : symSub 𝕜 Ω) : L2F 𝕜 Ω Ix) = pullM ha b hΩ' hT (u : L2F 𝕜 Ω' Ix) :=
  rfl

@[simp] theorem coe_pullTr (u : trSub 𝕜 Ω') :
    ((pullTr ha b hΩ' hT u : trSub 𝕜 Ω) : L2F 𝕜 Ω Ix) = pullM ha b hΩ' hT (u : L2F 𝕜 Ω' Ix) :=
  rfl

theorem toL2F_pullL (f : L2 𝕜 Ω') :
    L2.toL2F 𝕜 Ω (pullL ha b hΩ' hT f) = pullF ha b hΩ'.measurableSet hT Unit (L2.toL2F 𝕜 Ω' f) :=
  rfl

theorem inner_pullSym (u v : symSub 𝕜 Ω') :
    ⟪pullSym ha b hΩ' hT u, pullSym ha b hΩ' hT v⟫_𝕜 =
      (((jac (E := R3) a)⁻¹ : ℝ) : 𝕜) * ⟪u, v⟫_𝕜 := by
  rw [Submodule.coe_inner, Submodule.coe_inner, coe_pullSym, coe_pullSym, inner_pullF]

theorem inner_pullTr (u v : trSub 𝕜 Ω') :
    ⟪pullTr ha b hΩ' hT u, pullTr ha b hΩ' hT v⟫_𝕜 =
      (((jac (E := R3) a)⁻¹ : ℝ) : 𝕜) * ⟪u, v⟫_𝕜 := by
  rw [Submodule.coe_inner, Submodule.coe_inner, coe_pullTr, coe_pullTr, inner_pullF]

theorem inner_pullL (u v : L2 𝕜 Ω') :
    ⟪pullL ha b hΩ' hT u, pullL ha b hΩ' hT v⟫_𝕜 =
      (((jac (E := R3) a)⁻¹ : ℝ) : 𝕜) * ⟪u, v⟫_𝕜 :=
  inner_pullₗ ha b hΩ'.measurableSet hT u v

/-! ### The complexes -/

omit ha hΩ' hT in
theorem hessCurlMax_d₁_eq (hΩ : IsOpen Ω) :
    (hessCurlMax 𝕜 hΩ).d₁ = (symCurlDivDiv 𝕜 hΩ).d₀† := rfl

omit ha hΩ' hT in
theorem hessCurlMax_d₀_eq (hΩ : IsOpen Ω) :
    (hessCurlMax 𝕜 hΩ).d₀ = (symCurlDivDiv 𝕜 hΩ).d₁† := rfl

/-- **`sym curl` on `H̊(sym curl, T)` under the pull-back**: `d₀ = a · P d₀' P⁻¹`. -/
theorem symCurlDivDiv_d₀_pull :
    (symCurlDivDiv 𝕜 (isOpen_of_aff b hΩ' hT)).d₀ =
      (symCurlDivDiv 𝕜 hΩ').d₀.conjScaled (pullTr ha b hΩ' hT) (pullSym ha b hΩ' hT)
        ((a ^ 1 : ℝ) : 𝕜) :=
  ConstCoeffOp.minimalVia_pull isHomogeneous_symCurlOp ha hΩ'.measurableSet hT
    (fun _ => rfl) (fun _ => rfl) (denseVia_symSub (isOpen_of_aff b hΩ' hT)) (denseVia_symSub hΩ')

/-- **`div div` on `H̊(div div, S)` under the pull-back**: `d₁ = a² · P d₁' P⁻¹`. -/
theorem symCurlDivDiv_d₁_pull :
    (symCurlDivDiv 𝕜 (isOpen_of_aff b hΩ' hT)).d₁ =
      (symCurlDivDiv 𝕜 hΩ').d₁.conjScaled (pullSym ha b hΩ' hT) (pullL ha b hΩ' hT)
        ((a ^ 2 : ℝ) : 𝕜) :=
  ConstCoeffOp.minimalVia_pull isHomogeneous_divdivOp ha hΩ'.measurableSet hT
    (fun _ => rfl) (fun _ => rfl) (denseVia_scalar (isOpen_of_aff b hΩ' hT))
    (denseVia_scalar hΩ')

/-- **The curl of (4.16) with the printed boundary conditions under the pull-back**:
`H(curl, S)` on `Ω` is the pull-back of `H(curl, S)` on `Ω'`, and `curl (u ∘ T) = a (curl u) ∘ T`. -/
theorem hessCurlMax_d₁_pull :
    (hessCurlMax 𝕜 (isOpen_of_aff b hΩ' hT)).d₁ =
      (hessCurlMax 𝕜 hΩ').d₁.conjScaled (pullSym ha b hΩ' hT) (pullTr ha b hΩ' hT)
        ((a ^ 1 : ℝ) : 𝕜) := by
  have h := LinearPMap.adjoint_conjScaled (T := (symCurlDivDiv 𝕜 hΩ').d₀)
    (e₁ := pullTr ha b hΩ' hT) (e₂ := pullSym ha b hΩ' hT) (κ := ((a ^ 1 : ℝ) : 𝕜))
    (s := (jac (E := R3) a)⁻¹) (inv_pos.2 (jac_pos ha)) (inner_pullTr ha b hΩ' hT)
    (inner_pullSym ha b hΩ' hT) (RCLike.ofReal_ne_zero.2 (pow_ne_zero 1 ha))
    (symCurlDivDiv 𝕜 hΩ').dense₀
  rw [RCLike.conj_ofReal] at h
  rw [hessCurlMax_d₁_eq, hessCurlMax_d₁_eq, symCurlDivDiv_d₀_pull ha b hΩ' hT, h]

/-- **The Hessian of (4.16) with the printed boundary conditions under the pull-back**
(`H²(Ω)`, `∇² (f ∘ T) = a² (∇² f) ∘ T`). -/
theorem hessCurlMax_d₀_pull :
    (hessCurlMax 𝕜 (isOpen_of_aff b hΩ' hT)).d₀ =
      (hessCurlMax 𝕜 hΩ').d₀.conjScaled (pullL ha b hΩ' hT) (pullSym ha b hΩ' hT)
        ((a ^ 2 : ℝ) : 𝕜) := by
  have h := LinearPMap.adjoint_conjScaled (T := (symCurlDivDiv 𝕜 hΩ').d₁)
    (e₁ := pullSym ha b hΩ' hT) (e₂ := pullL ha b hΩ' hT) (κ := ((a ^ 2 : ℝ) : 𝕜))
    (s := (jac (E := R3) a)⁻¹) (inv_pos.2 (jac_pos ha)) (inner_pullSym ha b hΩ' hT)
    (inner_pullL ha b hΩ' hT) (RCLike.ofReal_ne_zero.2 (pow_ne_zero 2 ha))
    (symCurlDivDiv 𝕜 hΩ').dense₁
  rw [RCLike.conj_ofReal] at h
  rw [hessCurlMax_d₀_eq, hessCurlMax_d₀_eq, symCurlDivDiv_d₁_pull ha b hΩ' hT, h]

/-- `d₀† = div div` on `H̊(div div, S)` under the pull-back. -/
theorem adjoint_hessCurlMax_d₀_pull :
    (hessCurlMax 𝕜 (isOpen_of_aff b hΩ' hT)).d₀† =
      (hessCurlMax 𝕜 hΩ').d₀†.conjScaled (pullSym ha b hΩ' hT) (pullL ha b hΩ' hT)
        ((a ^ 2 : ℝ) : 𝕜) := by
  rw [adjoint_hessCurlMax_d₀, adjoint_hessCurlMax_d₀]
  exact symCurlDivDiv_d₁_pull ha b hΩ' hT

/-- `d₁† = sym curl` on `H̊(sym curl, T)` under the pull-back. -/
theorem adjoint_hessCurlMax_d₁_pull :
    (hessCurlMax 𝕜 (isOpen_of_aff b hΩ' hT)).d₁† =
      (hessCurlMax 𝕜 hΩ').d₁†.conjScaled (pullTr ha b hΩ' hT) (pullSym ha b hΩ' hT)
        ((a ^ 1 : ℝ) : 𝕜) := by
  rw [adjoint_hessCurlMax_d₁, adjoint_hessCurlMax_d₁]
  exact symCurlDivDiv_d₀_pull ha b hΩ' hT

end Pull

/-! ### `L²(TSD)` under the pull-back -/

section TSD

variable {a : ℝ} (ha : a ≠ 0) (b : R3) {Ω Ω' : Set R3} (hΩ' : IsOpen Ω') (hT : aff a b ⁻¹' Ω' = Ω)
include ha hΩ' hT

/-- The weak divergence `d₀† = -div` of the thesis' complex under the pull-back. -/
theorem adjoint_gradCurl_d₀_pull :
    (gradCurl ℝ (isOpen_of_aff b hΩ' hT)).d₀† =
      (gradCurl ℝ hΩ').d₀†.conjScaled (pullM ha b hΩ' hT)
        (pullF ha b hΩ'.measurableSet hT (Fin 3)) ((a ^ 1 : ℝ) : ℝ) := by
  rw [gradCurl_d₀, gradCurl_d₀, ConstCoeffOp.minimal_pull isHomogeneous_gradOp33 ha b
    hΩ'.measurableSet hT hΩ', LinearPMap.adjoint_conjScaled (inv_pos.2 (jac_pos ha))
    (inner_pullF ha b hΩ'.measurableSet hT) (inner_pullF ha b hΩ'.measurableSet hT)
    (RCLike.ofReal_ne_zero.2 (pow_ne_zero 1 ha))
    ((gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).dense_minimal_domain hΩ'), RCLike.conj_ofReal]
  rfl

/-- **`L²(TSD)` is invariant under affine changes of variables**: `u ∘ T ∈ L²(Ω; TSD)` iff
`u ∈ L²(Ω'; TSD)`. -/
theorem pullF_mem_tsd_iff {u : L2F ℝ Ω' Ix} :
    pullM ha b hΩ' hT u ∈ tsd Ω ↔ u ∈ tsd Ω' := by
  have hΩ := isOpen_of_aff b hΩ' hT
  have hinj : Function.Injective (pull (𝕜 := ℝ) ha b hΩ'.measurableSet hT) :=
    (pullL (𝕜 := ℝ) ha b hΩ' hT).injective
  rw [mem_tsd_iff_ker hΩ, mem_tsd_iff_ker hΩ', adjoint_gradCurl_d₀_pull ha b hΩ' hT,
    LinearPMap.mem_ker_conjScaled (pow_ne_zero 1 ha),
    ContinuousLinearEquiv.symm_apply_apply]
  refine and_congr ?_ (and_congr ?_ Iff.rfl)
  · simp only [pullM_apply, hinj.eq_iff]
  · simp only [pullM_apply]
    rw [← map_sum, ← (pull (𝕜 := ℝ) ha b hΩ'.measurableSet hT).map_zero, hinj.eq_iff]

theorem pullSym_mem_tsdS_iff {u : symSub ℝ Ω'} :
    pullSym ha b hΩ' hT u ∈ tsdS Ω ↔ u ∈ tsdS Ω' :=
  pullF_mem_tsd_iff ha b hΩ' hT

theorem pullTr_mem_tsdT_iff {u : trSub ℝ Ω'} :
    pullTr ha b hΩ' hT u ∈ tsdT Ω ↔ u ∈ tsdT Ω' :=
  pullF_mem_tsd_iff ha b hΩ' hT

end TSD

end Feec.Models.BoundedDomain
