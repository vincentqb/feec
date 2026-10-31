module

public import Feec.Algebra.CubicalForm
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Coefficient forms and Mathlib's exterior algebra

The forms of `Feec` on `K^d` are coefficient functions `ω : Finset d → R` in the basis
`dx_s = dx_{s₁} ∧ ⋯ ∧ dx_{s_k}` (`Feec.ExteriorFibre`, `Feec.Koszul.PolyForm`). This module
identifies them with Mathlib's exterior algebra: the constant forms with
`ExteriorAlgebra K (Module.Dual K (d → K))`, and the polynomial forms with
`P(K^d) ⊗ Λ(K^d)* = MvPolynomial d K ⊗[K] ExteriorAlgebra K (Module.Dual K (d → K))`, the model
of [AFW2006], §3.1 (`dim P_rΛᵏ = dim P_r · dim Altᵏ`). Under the identification the exterior
derivative `Σⱼ ∂ⱼ ⊗ (dx_j ∧ ·)` and the Koszul differential `Σⱼ xⱼ ⊗ ι_{∂ⱼ}` (Mathlib's
contraction `CliffordAlgebra.contractLeft`) are `Feec.Koszul.extDeriv` and `Feec.Koszul.koszul`.

## Main definitions

* `Feec.ExteriorFibre.coeffs`: the coefficients `(ω_s)_s` of an element of the exterior algebra,
  through the action `ExteriorAlgebra.lift` of the covectors by exterior multiplication;
  `Feec.ExteriorFibre.coeffsEquiv`: it is a linear equivalence;
* `Feec.Koszul.TensorForm K d`, `Feec.Koszul.formEquiv`: `P(K^d) ⊗ Λ(K^d)* ≃ PolyForm K d`;
* `Feec.Koszul.tensorExtDeriv`, `Feec.Koszul.tensorKoszul`: `d` and `κ` on the tensor product.

## Main results

* `coeffs_ι_mul`, `coeffs_contractLeft`: exterior multiplication and contraction act on the
  coefficients by `Feec.ExteriorFibre.wedge` and `Feec.ExteriorFibre.interior`;
* `mem_map_coeffs_iff`: the coefficients of `⋀ᵏ(K^d)*` are the `k`-forms; `coeffs_ιMulti_proj`:
  `coeffs (dx_{σ₁} ∧ ⋯ ∧ dx_{σ_k}) = dx_s` for increasing `σ` with image `s`;
* `formEquiv_tensorExtDeriv`, `formEquiv_tensorKoszul`: the two models of `d` and `κ` agree;
* `map_formEquiv_range_mapIncl`: `S ⊗ ⋀ᵏ(K^d)*` is `Feec.Koszul.coeffForm K k S`;
  `map_formEquiv_iSup`: `⨁_σ restrictSupport (T σ) ⊗ dx_σ` is `Feec.Koszul.supportForm K d k T`;
* `contractLeft_mul_of_mem`, `tensorKoszul_mul`: the Leibniz rules
  `ψ ⌋ (x ∧ y) = (ψ ⌋ x) ∧ y + (-1)ᵏ x ∧ (ψ ⌋ y)` and `κ(ω ∧ η) = κω ∧ η + (-1)ᵏ ω ∧ κη`, the wedge
  product of `P(K^d) ⊗ Λ(K^d)*` being the product of the algebra; `range_mapIncl_mul_le`:
  `(S ⊗ ⋀ᵏ) ∧ (T ⊗ ⋀ˡ) ⊆ S T ⊗ ⋀^{k+l}`.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §3.1–§3.2 (polynomial differential forms, the Koszul differential, (3.6))

Bibliography: [references.bib](../../docs/references.bib)
-/

open Finset
open scoped TensorProduct

@[expose] public noncomputable section

namespace Feec.ExteriorFibre

variable (K : Type*) [Field K] (d : Type*) [LinearOrder d]

/-- The coordinates `ξ_j = ξ(e_j)` of a covector of `K^d`. -/
def coord : Module.Dual K (d → K) →ₗ[K] (d → K) :=
  LinearMap.pi fun j => LinearMap.applyₗ (Pi.single j 1)

@[simp] theorem coord_apply (ξ : Module.Dual K (d → K)) (j : d) :
    coord K d ξ j = ξ (Pi.single j 1) := rfl

/-- Exterior multiplication `ξ ∧ ·` by a covector, on the coefficient forms. -/
def wedgeₗ : Module.Dual K (d → K) →ₗ[K] Module.End K (Finset d → K) where
  toFun ξ :=
    { toFun := wedge (coord K d ξ)
      map_add' := wedge_add _
      map_smul' := wedge_smul _ }
  map_add' ξ η := LinearMap.ext fun ω => by simp [wedge_add_left]
  map_smul' c ξ := LinearMap.ext fun ω => by simp [wedge_smul_left]

/-- The action of the exterior algebra of `(K^d)*` on the coefficient forms by exterior
multiplication. -/
def wedgeAlgHom : ExteriorAlgebra K (Module.Dual K (d → K)) →ₐ[K] Module.End K (Finset d → K) :=
  ExteriorAlgebra.lift K ⟨wedgeₗ K d, fun _ => LinearMap.ext fun ω => wedge_wedge_self _ ω⟩

/-- The coefficients `(ω_s)_s` of an element `ω = Σ_s ω_s dx_s` of the exterior algebra of
`(K^d)*`, `dx_s = dx_{s₁} ∧ ⋯ ∧ dx_{s_k}`. -/
def coeffs : ExteriorAlgebra K (Module.Dual K (d → K)) →ₗ[K] (Finset d → K) :=
  LinearMap.applyₗ (Pi.single ∅ 1) ∘ₗ (wedgeAlgHom K d).toLinearMap

variable {K d}

theorem coeffs_ι_mul (ξ : Module.Dual K (d → K)) (x : ExteriorAlgebra K (Module.Dual K (d → K))) :
    coeffs K d (ExteriorAlgebra.ι K ξ * x) = wedge (coord K d ξ) (coeffs K d x) := by
  simp [coeffs, wedgeAlgHom, wedgeₗ]

theorem coeffs_algebraMap (c : K) :
    coeffs K d (algebraMap K (ExteriorAlgebra K (Module.Dual K (d → K))) c) =
      c • Pi.single ∅ 1 := by
  simp [coeffs, Algebra.algebraMap_eq_smul_one]


theorem eq_sum_coord_smul_proj [Fintype d] (ξ : Module.Dual K (d → K)) :
    ξ = ∑ j, coord K d ξ j • LinearMap.proj j := by
  ext v
  simp [Pi.single_apply]

theorem interior_single_empty [Fintype d] (ζ : d → K) :
    interior ζ (Pi.single (∅ : Finset d) (1 : K)) = 0 := by
  funext s
  exact sum_eq_zero fun j _ => by simp [insert_ne_empty]

/-- Contraction with a vector `ψ` acts on the coefficients as interior multiplication by its
coordinates `ψ(dx_j)`. -/
theorem coeffs_contractLeft [Fintype d] (ψ : Module.Dual K (Module.Dual K (d → K)))
    (x : ExteriorAlgebra K (Module.Dual K (d → K))) :
    coeffs K d (CliffordAlgebra.contractLeft ψ x) =
      interior (fun j => ψ (LinearMap.proj j)) (coeffs K d x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap c =>
    rw [CliffordAlgebra.contractLeft_algebraMap, map_zero, coeffs_algebraMap, interior_smul,
      interior_single_empty, smul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, interior_add]
  | ι_mul x ξ hx =>
    have hc := wedge_interior_add_interior_wedge (coord K d ξ) (fun j => ψ (LinearMap.proj j))
      (coeffs K d x)
    have hψ : ∑ j, coord K d ξ j * ψ (LinearMap.proj j) = ψ ξ := by
      conv_rhs => rw [eq_sum_coord_smul_proj ξ]
      simp [map_sum, map_smul]
    rw [CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, coeffs_ι_mul, coeffs_ι_mul, hx, ← hψ,
      ← hc]
    abel


theorem coord_proj (j : d) : coord K d (LinearMap.proj j) = Pi.single j 1 := by
  funext i; simp [Pi.single_apply, eq_comm]

theorem isDeg_coeffs_ιMulti (k : ℕ) (v : Fin k → Module.Dual K (d → K)) :
    IsDeg k (coeffs K d (ExteriorAlgebra.ιMulti K k v)) := by
  induction k with
  | zero =>
    rw [ExteriorAlgebra.ιMulti_zero_apply, ← map_one (algebraMap K _), coeffs_algebraMap]
    intro s hs
    simp [Finset.card_eq_zero.not.1 hs]
  | succ k ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, coeffs_ι_mul]
    exact (ih _).wedge _

/-- The coefficients of an element of `⋀ᵏ(K^d)*` form a `k`-form. -/
theorem isDeg_coeffs {k : ℕ} {x : ExteriorAlgebra K (Module.Dual K (d → K))}
    (hx : x ∈ ⋀[K]^k (Module.Dual K (d → K))) : IsDeg k (coeffs K d x) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem _ h => obtain ⟨v, rfl⟩ := h; exact isDeg_coeffs_ιMulti k v
  | zero => intro s _; simp
  | add x y _ _ hx hy => intro s hs; simp [hx s hs, hy s hs]
  | smul c x _ hx => intro s hs; simp [hx s hs]

theorem single_mem_map_coeffs (s : Finset d) :
    Pi.single s 1 ∈ (⋀[K]^#s (Module.Dual K (d → K))).map (coeffs K d) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, ?_, ?_⟩
    · rw [← ExteriorAlgebra.ιMulti_zero_apply (R := K) ![]]
      exact ExteriorAlgebra.ιMulti_range K 0 ⟨_, rfl⟩
    · rw [← map_one (algebraMap K _), coeffs_algebraMap, one_smul]
  | insert j t hj ih =>
    obtain ⟨x, hx, hcx⟩ := ih
    refine ⟨(sgn j t : K) • (ExteriorAlgebra.ι K (LinearMap.proj j) * x), ?_, ?_⟩
    · refine Submodule.smul_mem _ _ ?_
      rw [card_insert_of_notMem hj, ExteriorAlgebra.exteriorPower, pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) hx
    · simp only [map_smul, coeffs_ι_mul, hcx, coord_proj, wedge_single_single hj, smul_smul,
        sgn_mul_self, one_smul]

/-- The coefficients `coeffs x` of `x ∈ ⋀ᵏ(K^d)*` are exactly the `k`-forms. -/
theorem mem_map_coeffs_iff {k : ℕ} {c : Finset d → K} [Fintype d] :
    c ∈ (⋀[K]^k (Module.Dual K (d → K))).map (coeffs K d) ↔ IsDeg k c := by
  refine ⟨fun ⟨x, hx, h⟩ => h ▸ isDeg_coeffs hx, fun hc => ?_⟩
  rw [← univ_sum_single c]
  refine Submodule.sum_mem _ fun s _ => ?_
  by_cases hs : #s = k
  · rw [show Pi.single s (c s) = c s • (Pi.single s 1 : Finset d → K) by
      ext t; simp [Pi.single_apply]]
    exact Submodule.smul_mem _ _ (hs ▸ single_mem_map_coeffs s)
  · rw [hc s hs, Pi.single_zero]; exact Submodule.zero_mem _

theorem coeffs_surjective [Fintype d] : Function.Surjective (coeffs K d) := fun c => by
  rw [← univ_sum_single c]
  have h : ∀ s, ∃ x, coeffs K d x = Pi.single s (c s) := fun s => by
    obtain ⟨x, -, hx⟩ := single_mem_map_coeffs (K := K) s
    exact ⟨c s • x, by rw [map_smul, hx, ← Pi.single_smul, smul_eq_mul, mul_one]⟩
  choose x hx using h
  exact ⟨∑ s, x s, by simp [map_sum, hx]⟩

theorem coeffs_bijective [Fintype d] : Function.Bijective (coeffs K d) := by
  have b := (Pi.basisFun K d).dualBasis.ExteriorAlgebra
  have := Module.Finite.of_basis b
  refine ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2 coeffs_surjective,
    coeffs_surjective⟩
  rw [Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card]

variable (K d) in
/-- The exterior algebra of `(K^d)*` is the space of coefficient forms `Σ_s ω_s dx_s`. -/
def coeffsEquiv [Fintype d] : ExteriorAlgebra K (Module.Dual K (d → K)) ≃ₗ[K] (Finset d → K) :=
  LinearEquiv.ofBijective (coeffs K d) coeffs_bijective

/-- **The Leibniz rule for the contraction**: `ψ ⌋ (x ∧ y) = (ψ ⌋ x) ∧ y + (-1)ᵏ x ∧ (ψ ⌋ y)` for
`x ∈ ⋀ᵏM`. -/
theorem contractLeft_mul_of_mem {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (ψ : Module.Dual R M) {k : ℕ} {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^k M)
    (y : ExteriorAlgebra R M) :
    CliffordAlgebra.contractLeft ψ (x * y) = CliffordAlgebra.contractLeft ψ x * y +
      (-1 : R) ^ k • (x * CliffordAlgebra.contractLeft ψ y) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ExteriorAlgebra.ιMulti_succ_apply, mul_assoc, ExteriorAlgebra.ι,
        CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι_mul,
        ← ExteriorAlgebra.ι, ih, pow_succ]
      simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_assoc]
      module
  | zero => simp
  | add x y _ _ hx hy => simp only [add_mul, map_add, hx, hy, smul_add]; abel
  | smul c x _ hx => simp only [smul_mul_assoc, map_smul, hx, smul_add, smul_comm c]

end Feec.ExteriorFibre

namespace Feec.Koszul

open ExteriorFibre MvPolynomial

variable (K : Type*) [Field K] (d : Type*) [LinearOrder d] [Fintype d]

/-- Polynomial differential forms on `K^d` as `P(K^d) ⊗ Λ(K^d)*`. -/
abbrev TensorForm := MvPolynomial d K ⊗[K] ExteriorAlgebra K (Module.Dual K (d → K))

/-- The coefficients `ω_s ∈ K[x]` of `ω = Σ_s ω_s dx_s ∈ P(K^d) ⊗ Λ(K^d)*`. -/
def formEquiv : TensorForm K d ≃ₗ[K] PolyForm K d :=
  (coeffsEquiv K d).lTensor _ ≪≫ₗ TensorProduct.piScalarRight K K (MvPolynomial d K) (Finset d)

/-- The exterior derivative `d = Σⱼ ∂ⱼ ⊗ (dx_j ∧ ·)` of `P(K^d) ⊗ Λ(K^d)*`. -/
def tensorExtDeriv : TensorForm K d →ₗ[K] TensorForm K d :=
  ∑ j, TensorProduct.map (pderiv j).toLinearMap
    (LinearMap.mulLeft K (ExteriorAlgebra.ι K (LinearMap.proj j)))

/-- The Koszul differential `κ = Σⱼ xⱼ ⊗ ι_{∂ⱼ}` of `P(K^d) ⊗ Λ(K^d)*`. -/
def tensorKoszul : TensorForm K d →ₗ[K] TensorForm K d :=
  ∑ j, TensorProduct.map (LinearMap.mulLeft K (X j))
    (CliffordAlgebra.contractLeft (Module.Dual.eval K (d → K) (Pi.single j 1)))

variable {K d}

@[simp] theorem formEquiv_tmul (p : MvPolynomial d K)
    (x : ExteriorAlgebra K (Module.Dual K (d → K))) :
    formEquiv K d (p ⊗ₜ x) = fun s => coeffs K d x s • p := by
  simp [formEquiv, coeffsEquiv]

omit [Fintype d] in
theorem sgn_eq_algebraMap (j : d) (s : Finset d) :
    (sgn j s : MvPolynomial d K) = algebraMap K _ (sgn j s) := by
  simp [sgn]

theorem formEquiv_tensorExtDeriv (ω : TensorForm K d) :
    formEquiv K d (tensorExtDeriv K d ω) = extDeriv (formEquiv K d ω) := by
  induction ω using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, extDeriv_add]
  | tmul p x =>
    funext s
    simp only [tensorExtDeriv, LinearMap.sum_apply, Finset.sum_apply, TensorProduct.map_tmul,
      map_sum, formEquiv_tmul, LinearMap.mulLeft_apply, coeffs_ι_mul, coord_proj, extDeriv_apply,
      wedge_apply]
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Pi.single_apply, sgn_eq_algebraMap, Algebra.smul_def, apply_ite C, ite_mul,
      Finset.sum_ite_eq, mul_assoc]

theorem formEquiv_tensorKoszul (ω : TensorForm K d) :
    formEquiv K d (tensorKoszul K d ω) = koszul (formEquiv K d ω) := by
  induction ω using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, koszul_add]
  | tmul p x =>
    funext s
    simp only [tensorKoszul, LinearMap.sum_apply, Finset.sum_apply, TensorProduct.map_tmul,
      map_sum, formEquiv_tmul, LinearMap.mulLeft_apply, coeffs_contractLeft, koszul,
      interior_apply]
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Pi.single_apply, sgn_eq_algebraMap, Algebra.smul_def, apply_ite C, ite_mul,
      Finset.sum_ite_eq, eq_comm]
    ring

theorem formEquiv_tmul_eq_single {p : MvPolynomial d K}
    {x : ExteriorAlgebra K (Module.Dual K (d → K))} {s : Finset d}
    (hx : coeffs K d x = Pi.single s 1) : formEquiv K d (p ⊗ₜ x) = Pi.single s p := by
  funext t
  by_cases h : t = s
  · subst h; simp [hx]
  · simp [hx, Pi.single_eq_of_ne h]

/-- **`S ⊗ ⋀ᵏ(K^d)*` is the space of `k`-forms with coefficients in `S`.** -/
theorem map_formEquiv_range_mapIncl (S : Submodule K (MvPolynomial d K)) (k : ℕ) :
    (LinearMap.range (TensorProduct.mapIncl S (⋀[K]^k (Module.Dual K (d → K))))).map
      (formEquiv K d).toLinearMap = coeffForm K k S := by
  rw [TensorProduct.range_mapIncl, Submodule.map₂_eq_span_image2, Submodule.map_span]
  refine le_antisymm (Submodule.span_le.2 ?_) fun ω hω => ?_
  · rintro _ ⟨_, ⟨p, hp, x, hx, rfl⟩, rfl⟩
    refine ⟨fun s hs => ?_, fun s => ?_⟩
    · simp [isDeg_coeffs hx s hs]
    · simpa using S.smul_mem _ hp
  · rw [← univ_sum_single ω]
    refine Submodule.sum_mem _ fun s _ => ?_
    by_cases hs : #s = k
    · have hdeg : IsDeg k (Pi.single s 1 : Finset d → K) := fun t ht =>
        Pi.single_eq_of_ne (fun h : t = s => ht (h ▸ hs)) _
      obtain ⟨x, hx, hcx⟩ := mem_map_coeffs_iff.2 hdeg
      exact Submodule.subset_span ⟨_, ⟨ω s, hω.2 s, x, hx, rfl⟩, formEquiv_tmul_eq_single hcx⟩
    · rw [hω.1 s hs, Pi.single_zero]; exact Submodule.zero_mem _

omit [Fintype d] in
theorem image_univ_fin_succ {k : ℕ} (σ : Fin (k + 1) → d) :
    univ.image σ = insert (σ 0) (univ.image (σ ∘ Fin.succ)) := by
  ext x; simp [Fin.exists_fin_succ, eq_comm]

omit [Fintype d] in
/-- `dx_{σ₁} ∧ ⋯ ∧ dx_{σ_k}` for increasing `σ` is the basis form `dx_s`, `s = {σ₁, …, σ_k}`. -/
theorem coeffs_ιMulti_proj {k : ℕ} {σ : Fin k → d} (hσ : StrictMono σ) :
    coeffs K d (ExteriorAlgebra.ιMulti K k fun i => LinearMap.proj (σ i)) =
      Pi.single (univ.image σ) 1 := by
  induction k with
  | zero =>
    rw [ExteriorAlgebra.ιMulti_zero_apply, ← map_one (algebraMap K _), coeffs_algebraMap, one_smul]
    simp
  | succ k ih =>
    have h0 : σ 0 ∉ univ.image (σ ∘ Fin.succ) := by
      simp only [mem_image, mem_univ, true_and, Function.comp_apply, not_exists]
      exact fun i h => (hσ (Fin.succ_pos i)).ne' h
    have hs : (sgn (σ 0) (univ.image (σ ∘ Fin.succ)) : K) = 1 := by
      rw [sgn, filter_eq_empty_iff.2 fun l hl => ?_, card_empty, pow_zero]
      obtain ⟨i, -, rfl⟩ := mem_image.1 hl
      exact not_lt.2 (hσ (Fin.succ_pos i)).le
    rw [ExteriorAlgebra.ιMulti_succ_apply, coeffs_ι_mul]
    erw [ih (hσ.comp (Fin.strictMono_succ))]
    rw [coord_proj, wedge_single_single h0, hs, one_smul, image_univ_fin_succ]

/-- **`⨁_σ restrictSupport (T σ) dx_σ` is the space of `k`-forms whose coefficient `ω_s` is
supported on `T s`** (`σ` increasing, `s` its image). -/
theorem map_formEquiv_iSup (T : Finset d → Set (d →₀ ℕ)) (k : ℕ) :
    (⨆ (σ : Fin k → d) (_ : StrictMono σ), (restrictSupport K (T (univ.image σ))).map
      ((TensorProduct.mk K _ _).flip (ExteriorAlgebra.ιMulti K k fun i =>
        LinearMap.proj (σ i)))).map (formEquiv K d).toLinearMap = supportForm K d k T := by
  simp_rw [Submodule.map_iSup, ← Submodule.map_comp]
  refine le_antisymm (iSup₂_le fun σ hσ => ?_) (supportForm_le_of_single fun s hs α hα => ?_)
  · rintro _ ⟨p, hp, rfl⟩
    have hcard : #(univ.image σ) = k := by
      rw [card_image_of_injective _ hσ.injective, card_univ, Fintype.card_fin]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
      TensorProduct.mk_apply, LinearEquiv.coe_coe]
    rw [formEquiv_tmul_eq_single (coeffs_ιMulti_proj hσ)]
    refine ⟨fun t ht => Pi.single_eq_of_ne (fun h : t = _ => ht (h ▸ hcard)) _, fun t => ?_⟩
    by_cases h : t = univ.image σ
    · subst h; rwa [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h]; exact Submodule.zero_mem _
  · set σ := s.orderEmbOfFin hs
    have hσ : univ.image σ = s := by simp [σ]
    refine Submodule.mem_iSup_of_mem (σ : Fin k → d) (Submodule.mem_iSup_of_mem σ.strictMono ?_)
    refine ⟨monomial α 1, (monomial_mem_restrictSupport K).2 (Or.inl (hσ ▸ hα)), ?_⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
      TensorProduct.mk_apply, LinearEquiv.coe_coe]
    rw [formEquiv_tmul_eq_single (coeffs_ιMulti_proj σ.strictMono), hσ]

/-! ### The wedge product -/

omit [LinearOrder d] [Fintype d] in
/-- `P_r P_s ⊆ P_{r+s}`. -/
theorem restrictTotalDegree_mul_le (r s : ℕ) :
    restrictTotalDegree d K r * restrictTotalDegree d K s ≤ restrictTotalDegree d K (r + s) :=
  Submodule.mul_le.2 fun p hp q hq => by
    rw [mem_restrictTotalDegree] at hp hq ⊢
    exact (totalDegree_mul p q).trans (add_le_add hp hq)

omit [LinearOrder d] [Fintype d] in
/-- `(S ⊗ ⋀ᵏ) ∧ (T ⊗ ⋀ˡ) ⊆ S T ⊗ ⋀^{k+l}`: the wedge product of `P(K^d) ⊗ Λ(K^d)*` is the
product of the algebra. -/
theorem range_mapIncl_mul_le (S T : Submodule K (MvPolynomial d K)) (k l : ℕ) :
    LinearMap.range (TensorProduct.mapIncl S (⋀[K]^k (Module.Dual K (d → K)))) *
        LinearMap.range (TensorProduct.mapIncl T (⋀[K]^l (Module.Dual K (d → K)))) ≤
      LinearMap.range (TensorProduct.mapIncl (S * T) (⋀[K]^(k + l) (Module.Dual K (d → K)))) := by
  rw [TensorProduct.range_mapIncl, TensorProduct.range_mapIncl, TensorProduct.range_mapIncl,
    Submodule.map₂_eq_span_image2, Submodule.map₂_eq_span_image2, Submodule.span_mul_span,
    Submodule.map₂_eq_span_image2]
  refine Submodule.span_mono ?_
  rintro _ ⟨_, ⟨p, hp, x, hx, rfl⟩, _, ⟨q, hq, y, hy, rfl⟩, rfl⟩
  refine ⟨p * q, Submodule.mul_mem_mul hp hq, x * y, ?_,
    (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).symm⟩
  rw [SetLike.mem_coe, show ⋀[K]^(k + l) (Module.Dual K (d → K)) =
    ⋀[K]^k (Module.Dual K (d → K)) * ⋀[K]^l (Module.Dual K (d → K)) from pow_add _ _ _]
  exact Submodule.mul_mem_mul hx hy

theorem tensorKoszul_tmul (p : MvPolynomial d K) (x : ExteriorAlgebra K (Module.Dual K (d → K))) :
    tensorKoszul K d (p ⊗ₜ x) = ∑ j, (X j * p) ⊗ₜ
      CliffordAlgebra.contractLeft (Module.Dual.eval K (d → K) (Pi.single j 1)) x := by
  simp [tensorKoszul]

/-- **The Leibniz rule for `κ`**: `κ (ω ∧ η) = κω ∧ η + (-1)ᵏ ω ∧ κη` for a `k`-form `ω`.
[AFW2006], (3.6) -/
theorem tensorKoszul_mul {k : ℕ} {ω : TensorForm K d}
    (hω : ω ∈ LinearMap.range (TensorProduct.mapIncl ⊤ (⋀[K]^k (Module.Dual K (d → K)))))
    (η : TensorForm K d) :
    tensorKoszul K d (ω * η) =
      tensorKoszul K d ω * η + (-1 : K) ^ k • (ω * tensorKoszul K d η) := by
  rw [TensorProduct.range_mapIncl, Submodule.map₂_eq_span_image2] at hω
  induction hω using Submodule.span_induction with
  | mem ω hω =>
    obtain ⟨p, -, x, hx, rfl⟩ := hω
    induction η using TensorProduct.inductionOn with
    | add η η' h h' => simp only [mul_add, map_add, h, h', smul_add]; abel
    | tmul q y =>
      simp only [TensorProduct.mk_apply, Algebra.TensorProduct.tmul_mul_tmul, tensorKoszul_tmul,
        contractLeft_mul_of_mem _ hx, Finset.sum_mul, Finset.mul_sum, Finset.smul_sum,
        TensorProduct.tmul_add, Finset.sum_add_distrib, TensorProduct.tmul_smul]
      simp only [mul_assoc, mul_left_comm p]
  | zero => simp
  | add ω ω' _ _ h h' => simp only [add_mul, map_add, h, h', smul_add]; abel
  | smul c ω _ h => simp only [smul_mul_assoc, map_smul, h, smul_add, smul_comm c]

end Feec.Koszul
