module

public import Feec.Domain.FormPullback
public import Feec.Models.Cube.FiniteElementConvergence
public import Feec.Models.Cube.PolyRate

/-!
# The finite element method on parallelepipeds

PLACEHOLDER
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset Filter Topology
open scoped ContDiff InnerProductSpace

namespace Feec.Models.Parallelepiped

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex Feec.ExteriorFibre

variable {n : ℕ}

/-! ### The fibre matrices of the pullback of forms -/

/-- The matrix `A` as a family of rows, the argument of `Feec.FiniteElement.affine`. -/
abbrev rows (A : Matrix (Fin n) (Fin n) ℝ) : Fin n → Fin n → ℝ := fun i j => A i j

/-- **The fibre matrix of the pullback by `A` on `k`-forms**: `(A^* α)_s = Σ_t minorMat A k s t α_t`
with `minorMat A k s t = (θ_{t₁} ∧ ⋯ ∧ θ_{t_k})_s` for the rows `θᵢ = A_{i·}`, the `k × k` minor
of `A` on the rows `t` and the columns `s` (`Feec.ExteriorFibre.wedgeProd_apply_eq_det_submatrix`). -/
def minorMat (A : Matrix (Fin n) (Fin n) ℝ) (k : ℤ) (s t : formIdx n k) : ℝ :=
  wedgeProd (rows A) t.1 s.1

theorem affine_rows (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    affine (rows A) b = affMap A b := by
  funext x i
  rw [affine_apply, affMap_apply]

/-- `Σ_{t ⊆ Fin n} ext(f)_t g_t = Σ_{#t = k} f_t g_t`. -/
theorem sum_formExt_mul {k : ℤ} (f : formIdx n k → ℝ) (g : Finset (Fin n) → ℝ) :
    ∑ t, formExt f t * g t = ∑ t : formIdx n k, f t * g t.1 := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun t : Finset (Fin n) => (#t : ℤ) = k)]
  rw [Fintype.sum_eq_zero (fun t : {t : Finset (Fin n) // ¬ (#t : ℤ) = k} => _) fun t => by
    simp [formExt, t.2], add_zero]
  refine Fintype.sum_congr _ _ fun t => ?_
  rw [formExt_val]

/-- The degree-`k` form field with components `φ`. -/
def formField {k : ℤ} (φ : formIdx n k → (Fin n → ℝ) → ℝ) : FormField n :=
  fun x s => formExt φ s x

theorem formExt_apply {k : ℤ} (φ : formIdx n k → (Fin n → ℝ) → ℝ) (s : Finset (Fin n))
    (x : Fin n → ℝ) : formExt φ s x = formExt (fun t => φ t x) s := by
  unfold formExt; split_ifs <;> rfl

theorem isDeg_formField {k : ℕ} (φ : formIdx n k → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    IsDeg k (formField φ x) := by
  intro s hs
  have h : ¬ (#s : ℤ) = (k : ℤ) := fun h => hs (by exact_mod_cast h)
  simp [formField, formExt, h]

theorem contDiff_formField {k : ℤ} {φ : formIdx n k → (Fin n → ℝ) → ℝ}
    (hφ : ∀ t, ContDiff ℝ ∞ (φ t)) : ContDiff ℝ ∞ (formField φ) :=
  contDiff_pi.2 fun s => contDiff_formExt hφ s

/-- **The pullback of fields is `Feec.FiniteElement.affinePullback` pointwise**: the components of
`T^* φ` are those of the pullback of the form field of `φ`. -/
theorem pullFun_minorMat (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) {k : ℤ}
    (φ : formIdx n k → (Fin n → ℝ) → ℝ) :
    pullFun A b (minorMat A k) φ = formComp (affinePullback (rows A) b (formField φ)) := by
  funext s x
  simp only [Feec.Domain.pullFun, formComp, affinePullback_apply, pullback_apply, affine_rows,
    formField, formExt_apply φ _ (affMap A b x)]
  rw [sum_formExt_mul (fun t => φ t (affMap A b x)) (fun t => wedgeProd (rows A) t s.1)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [minorMat, mul_comm]

/-- `d` of the form field of `φ` is the form field of `d φ`. -/
theorem extDeriv_formField {k : ℕ} (φ : formIdx n k → (Fin n → ℝ) → ℝ) :
    extDeriv (formField φ) = formField ((extDerivOp ℝ n k).apply φ) := by
  funext x s
  by_cases hs : (#s : ℤ) = (k : ℤ) + 1
  · simp only [formField]
    rw [formExt_extDerivOp_apply φ hs, extD, extDeriv_apply]
    rfl
  · rw [IsDeg.extDeriv (isDeg_formField φ) x s (fun h => hs (by exact_mod_cast h))]
    simp [formField, formExt, hs]

/-- On negative degrees there are no components. -/
theorem formIdx_isEmpty_of_neg {k : ℤ} (hk : k < 0) : IsEmpty (formIdx n k) :=
  ⟨fun s => by have := s.2; omega⟩

/-- `d` of a field indexed by an empty set of components vanishes. -/
theorem extDerivOp_apply_of_isEmpty {k : ℤ} [IsEmpty (formIdx n k)]
    (w : formIdx n k → (Fin n → ℝ) → ℝ) (u : formIdx n (k + 1)) (y : Fin n → ℝ) :
    (extDerivOp ℝ n k).apply w u y = 0 := by
  rw [extDerivOp_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : formExt w (u.1.erase j) = 0 := by
    funext z; simp only [formExt, Pi.zero_apply]; split_ifs with h
    · exact (IsEmpty.false (⟨_, h⟩ : formIdx n k)).elim
    · rfl
  rw [this]; simp

/-- **The minors intertwine `d`**: `d (T^* φ) = T^* (d φ)` for smooth `k`-forms
(`Feec.FiniteElement.extDeriv_affinePullback_apply`). -/
theorem isDIntertwining_minorMat (A : Matrix (Fin n) (Fin n) ℝ) :
    IsDIntertwining A (minorMat A) := by
  intro b k φ hφ
  by_cases hk : 0 ≤ k
  · lift k to ℕ using hk
    have hω := contDiff_formField hφ
    funext t x
    rw [pullFun_minorMat, extDerivOp_apply_formComp (IsDeg.affinePullback (isDeg_formField φ) _ b)
      t x, extDeriv_affinePullback_apply _ b ((hω.differentiable (by simp)) _), pullFun_minorMat,
      extDeriv_formField]
    rfl
  · have := formIdx_isEmpty_of_neg (n := n) (not_le.1 hk)
    funext t x
    rw [extDerivOp_apply_of_isEmpty, Feec.Domain.pullFun]
    simp only [extDerivOp_apply_of_isEmpty, mul_zero, Finset.sum_const_zero]

/-- **Cauchy–Binet for the minors** (functoriality of the pullback,
`Feec.ExteriorFibre.pullback_pullback`). -/
theorem sum_minorMat_mul (A A' : Matrix (Fin n) (Fin n) ℝ) (k : ℤ) (s r : formIdx n k) :
    ∑ t, minorMat A k s t * minorMat A' k t r = minorMat (A' * A) k s r := by
  classical
  have h := congrFun (pullback_pullback (rows A') (rows A) (Pi.single r.1 (1 : ℝ))) s.1
  simp only [pullback_apply, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h
  have e1 : (fun j l => ∑ i, rows A' j i * rows A i l) = rows (A' * A) := by
    funext j l; simp [rows, Matrix.mul_apply]
  rw [e1] at h
  rw [minorMat, ← h]
  have hdeg : ∀ t : Finset (Fin n), (#t : ℤ) ≠ k → wedgeProd (rows A') r.1 t = 0 := fun t ht =>
    isDeg_wedgeProd (rows A') r.1 t (fun h' => ht (by rw [h', r.2]))
  rw [← Fintype.sum_subtype_add_sum_subtype (fun t : Finset (Fin n) => (#t : ℤ) = k)]
  rw [Fintype.sum_eq_zero (fun t : {t : Finset (Fin n) // ¬ (#t : ℤ) = k} => _) fun t => by
    rw [hdeg t t.2, zero_mul], add_zero]
  refine Fintype.sum_congr _ _ fun t => ?_
  rw [minorMat, minorMat, mul_comm]

theorem minorMat_one (k : ℤ) (s r : formIdx n k) :
    minorMat (1 : Matrix (Fin n) (Fin n) ℝ) k s r = if s = r then 1 else 0 := by
  classical
  have e : rows (1 : Matrix (Fin n) (Fin n) ℝ) = fun j => (Pi.single j 1 : Fin n → ℝ) := by
    funext j l; simp [rows, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [minorMat, e, wedgeProd_single, Pi.single_apply]
  by_cases h : s = r
  · subst h; simp
  · have h' : ¬ s.1 = r.1 := fun h' => h (Subtype.ext h')
    simp [h, h']

/-- **The fibre data of the pullback of forms along `x ↦ A x + b`**: the minors of `A` and of
`A⁻¹`, mutually inverse (Cauchy–Binet) and intertwining `d`. -/
def formPullData (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) : FormPullData A where
  C := minorMat A
  Cinv := minorMat A⁻¹
  isDIntertwining := isDIntertwining_minorMat A
  isDIntertwining_inv := isDIntertwining_minorMat A⁻¹
  mul_inv k s r := by rw [sum_minorMat_mul, Matrix.nonsing_inv_mul A hA, minorMat_one]
  inv_mul k s r := by rw [sum_minorMat_mul, Matrix.mul_nonsing_inv A hA, minorMat_one]

end Feec.Models.Parallelepiped

/-! ### Isomorphisms of Hilbert complexes and the transfer of the finite element theory -/

namespace Feec.HilbertComplex

open Filter Topology

variable {ι : Type*} {c : ComplexShape ι} {W W' : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace ℝ (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace ℝ (W' i)] [∀ i, CompleteSpace (W' i)]

/-- **`e` is an isomorphism of Hilbert complexes** `H ≅ H'` (not necessarily isometric): every
`e i` is a bounded isomorphism with `e (D(dᵢⱼ)) = D(d'ᵢⱼ)` and `d' e = e d`. -/
structure IsChainIso (H : HilbertComplex ℝ c W) (H' : HilbertComplex ℝ c W')
    (e : ∀ i, W i ≃L[ℝ] W' i) : Prop where
  mem_domain_iff : ∀ i j (x : W i), e i x ∈ (H'.d i j).domain ↔ x ∈ (H.d i j).domain
  comm : ∀ i j (x : (H.d i j).domain) (h : e i x ∈ (H'.d i j).domain),
    H'.d i j ⟨e i x, h⟩ = e j (H.d i j x)

/-- A transported complex is isomorphic to the original one. -/
theorem isChainIso_transport (H : HilbertComplex ℝ c W) (e : ∀ i, W i ≃L[ℝ] W' i) :
    IsChainIso H (H.transport e (fun _ _ => 1) fun _ _ => one_ne_zero) e where
  mem_domain_iff i j x := by
    change (e i).symm (e i x) ∈ (H.d i j).domain ↔ x ∈ (H.d i j).domain
    rw [ContinuousLinearEquiv.symm_apply_apply]
  comm i j x h := by
    refine (HilbertComplex.transportD_apply (H := H) (e := e) (κ := fun _ _ => (1 : ℝ))
      ⟨e i x, h⟩).trans ?_
    rw [one_smul]
    exact congrArg (e j) (LinearPMap.apply_congr' _ _ _ ((e i).symm_apply_apply x))

namespace IsChainIso

variable {H : HilbertComplex ℝ c W} {H' : HilbertComplex ℝ c W'} {e : ∀ i, W i ≃L[ℝ] W' i}
  (hI : IsChainIso H H' e)
include hI

theorem symm_mem_domain_iff (i j : ι) (y : W' i) :
    (e i).symm y ∈ (H.d i j).domain ↔ y ∈ (H'.d i j).domain := by
  rw [← hI.mem_domain_iff, ContinuousLinearEquiv.apply_symm_apply]

theorem comm_symm (i j : ι) (y : (H'.d i j).domain) (h : (e i).symm y ∈ (H.d i j).domain) :
    H.d i j ⟨(e i).symm y, h⟩ = (e j).symm (H'.d i j y) := by
  have h' : e i ((e i).symm y) ∈ (H'.d i j).domain := by
    rw [ContinuousLinearEquiv.apply_symm_apply]; exact y.2
  have e1 := hI.comm i j ⟨_, h⟩ h'
  have e2 : H'.d i j ⟨e i ((e i).symm y), h'⟩ = H'.d i j y :=
    LinearPMap.apply_congr' _ _ _ ((e i).apply_symm_apply y)
  rw [e2] at e1
  rw [e1, ContinuousLinearEquiv.symm_apply_apply]

theorem mem_cycles_iff (i : ι) (x : W i) : e i x ∈ H'.cycles i ↔ x ∈ H.cycles i := by
  simp only [HilbertComplex.cycles, LinearPMap.mem_ker_iff]
  constructor
  · rintro ⟨y, hy, h0⟩
    have hex : e i x ∈ (H'.d i (c.next i)).domain := by rw [hy]; exact y.2
    have hx : x ∈ (H.d i (c.next i)).domain := (hI.mem_domain_iff _ _ x).1 hex
    refine ⟨⟨x, hx⟩, rfl, ?_⟩
    have h1 := hI.comm i (c.next i) ⟨x, hx⟩ hex
    have h2 : H'.d i (c.next i) ⟨e i x, hex⟩ = H'.d i (c.next i) y :=
      LinearPMap.apply_congr' _ _ _ hy
    rw [h2, h0] at h1
    exact (e (c.next i)).injective (by rw [← h1, map_zero])
  · rintro ⟨y, rfl, h0⟩
    refine ⟨⟨e i y, (hI.mem_domain_iff _ _ _).2 y.2⟩, rfl, ?_⟩
    rw [hI.comm, h0, map_zero]

theorem mem_boundaries_iff (i : ι) (x : W i) :
    e i x ∈ H'.boundaries i ↔ x ∈ H.boundaries i := by
  simp only [HilbertComplex.boundaries, LinearMap.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    have hz : (e (c.prev i)).symm y ∈ (H.d (c.prev i) i).domain :=
      (hI.symm_mem_domain_iff _ _ _).2 y.2
    refine ⟨⟨_, hz⟩, ?_⟩
    change H.d (c.prev i) i ⟨_, hz⟩ = x
    rw [hI.comm_symm, show H'.d (c.prev i) i y = e i x from hy,
      ContinuousLinearEquiv.symm_apply_apply]
  · rintro ⟨y, rfl⟩
    exact ⟨⟨e (c.prev i) y, (hI.mem_domain_iff _ _ _).2 y.2⟩, hI.comm _ _ _ _⟩

/-! #### Subcomplexes, cochain projections -/

/-- The subcomplex `e⁻¹ S'` of `H` of a subcomplex `S'` of `H'`. -/
def comapSub (S' : H'.Subcomplex) : H.Subcomplex where
  V i := (S'.V i).comap (e i : W i →L[ℝ] W' i).toLinearMap
  le_domain i j x hx := (hI.mem_domain_iff i j x).1 (S'.le_domain i j hx)
  mapsTo i j x hx := by
    change e j (H.d i j ⟨x, _⟩) ∈ S'.V j
    rw [← hI.comm i j ⟨x, _⟩ (S'.le_domain i j hx)]
    exact S'.mapsTo i j _ hx

theorem mem_comapSub_V {S' : H'.Subcomplex} {i : ι} {x : W i} :
    x ∈ (hI.comapSub S').V i ↔ e i x ∈ S'.V i := Iff.rfl

instance (S' : H'.Subcomplex) [∀ i, FiniteDimensional ℝ (S'.V i)] (i : ι) :
    FiniteDimensional ℝ ((hI.comapSub S').V i) := by
  let f : (hI.comapSub S').V i →ₗ[ℝ] S'.V i :=
    { toFun := fun x => ⟨e i (x : W i), x.2⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun a x => Subtype.ext (by simp) }
  exact Module.Finite.of_injective f fun x y hxy =>
    Subtype.ext ((e i).injective (congrArg Subtype.val hxy))

/-- The cochain projection `e⁻¹ π' e` onto a subcomplex `S` of `H` with `S = e⁻¹ S'`. -/
def comapProj {S' : H'.Subcomplex} (S : H.Subcomplex) (hS : ∀ i x, x ∈ S.V i ↔ e i x ∈ S'.V i)
    (P : S'.CochainProjection) : S.CochainProjection where
  π i := ((e i).symm : W' i →L[ℝ] W i).toLinearMap ∘ₗ P.π i ∘ₗ (e i : W i →L[ℝ] W' i).toLinearMap
  mem i x := (hS i _).2 (by
    change e i ((e i).symm _) ∈ _
    rw [ContinuousLinearEquiv.apply_symm_apply]; exact P.mem i _)
  proj i x hx := by
    change (e i).symm (P.π i (e i x)) = x
    rw [P.proj i _ ((hS i x).1 hx), ContinuousLinearEquiv.symm_apply_apply]
  comm i j x := by
    have hx' : e i x ∈ (H'.d i j).domain := (hI.mem_domain_iff _ _ _).2 x.2
    change H.d i j ⟨(e i).symm (P.π i (e i x)), _⟩ = (e j).symm (P.π j (e j (H.d i j x)))
    refine (hI.comm_symm i j ⟨_, S'.le_domain i j (P.mem i (e i x))⟩ _).trans ?_
    exact congrArg (e j).symm ((P.comm i j ⟨_, hx'⟩).trans (congrArg _ (hI.comm i j x hx')))

theorem comapProj_π {S' : H'.Subcomplex} (S : H.Subcomplex) (hS) (P : S'.CochainProjection)
    (i : ι) (x : W i) : (hI.comapProj S hS P).π i x = (e i).symm (P.π i (e i x)) := rfl

/-- `‖e⁻¹ π' e x‖ ≤ ‖e⁻¹‖ C ‖e‖ ‖x‖`. -/
theorem norm_comapProj_le {S' : H'.Subcomplex} (S : H.Subcomplex) (hS)
    (P : S'.CochainProjection) {i : ι} {C M M' : ℝ}
    (hC : 0 ≤ C) (hπ : ∀ y, ‖P.π i y‖ ≤ C * ‖y‖) (hM : ‖(e i : W i →L[ℝ] W' i)‖ ≤ M)
    (hM' : ‖((e i).symm : W' i →L[ℝ] W i)‖ ≤ M') (x : W i) :
    ‖(hI.comapProj S hS P).π i x‖ ≤ M' * C * M * ‖x‖ := by
  rw [comapProj_π]
  have h1 := ((e i).symm : W' i →L[ℝ] W i).le_of_opNorm_le hM' (P.π i (e i x))
  have h2 := (e i : W i →L[ℝ] W' i).le_of_opNorm_le hM x
  have hM'0 : 0 ≤ M' := (norm_nonneg _).trans hM'
  calc ‖(e i).symm (P.π i (e i x))‖ ≤ M' * ‖P.π i (e i x)‖ := h1
    _ ≤ M' * (C * ‖e i x‖) := by gcongr; exact hπ _
    _ ≤ M' * (C * (M * ‖x‖)) := by gcongr; exact h2
    _ = _ := by ring

/-- **Graph bounds transfer**: if `π'` is bounded by `C` in the graph norm of `d'ᵢⱼ`, then
`e⁻¹ π' e` is bounded by `M' C M` in the graph norm of `dᵢⱼ`, `‖e‖ ≤ M`, `‖e⁻¹‖ ≤ M'`. -/
theorem isGraphBounded_comapProj {S' : H'.Subcomplex} (S : H.Subcomplex) (hS)
    (P : S'.CochainProjection) {i j : ι}
    {C M M' : ℝ} (h : P.IsGraphBounded i j C)
    (hM : ∀ k, ‖(e k : W k →L[ℝ] W' k)‖ ≤ M)
    (hM' : ∀ k, ‖((e k).symm : W' k →L[ℝ] W k)‖ ≤ M') :
    (hI.comapProj S hS P).IsGraphBounded i j (M' * C * M) := by
  intro x
  have hx' : e i x ∈ (H'.d i j).domain := (hI.mem_domain_iff _ _ _).2 x.2
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM i)
  have hM'0 : 0 ≤ M' := (norm_nonneg _).trans (hM' i)
  have hb := h ⟨_, hx'⟩
  set y : (H'.d i j).domain := ⟨P.π i (e i x), S'.le_domain i j (P.mem i _)⟩
  have hd : H.d i j ⟨(hI.comapProj S hS P).π i x,
      S.le_domain i j ((hI.comapProj S hS P).mem i x)⟩ = (e j).symm (H'.d i j y) :=
    hI.comm_symm i j y _
  have hdx : H'.d i j ⟨e i x, hx'⟩ = e j (H.d i j x) := hI.comm i j x hx'
  rw [hd, comapProj_π]
  have n1 := ((e i).symm : W' i →L[ℝ] W i).le_of_opNorm_le (hM' i) (P.π i (e i x))
  have n2 := ((e j).symm : W' j →L[ℝ] W j).le_of_opNorm_le (hM' j) (H'.d i j y)
  have n3 := (e i : W i →L[ℝ] W' i).le_of_opNorm_le (hM i) x
  have n4 := (e j : W j →L[ℝ] W' j).le_of_opNorm_le (hM j) (H.d i j x)
  change ‖P.π i (e i x)‖ ^ 2 + ‖H'.d i j y‖ ^ 2 ≤
    C ^ 2 * (‖e i x‖ ^ 2 + ‖H'.d i j ⟨e i x, hx'⟩‖ ^ 2) at hb
  rw [hdx] at hb
  have s1 : ‖(e i).symm (P.π i (e i x))‖ ^ 2 ≤ M' ^ 2 * ‖P.π i (e i x)‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) n1 2
  have s2 : ‖(e j).symm (H'.d i j y)‖ ^ 2 ≤ M' ^ 2 * ‖H'.d i j y‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) n2 2
  have s3 : ‖e i x‖ ^ 2 ≤ M ^ 2 * ‖(x : W i)‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) n3 2
  have s4 : ‖e j (H.d i j x)‖ ^ 2 ≤ M ^ 2 * ‖H.d i j x‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) n4 2
  calc ‖(e i).symm (P.π i (e i x))‖ ^ 2 + ‖(e j).symm (H'.d i j y)‖ ^ 2
      ≤ M' ^ 2 * (‖P.π i (e i x)‖ ^ 2 + ‖H'.d i j y‖ ^ 2) := by nlinarith
    _ ≤ M' ^ 2 * (C ^ 2 * (‖e i x‖ ^ 2 + ‖e j (H.d i j x)‖ ^ 2)) := by gcongr
    _ ≤ M' ^ 2 * (C ^ 2 * (M ^ 2 * ‖(x : W i)‖ ^ 2 + M ^ 2 * ‖H.d i j x‖ ^ 2)) := by gcongr
    _ = (M' * C * M) ^ 2 * (‖(x : W i)‖ ^ 2 + ‖H.d i j x‖ ^ 2) := by ring

/-! #### Poincaré inequalities, harmonic forms, approximation -/

/-- **The Poincaré inequality transfers**: if `‖z‖ ≤ c_P ‖d' z‖` for `z ∈ D(d'ᵢⱼ) ⊥ 𝔷'ⁱ`, then
`‖z‖ ≤ ‖e⁻¹‖ c_P ‖e‖ ‖d z‖` for `z ∈ D(dᵢⱼ) ⊥ 𝔷ⁱ`: project `e z` onto `(𝔷')ᗮ` and pull back;
the correction is a cycle, and `z` is the shortest point of `z + 𝔷ⁱ`. -/
theorem norm_le_of_mem_orthogonal_cycles {i j : ι} (hij : c.Rel i j) {cP M M' : ℝ}
    (hcP : 0 ≤ cP) (hM : ‖(e j : W j →L[ℝ] W' j)‖ ≤ M)
    (hM' : ‖((e i).symm : W' i →L[ℝ] W i)‖ ≤ M')
    (hP : ∀ z : (H'.d i j).domain, (z : W' i) ∈ (H'.cycles i)ᗮ →
      ‖(z : W' i)‖ ≤ cP * ‖H'.d i j z‖)
    (z : (H.d i j).domain) (hz : (z : W i) ∈ (H.cycles i)ᗮ) :
    ‖(z : W i)‖ ≤ M' * cP * M * ‖H.d i j z‖ := by
  have hw : e i z ∈ (H'.d i j).domain := (hI.mem_domain_iff _ _ _).2 z.2
  set p := (H'.cycles i).starProjection (e i z)
  have hp : p ∈ H'.cycles i := Submodule.starProjection_apply_mem _ _
  have hpk : p ∈ (H'.d i j).ker := by rw [← H'.cycles_eq hij]; exact hp
  obtain ⟨pd, hpd, hp0⟩ := LinearPMap.mem_ker_iff.1 hpk
  set w' : (H'.d i j).domain := ⟨e i z, hw⟩ - pd
  have hw'v : (w' : W' i) = e i z - p := by simp [w', hpd]
  have hdw' : H'.d i j w' = e j (H.d i j z) := by
    rw [LinearPMap.map_sub, hp0, sub_zero, hI.comm]
  have hw'o : (w' : W' i) ∈ (H'.cycles i)ᗮ := by
    rw [hw'v]; exact Submodule.sub_starProjection_mem_orthogonal _
  have h1 := hP w' hw'o
  rw [hdw'] at h1
  set ζ := (e i).symm p
  have hζ : ζ ∈ H.cycles i := (hI.mem_cycles_iff i ζ).1 (by
    rw [ContinuousLinearEquiv.apply_symm_apply]; exact hp)
  have hzζ : (z : W i) - ζ = (e i).symm w' := by
    rw [hw'v, map_sub, ContinuousLinearEquiv.symm_apply_apply]
  have h0 : ⟪ζ, (z : W i)⟫_ℝ = 0 := Submodule.inner_right_of_mem_orthogonal hζ hz
  have h2 : ‖(z : W i)‖ ≤ ‖(z : W i) - ζ‖ := by
    have : ‖(z : W i) - ζ‖ ^ 2 = ‖(z : W i)‖ ^ 2 + ‖ζ‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_comm, h0]; ring
    nlinarith [norm_nonneg ζ, norm_nonneg ((z : W i) - ζ), norm_nonneg (z : W i)]
  have h3 := ((e i).symm : W' i →L[ℝ] W i).le_of_opNorm_le hM' (w' : W' i)
  have h4 := (e j : W j →L[ℝ] W' j).le_of_opNorm_le hM (H.d i j z)
  have hM'0 : 0 ≤ M' := (norm_nonneg _).trans hM'
  calc ‖(z : W i)‖ ≤ ‖(z : W i) - ζ‖ := h2
    _ = ‖(e i).symm w'‖ := by rw [hzζ]
    _ ≤ M' * ‖(w' : W' i)‖ := h3
    _ ≤ M' * (cP * ‖e j (H.d i j z)‖) := by gcongr
    _ ≤ M' * (cP * (M * ‖H.d i j z‖)) := by gcongr; exact h4
    _ = _ := by ring

/-- **The map `x ↦ P_{ℌ'} (e x)` is injective on `ℌⁱ`**: `e x ⊥ ℌ'` forces `e x ∈ cl 𝔅'`, so
`x ∈ cl 𝔅 ∩ ℌ = 0`. -/
theorem injective_harmonic (j : ι) [CompleteSpace (H'.harmonic j)] :
    Function.Injective ((H'.harmonic j).orthogonalProjectionOnto.toLinearMap ∘ₗ
      (e j : W j →L[ℝ] W' j).toLinearMap ∘ₗ (H.harmonic j).subtype) := by
  intro x y hxy
  rw [← sub_eq_zero] at hxy ⊢
  rw [← map_sub] at hxy
  set u : H.harmonic j := x - y
  have hu : (u : W j) ∈ H.harmonic j := u.2
  have hy0 : e j (u : W j) ∈ (H'.harmonic j)ᗮ := by
    rw [← Submodule.orthogonalProjectionOnto_eq_zero_iff]; exact hxy
  have hyz : e j (u : W j) ∈ H'.cycles j :=
    (hI.mem_cycles_iff j _).2 ((H.mem_harmonic_iff.1 hu).1)
  rw [← H'.closure_boundaries_sup_harmonic j, Submodule.mem_sup] at hyz
  obtain ⟨b, hb, h, hh, hbh⟩ := hyz
  have hh0 : h = 0 := by
    have e1 : ⟪h, e j (u : W j)⟫_ℝ = 0 := Submodule.inner_right_of_mem_orthogonal hh hy0
    have e2 : ⟪h, b⟫_ℝ = 0 :=
      (H'.isOrtho_closure_boundaries_harmonic j).symm.inner_eq hh hb
    rw [← hbh, inner_add_right, e2, zero_add] at e1
    exact inner_self_eq_zero.1 e1
  rw [hh0, add_zero] at hbh
  -- `u = e⁻¹ b ∈ cl 𝔅`
  have hcl : (u : W j) ∈ (H.boundaries j).topologicalClosure := by
    have hb' : b ∈ closure (H'.boundaries j : Set (W' j)) := by
      rwa [← Submodule.topologicalClosure_coe]
    have hmem := mem_closure_image (((e j).symm : W' j →L[ℝ] W j).continuous.continuousAt) hb'
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    refine closure_mono ?_ (by rwa [hbh, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] at hmem)
    rintro _ ⟨v, hv, rfl⟩
    exact (hI.mem_boundaries_iff j _).1 (by
      rw [ContinuousLinearEquiv.apply_symm_apply]; exact hv)
  have horth : (u : W j) ∈ (H.boundaries j).topologicalClosureᗮ := by
    rw [H.orthogonal_closure_boundaries]; exact (H.mem_harmonic_iff.1 hu).2
  exact Subtype.ext (inner_self_eq_zero.1
    (Submodule.inner_right_of_mem_orthogonal hcl horth))

/-- **Finite-dimensional harmonic forms transfer** (`injective_harmonic`). -/
theorem finiteDimensional_harmonic (j : ι) [FiniteDimensional ℝ (H'.harmonic j)] :
    FiniteDimensional ℝ (H.harmonic j) := by
  have : CompleteSpace (H'.harmonic j) := (H'.isClosed_harmonic j).completeSpace_coe
  exact Module.Finite.of_injective _ (hI.injective_harmonic j)

/-- **Degreewise graph-norm approximation transfers**: a `v' ∈ S'ⁱ` within `ε` of `e x` (and
`d' (e x - v')` within `ε`) gives `v = e⁻¹ v' ∈ (e⁻¹ S')ⁱ` within `M' ε` of `x`. -/
theorem exists_near_comapSub {S' : H'.Subcomplex} (S : H.Subcomplex)
    (hS : ∀ i x, x ∈ S.V i ↔ e i x ∈ S'.V i) {M' : ℝ}
    (hM' : ∀ k, ‖((e k).symm : W' k →L[ℝ] W k)‖ ≤ M') {i : ι} {x : W i} {ε : ℝ}
    {v' : W' i} (hv' : v' ∈ S'.V i) (h1 : ‖e i x - v'‖ ≤ ε)
    (h2 : ∀ j (hx : e i x ∈ (H'.d i j).domain),
      ‖H'.d i j ⟨e i x - v', Submodule.sub_mem _ hx (S'.le_domain i j hv')⟩‖ ≤ ε) :
    ∃ v, ∃ hv : v ∈ S.V i, ‖x - v‖ ≤ M' * ε ∧
      ∀ j (hx : x ∈ (H.d i j).domain),
        ‖H.d i j ⟨x - v, Submodule.sub_mem _ hx (S.le_domain i j hv)⟩‖ ≤ M' * ε := by
  have hv : (e i).symm v' ∈ S.V i :=
    (hS i _).2 (by rw [ContinuousLinearEquiv.apply_symm_apply]; exact hv')
  have hxv : x - (e i).symm v' = (e i).symm (e i x - v') := by
    rw [map_sub, ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨_, hv, ?_, fun j hx => ?_⟩
  · rw [hxv]
    exact (((e i).symm : W' i →L[ℝ] W i).le_of_opNorm_le (hM' i) _).trans
      (mul_le_mul_of_nonneg_left h1 ((norm_nonneg _).trans (hM' i)))
  · have hx' : e i x ∈ (H'.d i j).domain := (hI.mem_domain_iff _ _ _).2 hx
    set y : (H'.d i j).domain := ⟨e i x - v', Submodule.sub_mem _ hx' (S'.le_domain i j hv')⟩
    have hy : (e i).symm (y : W' i) ∈ (H.d i j).domain := by
      rw [← hxv]; exact Submodule.sub_mem _ hx (S.le_domain i j hv)
    have e1 : H.d i j ⟨x - (e i).symm v', Submodule.sub_mem _ hx
        (S.le_domain i j hv)⟩ = H.d i j ⟨(e i).symm y, hy⟩ :=
      LinearPMap.apply_congr' _ _ _ hxv
    rw [e1, hI.comm_symm]
    exact (((e j).symm : W' j →L[ℝ] W j).le_of_opNorm_le (hM' j) _).trans
      (mul_le_mul_of_nonneg_left (h2 j hx') ((norm_nonneg _).trans (hM' j)))

/-- **Eventual degreewise approximation transfers** (the hypothesis of
`Feec.HilbertComplex.Subcomplex.eventually_exists_graphSub_lt`). -/
theorem eventually_near_comapSub {κ : Type*} {l : Filter κ} {S' : κ → H'.Subcomplex}
    (S : κ → H.Subcomplex) (hS : ∀ N i x, x ∈ (S N).V i ↔ e i x ∈ (S' N).V i) {M' : ℝ}
    (hM' : ∀ k, ‖((e k).symm : W' k →L[ℝ] W k)‖ ≤ M')
    (h' : ∀ i (x' : W' i) (ε : ℝ), 0 < ε → ∀ᶠ N in l, ∃ v, ∃ hv : v ∈ (S' N).V i,
      ‖x' - v‖ < ε ∧ ∀ j (hx : x' ∈ (H'.d i j).domain),
        ‖H'.d i j ⟨x' - v, Submodule.sub_mem _ hx ((S' N).le_domain i j hv)⟩‖ < ε) :
    ∀ i (x : W i) (ε : ℝ), 0 < ε → ∀ᶠ N in l, ∃ v, ∃ hv : v ∈ (S N).V i,
      ‖x - v‖ < ε ∧ ∀ j (hx : x ∈ (H.d i j).domain),
        ‖H.d i j ⟨x - v, Submodule.sub_mem _ hx ((S N).le_domain i j hv)⟩‖ < ε := by
  intro i x ε hε
  have hM'0 : 0 ≤ M' := (norm_nonneg _).trans (hM' i)
  set ε' := ε / (M' + 1)
  have hε' : 0 < ε' := div_pos hε (by linarith)
  have hlt : M' * ε' < ε := by
    rw [show M' * ε' = M' / (M' + 1) * ε by simp only [ε']; ring]
    have : M' / (M' + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
    nlinarith
  filter_upwards [h' i (e i x) ε' hε'] with N hN
  obtain ⟨v', hv', h1, h2⟩ := hN
  obtain ⟨v, hv, hv1, hv2⟩ := hI.exists_near_comapSub (S N) (hS N) hM' hv' h1.le
    fun j hx => (h2 j hx).le
  exact ⟨v, hv, hv1.trans_lt hlt, fun j hx => (hv2 j hx).trans_lt hlt⟩

omit hI in
/-- **`L²` approximation transfers**: if `dist(x', S'ⁱ_N) → 0` for every `x'`, then
`dist(x, (e⁻¹ S'_N)ⁱ) → 0` for every `x`. -/
theorem tendsto_infDist_comapSub {κ : Type*} {l : Filter κ} {S' : κ → H'.Subcomplex}
    (S : κ → H.Subcomplex) (hS : ∀ N i x, x ∈ (S N).V i ↔ e i x ∈ (S' N).V i) {i : ι}
    (h' : ∀ x' : W' i, Tendsto (fun N => Metric.infDist x' ((S' N).V i : Set (W' i))) l (𝓝 0))
    (x : W i) :
    Tendsto (fun N => Metric.infDist x ((S N).V i : Set (W i))) l (𝓝 0) := by
  set M' := ‖((e i).symm : W' i →L[ℝ] W i)‖
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun N =>
    ha.trans_le Metric.infDist_nonneg, fun a ha => ?_⟩
  set ε' := a / (M' + 1)
  have hε' : 0 < ε' := div_pos ha (by positivity)
  have hlt : M' * ε' < a := by
    rw [show M' * ε' = M' / (M' + 1) * a by simp only [ε']; ring]
    have : M' / (M' + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith
  filter_upwards [(tendsto_order.1 (h' (e i x))).2 ε' hε'] with N hN
  obtain ⟨v', hv', hd⟩ := (Metric.infDist_lt_iff ⟨0, (S' N).V i |>.zero_mem⟩).1 hN
  have hv : (e i).symm v' ∈ (S N).V i :=
    (hS N i _).2 (by rw [ContinuousLinearEquiv.apply_symm_apply]; exact hv')
  refine (Metric.infDist_le_dist_of_mem hv).trans_lt (lt_of_le_of_lt ?_ hlt)
  rw [dist_eq_norm, show x - (e i).symm v' = (e i).symm (e i x - v') by
    rw [map_sub, ContinuousLinearEquiv.symm_apply_apply]]
  refine (((e i).symm : W' i →L[ℝ] W i).le_opNorm _).trans ?_
  rw [← dist_eq_norm]
  exact mul_le_mul_of_nonneg_left hd.le (norm_nonneg _)

/-- The inverse of an isomorphism of Hilbert complexes. -/
theorem symm : IsChainIso H' H fun i => (e i).symm where
  mem_domain_iff i j y := hI.symm_mem_domain_iff i j y
  comm i j y h := hI.comm_symm i j y h

/-- **The harmonic forms of isomorphic complexes have the same dimension.** -/
theorem finrank_harmonic_eq (j : ι) [FiniteDimensional ℝ (H'.harmonic j)] :
    Module.finrank ℝ (H.harmonic j) = Module.finrank ℝ (H'.harmonic j) := by
  have := hI.finiteDimensional_harmonic j
  have : CompleteSpace (H'.harmonic j) := (H'.isClosed_harmonic j).completeSpace_coe
  have : CompleteSpace (H.harmonic j) := (H.isClosed_harmonic j).completeSpace_coe
  -- both injections `x ↦ P_ℌ (e x)` of `finiteDimensional_harmonic`
  refine le_antisymm ?_ ?_
  · obtain ⟨Φ, hΦ⟩ : ∃ Φ : H.harmonic j →ₗ[ℝ] H'.harmonic j, Function.Injective Φ := by
      refine ⟨(H'.harmonic j).orthogonalProjectionOnto.toLinearMap ∘ₗ
        (e j : W j →L[ℝ] W' j).toLinearMap ∘ₗ (H.harmonic j).subtype, ?_⟩
      exact hI.injective_harmonic j
    exact LinearMap.finrank_le_finrank_of_injective hΦ
  · obtain ⟨Φ, hΦ⟩ : ∃ Φ : H'.harmonic j →ₗ[ℝ] H.harmonic j, Function.Injective Φ := by
      refine ⟨(H.harmonic j).orthogonalProjectionOnto.toLinearMap ∘ₗ
        ((e j).symm : W' j →L[ℝ] W j).toLinearMap ∘ₗ (H'.harmonic j).subtype, ?_⟩
      exact hI.symm.injective_harmonic j
    exact LinearMap.finrank_le_finrank_of_injective hΦ

end IsChainIso

end Feec.HilbertComplex

/-! ### The parallelepiped `A · Q + b` and the pullback of forms -/

namespace Feec.Models.Parallelepiped

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex Feec.ExteriorFibre
open Feec.Models.Cube

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ)

/-- **The parallelepiped** `Ω = A · Q + b`, `Q = (0, ½)ⁿ`, written as `T⁻¹`-preimage of `Q`
(`domain_eq_image`); every open box `∏ᵢ (aᵢ, bᵢ)` is one (`domain_diag`). -/
def domain : Set (Fin n → ℝ) := affMap A⁻¹ (affInvShift A b) ⁻¹' FEM.cubeDomain n

theorem isOpen_domain : IsOpen (domain A b) :=
  (FEM.isOpen_cubeDomain n).preimage (continuous_affMap _ _)

include hA in
theorem preimage_domain : affMap A b ⁻¹' domain A b = FEM.cubeDomain n :=
  preimage_preimage_inv b hA _

include hA in
theorem domain_eq_image : domain A b = affMap A b '' FEM.cubeDomain n := by
  ext y
  constructor
  · intro hy
    exact ⟨affMap A⁻¹ (affInvShift A b) y, hy, affMap_affMap_inv b hA y⟩
  · rintro ⟨x, hx, rfl⟩
    change affMap A⁻¹ (affInvShift A b) (affMap A b x) ∈ FEM.cubeDomain n
    rwa [affMap_inv_affMap b hA]

include hA in
theorem isBounded_domain : Bornology.IsBounded (domain A b) := by
  rw [domain_eq_image A hA b]
  exact ((FEM.isCompact_closure_cubeDomain n).image (continuous_affMap A b)).isBounded.subset
    (Set.image_mono subset_closure)

/-- `T x = A x + b` as an affine equivalence of `ℝⁿ`. -/
def affEquiv : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ) where
  toEquiv := (affHomeo b hA).toEquiv
  linear := LinearEquiv.ofLinearMap (Matrix.toLin' A) (Matrix.toLin' A⁻¹)
    (LinearMap.ext fun x => by
      simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA])
    (LinearMap.ext fun x => by
      simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA])
  map_vadd' p v := by
    change affMap A b (v + p) = Matrix.toLin' A v + affMap A b p
    simp [affMap, Matrix.mulVec_add, add_assoc]

@[simp] theorem coe_affEquiv : ⇑(affEquiv A hA b) = affMap A b := rfl

@[simp] theorem coe_affEquiv_symm :
    ⇑(affEquiv A hA b).symm = affMap A⁻¹ (affInvShift A b) := rfl

include hA in
theorem convex_domain : Convex ℝ (domain A b) := by
  have h := (FEM.convex_cubeDomain n).affine_preimage (affEquiv A hA b).symm.toAffineMap
  simpa [domain] using h

/-- **The pullback of forms** `T^* : L²(Ω; Λᵏ) ≃ L²(Q; Λᵏ)`,
`(T^* u)_s = Σ_t minor_{ts}(A) u_t ∘ T` (`Feec.FiniteElement.affinePullback` pointwise,
`pullFun_minorMat`). -/
def pullEquiv (k : ℤ) :
    L2F ℝ (domain A b) (formIdx n k) ≃L[ℝ] L2F ℝ (FEM.cubeDomain n) (formIdx n k) :=
  (formPullData A hA).equiv hA b (isOpen_domain A b) (preimage_domain A hA b) k

theorem pullEquiv_apply (k : ℤ) (u : L2F ℝ (domain A b) (formIdx n k)) :
    pullEquiv A hA b k u = fieldPull hA b (isOpen_domain A b).measurableSet
      (preimage_domain A hA b) (minorMat A k) u := rfl

/-- `HΛ(Ω)`, the maximal `L²` de Rham complex of the parallelepiped. -/
abbrev complex : HilbertComplex ℝ (ComplexShape.up ℤ) fun k => L2F ℝ (domain A b) (formIdx n k) :=
  (deRham ℝ n).maximalComplex (isOpen_domain A b)

/-- `H̊Λ(Ω)`, the minimal `L²` de Rham complex of the parallelepiped. -/
abbrev complexMin :
    HilbertComplex ℝ (ComplexShape.up ℤ) fun k => L2F ℝ (domain A b) (formIdx n k) :=
  (deRham ℝ n).minimalComplex (isOpen_domain A b)

/-- **`HΛ(Q)` is the transport of `HΛ(Ω)` along `T^*`.** -/
theorem complex_cube_eq_transport : FEM.complex n = (complex A b).transport (pullEquiv A hA b)
    (fun _ _ => 1) fun _ _ => one_ne_zero :=
  (formPullData A hA).maximalComplex_eq_transport hA b (FEM.isOpen_cubeDomain n)
    (isOpen_domain A b) (preimage_domain A hA b)

/-- **`H̊Λ(Q)` is the transport of `H̊Λ(Ω)` along `T^*`.** -/
theorem complexMin_cube_eq_transport : FEM.complexMin n = (complexMin A b).transport
    (pullEquiv A hA b) (fun _ _ => 1) fun _ _ => one_ne_zero :=
  (formPullData A hA).minimalComplex_eq_transport hA b (FEM.isOpen_cubeDomain n)
    (isOpen_domain A b) (preimage_domain A hA b)

/-- **`T^*` is an isomorphism of Hilbert complexes `HΛ(Ω) ≅ HΛ(Q)`.** -/
theorem isChainIso : IsChainIso (complex A b) (FEM.complex n) (pullEquiv A hA b) := by
  rw [complex_cube_eq_transport A hA b]; exact isChainIso_transport _ _

/-- **`T^*` is an isomorphism of Hilbert complexes `H̊Λ(Ω) ≅ H̊Λ(Q)`.** -/
theorem isChainIsoMin : IsChainIso (complexMin A b) (FEM.complexMin n) (pullEquiv A hA b) := by
  rw [complexMin_cube_eq_transport A hA b]; exact isChainIso_transport _ _

/-! #### Explicit constants -/

/-- The constant `|det A|^{-1/2} Σ_{s,t ⊆ Fin n} |minor_{ts}(A)|` bounding `T^*` in every
degree; the minors are bounded by `k! ‖A‖_max^k` (`abs_wedgeProd_rows_le`). -/
def pullConst : ℝ :=
  Real.sqrt |A.det|⁻¹ * ∑ s : Finset (Fin n), ∑ t : Finset (Fin n), |wedgeProd (rows A) t s|

theorem pullConst_nonneg : 0 ≤ pullConst A :=
  mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    abs_nonneg _)

/-- A sum of nonnegative terms over a subtype is at most the full sum. -/
theorem sum_subtype_le_sum {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) : ∑ a : {a // p a}, f a ≤ ∑ a, f a := by
  rw [← Fintype.sum_subtype_add_sum_subtype p f]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun a _ => hf a)

theorem sum_minorMat_le (k : ℤ) :
    ∑ s : formIdx n k, ∑ t : formIdx n k, |minorMat A k s t| ≤
      ∑ s : Finset (Fin n), ∑ t : Finset (Fin n), |wedgeProd (rows A) t s| := by
  calc ∑ s : formIdx n k, ∑ t : formIdx n k, |minorMat A k s t|
      ≤ ∑ s : formIdx n k, ∑ t : Finset (Fin n), |wedgeProd (rows A) t s.1| :=
        Finset.sum_le_sum fun s _ => sum_subtype_le_sum (fun t : Finset (Fin n) => (#t : ℤ) = k)
          (f := fun t => |wedgeProd (rows A) t s.1|) fun _ => abs_nonneg _
    _ ≤ _ := sum_subtype_le_sum (fun s : Finset (Fin n) => (#s : ℤ) = k)
        (f := fun s => ∑ t : Finset (Fin n), |wedgeProd (rows A) t s|)
        fun _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- `‖T^*‖ ≤ pullConst A` in every degree. -/
theorem norm_pullEquiv_le (k : ℤ) :
    ‖(pullEquiv A hA b k : L2F ℝ (domain A b) (formIdx n k) →L[ℝ]
      L2F ℝ (FEM.cubeDomain n) (formIdx n k))‖ ≤ pullConst A := by
  refine ContinuousLinearMap.opNorm_le_bound _ (pullConst_nonneg A) fun u => ?_
  refine ((formPullData A hA).norm_equiv_le hA b (isOpen_domain A b) (preimage_domain A hA b) k
    u).trans ?_
  gcongr
  exact mul_le_mul_of_nonneg_left (sum_minorMat_le A k) (Real.sqrt_nonneg _)

/-- `‖(T^*)⁻¹‖ ≤ pullConst A⁻¹` in every degree. -/
theorem norm_pullEquiv_symm_le (k : ℤ) :
    ‖((pullEquiv A hA b k).symm : L2F ℝ (FEM.cubeDomain n) (formIdx n k) →L[ℝ]
      L2F ℝ (domain A b) (formIdx n k))‖ ≤ pullConst A⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (pullConst_nonneg A⁻¹) fun u => ?_
  refine ((formPullData A hA).norm_equiv_symm_le hA b (isOpen_domain A b)
    (preimage_domain A hA b) k u).trans ?_
  gcongr
  exact mul_le_mul_of_nonneg_left (sum_minorMat_le A⁻¹ k) (Real.sqrt_nonneg _)

/-- The minors of `A` are bounded by `k! ‖A‖_max^k` (Leibniz), so `pullConst A` is bounded in
terms of `‖A‖_max` and `|det A|`. -/
theorem abs_wedgeProd_rows_le {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i j, |A i j| ≤ M)
    (t s : Finset (Fin n)) :
    |wedgeProd (rows A) t s| ≤ (#t).factorial * M ^ #t := by
  by_cases hts : #s = #t
  · rw [wedgeProd_apply_eq_det_submatrix (rows A) rfl hts]
    have := Matrix.det_le (A := Matrix.of fun i j : Fin #t => rows A (t.orderEmbOfFin rfl i)
      (s.orderEmbOfFin hts j)) (abv := AbsoluteValue.abs) (x := M) fun i j => hM _ _
    simpa [Fintype.card_fin, nsmul_eq_mul] using this
  · rw [isDeg_wedgeProd (rows A) t s hts, abs_zero]
    positivity

/-! ### Images of meshes -/

section MeshMap

open Classical in
theorem vertexSet_mapEquiv_eq_image (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ)) {k : ℕ}
    (T : Affine.Simplex ℝ (Fin n → ℝ) k) : vertexSet (mapEquiv e T) = (vertexSet T).image e := by
  apply Finset.coe_injective
  rw [vertexSet_mapEquiv, Finset.coe_image]

open Classical in
theorem image_subset_vertexSet_mapEquiv_iff (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ))
    {g : Finset (Fin n → ℝ)} {T : Affine.Simplex ℝ (Fin n → ℝ) n} :
    g.image e ⊆ vertexSet (mapEquiv e T) ↔ g ⊆ vertexSet T := by
  rw [vertexSet_mapEquiv_eq_image, Finset.image_subset_image_iff e.injective]

theorem mapEquiv_mem_map (M : SimplicialMesh n) (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ))
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ M.simplices) :
    mapEquiv e T ∈ (M.map e).simplices :=
  (M.mem_map_simplices).2 ⟨T, hT, rfl⟩

open Classical in
theorem cofaces_map (M : SimplicialMesh n) (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ))
    (F : Finset (Fin n → ℝ)) :
    (M.map e).cofaces (F.image e) = (M.cofaces F).image (mapEquiv e) := by
  ext T'
  simp only [SimplicialMesh.mem_cofaces, Finset.mem_image, SimplicialMesh.mem_map_simplices]
  constructor
  · rintro ⟨⟨T, hT, rfl⟩, hF⟩
    exact ⟨T, ⟨hT, (image_subset_vertexSet_mapEquiv_iff e).1 hF⟩, rfl⟩
  · rintro ⟨T, ⟨hT, hF⟩, rfl⟩
    exact ⟨⟨T, hT, rfl⟩, (image_subset_vertexSet_mapEquiv_iff e).2 hF⟩

open Classical in
/-- **Boundary facets are mapped to boundary facets.** -/
theorem isBoundaryFacet_map (M : SimplicialMesh n) (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ))
    {F : Finset (Fin n → ℝ)} (hF : M.IsBoundaryFacet F) :
    (M.map e).IsBoundaryFacet (F.image e) := by
  rw [SimplicialMesh.isBoundaryFacet_iff] at hF ⊢
  obtain ⟨⟨hc, T, hT, hFT⟩, h1⟩ := hF
  refine ⟨⟨by rw [Finset.card_image_of_injective _ e.injective]; exact hc, mapEquiv e T,
    mapEquiv_mem_map M e hT, (image_subset_vertexSet_mapEquiv_iff e).2 hFT⟩, ?_⟩
  rw [cofaces_map, Finset.card_image_of_injective _ (mapEquiv_injective e), h1]

theorem interior_closedInterior_mapEquiv (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ))
    (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    interior (mapEquiv e T).closedInterior = e '' interior T.closedInterior := by
  rw [closedInterior_mapEquiv]
  exact ((AffineEquiv.toContinuousAffineEquiv e).toHomeomorph.image_interior _).symm

/-- Two meshes with the same simplices and domain are equal. -/
theorem SimplicialMesh.ext_of {M M' : SimplicialMesh n} (hs : M.simplices = M'.simplices)
    (hd : M.domain = M'.domain) : M = M' := by
  cases M; cases M'; subst hs hd; rfl

/-- Mapping by `e` and then by a left inverse `e'` gives back the mesh. -/
theorem map_map_of_leftInverse (M : SimplicialMesh n) (e e' : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ))
    (h : ∀ x, e' (e x) = x) : (M.map e).map e' = M := by
  have hT : ∀ T : Affine.Simplex ℝ (Fin n → ℝ) n, mapEquiv e' (mapEquiv e T) = T := fun T =>
    Affine.Simplex.ext fun i => by simp [h]
  refine SimplicialMesh.ext_of ?_ ?_
  · ext T
    simp only [SimplicialMesh.mem_map_simplices]
    constructor
    · rintro ⟨_, ⟨T', hT', rfl⟩, rfl⟩
      rwa [hT]
    · intro hTm
      exact ⟨mapEquiv e T, ⟨T, hTm, rfl⟩, hT T⟩
  · simp only [SimplicialMesh.map_domain, Set.image_image, h, Set.image_id']

end MeshMap

/-! ### Affine invariance of the Whitney spaces -/

section WhitneyInvariance

/-- A sum over all subsets of a degree-`k` coefficient vector is a sum over the `k`-subsets. -/
theorem sum_isDeg_mul {k : ℕ} {α : Finset (Fin n) → ℝ} (hα : IsDeg k α)
    (g : Finset (Fin n) → ℝ) :
    ∑ t, α t * g t = ∑ t : formIdx n (k : ℤ), α t.1 * g t.1 := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun t : Finset (Fin n) => (#t : ℤ) = (k : ℤ))]
  rw [Fintype.sum_eq_zero (fun t : {t : Finset (Fin n) // ¬ (#t : ℤ) = (k : ℤ)} => _) fun t => by
    rw [hα t.1 (fun h => t.2 (by rw [h])), zero_mul], add_zero]

open Classical in
/-- **The face integrals are affine invariant up to orientation**: for a `k`-face `g`,
`∫_g T^* w = ε_g ∫_{T(g)} w` with a sign `ε_g` depending only on `g` (the enumerations of `T(g)`
by `T ∘ faceEnum g` and `faceEnum (T g)` differ by a permutation). -/
theorem exists_whitneyFaceDof_affinePullback {g : Finset (Fin n → ℝ)} {k : ℕ}
    (hg : g.card = k + 1) : ∃ ε : ℝ, ∀ w : contForms n,
      whitneyFaceDof g k ⟨affinePullback (rows A) b (w : FormField n),
        continuous_affinePullback _ _ (mem_contForms.1 w.2)⟩ =
      ε * whitneyFaceDof (g.image (affEquiv A hA b)) k w := by
  set e := affEquiv A hA b
  set q := faceEnum g (k + 1)
  have hq : Function.Injective q := injective_faceEnum hg
  have hc : (g.image e).card = k + 1 := by
    rw [Finset.card_image_of_injective _ e.injective, hg]
  have hinj : Function.Injective fun i => affine (rows A) b (q i) := by
    intro i j hij
    simp only [affine_rows] at hij
    exact hq (e.injective hij)
  have hran : Set.range (fun i => affine (rows A) b (q i)) =
      Set.range (faceEnum (g.image e) (k + 1)) := by
    rw [range_faceEnum hc, Finset.coe_image, ← range_faceEnum hg, ← Set.range_comp]
    simp only [affine_rows]
    rfl
  obtain ⟨ε, -, hε⟩ := exists_sign_simplexIntegral_eq hinj (injective_faceEnum hc) hran
  refine ⟨ε, fun w => ?_⟩
  rw [whitneyFaceDof_apply, whitneyFaceDof_apply, ← hε w, simplexIntegral_comp_affine]

variable (M : SimplicialMesh n)

/-- The elementwise pullback of a piecewise Whitney field on `T(M)` to `M`. -/
def pullPiecewise (k : ℕ) (u : (whitneyElement n).Piecewise (M.map (affEquiv A hA b)) k) :
    (whitneyElement n).Piecewise M k := fun T =>
  ⟨affinePullback (rows A) b
    (u ⟨mapEquiv (affEquiv A hA b) T, mapEquiv_mem_map M _ T.2⟩ : FormField n), by
    have h1 := (u ⟨mapEquiv (affEquiv A hA b) T, mapEquiv_mem_map M _ T.2⟩).2
    change _ ∈ whitneySpace _ k at h1
    change _ ∈ whitneySpace _ k
    rw [whitneySpace_eq_p1MinusForms] at h1 ⊢
    exact affinePullback_mem_p1MinusForms _ _ h1⟩

theorem pullPiecewise_apply (k : ℕ) (u : (whitneyElement n).Piecewise (M.map (affEquiv A hA b)) k)
    (T : M.simplices) :
    (pullPiecewise A hA b M k u T : FormField n) = affinePullback (rows A) b
      (u ⟨mapEquiv (affEquiv A hA b) T, mapEquiv_mem_map M _ T.2⟩ : FormField n) := rfl

open Classical in
/-- **Global Whitney fields pull back to global Whitney fields**: the DOFs of the faces transform
by the signs of `exists_whitneyFaceDof_affinePullback`. -/
theorem pullPiecewise_mem_globalSpace {k : ℕ}
    {u : (whitneyElement n).Piecewise (M.map (affEquiv A hA b)) k}
    (hu : u ∈ (whitneyElement n).globalSpace (M.map (affEquiv A hA b)) k) :
    pullPiecewise A hA b M k u ∈ (whitneyElement n).globalSpace M k := by
  intro T T' g hg hg' i
  obtain ⟨ε, hε⟩ := exists_whitneyFaceDof_affinePullback A hA b i.2
  have hc : (g.image (affEquiv A hA b)).card = k + 1 := by
    rw [Finset.card_image_of_injective _ (affEquiv A hA b).injective, i.2]
  have h1 := hε ⟨(u ⟨mapEquiv (affEquiv A hA b) T, mapEquiv_mem_map M _ T.2⟩ : FormField n),
    (whitneyElement n).le_contForms _ k (u ⟨_, mapEquiv_mem_map M _ T.2⟩).2⟩
  have h2 := hε ⟨(u ⟨mapEquiv (affEquiv A hA b) T', mapEquiv_mem_map M _ T'.2⟩ : FormField n),
    (whitneyElement n).le_contForms _ k (u ⟨_, mapEquiv_mem_map M _ T'.2⟩).2⟩
  have h3 : whitneyFaceDof (g.image (affEquiv A hA b)) k
      ⟨(u ⟨mapEquiv (affEquiv A hA b) T, mapEquiv_mem_map M _ T.2⟩ : FormField n),
        (whitneyElement n).le_contForms _ k (u ⟨_, mapEquiv_mem_map M _ T.2⟩).2⟩ =
      whitneyFaceDof (g.image (affEquiv A hA b)) k
      ⟨(u ⟨mapEquiv (affEquiv A hA b) T', mapEquiv_mem_map M _ T'.2⟩ : FormField n),
        (whitneyElement n).le_contForms _ k (u ⟨_, mapEquiv_mem_map M _ T'.2⟩).2⟩ :=
    hu ⟨_, mapEquiv_mem_map M _ T.2⟩ ⟨_, mapEquiv_mem_map M _ T'.2⟩ (g.image (affEquiv A hA b))
      ((image_subset_vertexSet_mapEquiv_iff _).2 hg) ((image_subset_vertexSet_mapEquiv_iff _).2 hg')
      ⟨(), hc⟩
  rw [h3] at h1
  exact h1.trans h2.symm

open Classical in
/-- **Vanishing boundary DOFs pull back**: boundary facets of `M` are mapped to boundary facets
of `T(M)` (`isBoundaryFacet_map`). -/
theorem pullPiecewise_mem_globalSpace₀ {k : ℕ}
    {u : (whitneyElement n).Piecewise (M.map (affEquiv A hA b)) k}
    (hu : u ∈ (whitneyElement n).globalSpace₀ (M.map (affEquiv A hA b)) k) :
    pullPiecewise A hA b M k u ∈ (whitneyElement n).globalSpace₀ M k := by
  refine ⟨pullPiecewise_mem_globalSpace A hA b M hu.1, fun T F hF hFT g hg i => ?_⟩
  obtain ⟨ε, hε⟩ := exists_whitneyFaceDof_affinePullback A hA b i.2
  have hc : (g.image (affEquiv A hA b)).card = k + 1 := by
    rw [Finset.card_image_of_injective _ (affEquiv A hA b).injective, i.2]
  have h1 := hε ⟨(u ⟨mapEquiv (affEquiv A hA b) T, mapEquiv_mem_map M _ T.2⟩ : FormField n),
    (whitneyElement n).le_contForms _ k (u ⟨_, mapEquiv_mem_map M _ T.2⟩).2⟩
  have h0 : whitneyFaceDof (g.image (affEquiv A hA b)) k
      ⟨(u ⟨mapEquiv (affEquiv A hA b) T, mapEquiv_mem_map M _ T.2⟩ : FormField n),
        (whitneyElement n).le_contForms _ k (u ⟨_, mapEquiv_mem_map M _ T.2⟩).2⟩ = 0 :=
    hu.2 ⟨_, mapEquiv_mem_map M _ T.2⟩ (F.image (affEquiv A hA b))
      (isBoundaryFacet_map M _ hF) ((image_subset_vertexSet_mapEquiv_iff _).2 hFT)
      (g.image (affEquiv A hA b)) (Finset.image_subset_image hg) ⟨(), hc⟩
  rw [h0, mul_zero] at h1
  exact h1

/-- The components of a glued field are the piecewise components. -/
theorem coeFn_glue (E : LocalElement n) (M : SimplicialMesh n) {k : ℕ} (u : E.Piecewise M k)
    (s : formIdx n (k : ℤ)) :
    (E.glue M k u s : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict M.domain]
      pieceFun M (fun T => formComp (k := (k : ℤ)) (E.extendPW M u T) s) :=
  coeFn_pieceL2 M M.domain _ (fun _ hT s => continuous_formComp
    (E.contDiff_extendPW M u hT).continuous s) s

/-- **The glued pullback**: `T^* (glue u) = glue (T^* u)`, elementwise on the interiors. -/
theorem glue_pullPiecewise (hM : IsOpen M.domain) {k : ℕ}
    (u : (whitneyElement n).Piecewise (M.map (affEquiv A hA b)) k)
    (hmeas : MeasurableSet (M.map (affEquiv A hA b)).domain)
    (hT : affMap A b ⁻¹' (M.map (affEquiv A hA b)).domain = M.domain) :
    (whitneyElement n).glue M k (pullPiecewise A hA b M k u) =
      fieldPull hA b hmeas hT (minorMat A k)
        ((whitneyElement n).glue (M.map (affEquiv A hA b)) k u) := by
  refine PiLp.ext fun s => Lp.ext ?_
  filter_upwards [coeFn_glue (whitneyElement n) M (pullPiecewise A hA b M k u) s,
    coeFn_fieldPull hA b hmeas hT (minorMat A k) ((whitneyElement n).glue (M.map (affEquiv A hA b)) k u) s,
    ae_comp_affMap hA b hT hmeas (ae_all_iff.2 fun t => coeFn_glue (whitneyElement n) (M.map (affEquiv A hA b)) u t),
    ae_mem_interior M hM.measurableSet] with x h1 h2 h3 hx
  obtain ⟨T, hT', hxT⟩ := hx
  have hTx : affMap A b x ∈ interior (mapEquiv (affEquiv A hA b) T).closedInterior := by
    rw [interior_closedInterior_mapEquiv]; exact ⟨x, hxT, rfl⟩
  rw [h1, h2]
  simp only [h3]
  rw [pieceFun_of_mem_interior M _ hT' hxT]
  simp only [pieceFun_of_mem_interior (M.map (affEquiv A hA b)) _ (mapEquiv_mem_map M (affEquiv A hA b) hT') hTx]
  rw [(whitneyElement n).extendPW_of_mem M _ hT',
    (whitneyElement n).extendPW_of_mem (M.map (affEquiv A hA b)) _ (mapEquiv_mem_map M (affEquiv A hA b) hT')]
  simp only [formComp, pullPiecewise_apply, affinePullback_apply, pullback_apply, affine_rows]
  have hdeg := (whitneyElement n).isDeg_of_mem
    (u ⟨mapEquiv (affEquiv A hA b) T, mapEquiv_mem_map M _ hT'⟩).2 (affMap A b x)
  rw [sum_isDeg_mul hdeg]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [minorMat, mul_comm]

/-- **Affine invariance of the Whitney spaces**: `T^*` maps the Whitney space of `M₂ = T(M₁)`
into the Whitney space of `M₁`. -/
theorem fieldPull_mem_whitney_V {M₁ M₂ : SimplicialMesh n}
    (h : M₂ = M₁.map (affEquiv A hA b)) (hM₁ : IsOpen M₁.domain)
    (hmeas : MeasurableSet M₂.domain) (hT : affMap A b ⁻¹' M₂.domain = M₁.domain) (k : ℤ)
    {v : L2F ℝ M₂.domain (formIdx n k)} (hv : v ∈ (whitneyElement n).V M₂ k) :
    fieldPull hA b hmeas hT (minorMat A k) v ∈ (whitneyElement n).V M₁ k := by
  subst h
  rcases k with k | k
  · obtain ⟨⟨u, hu⟩, rfl⟩ := hv
    exact ⟨⟨pullPiecewise A hA b M₁ k u, pullPiecewise_mem_globalSpace A hA b M₁ hu⟩,
      glue_pullPiecewise A hA b M₁ hM₁ u hmeas hT⟩
  · have := LocalElement.subsingleton_L2F_negSucc M₁.domain (n := n) k
    rw [Subsingleton.elim (fieldPull hA b hmeas hT (minorMat A _) v) 0]
    exact Submodule.zero_mem _

/-- **Affine invariance of the Whitney spaces with vanishing boundary DOFs.** -/
theorem fieldPull_mem_whitney_V₀ {M₁ M₂ : SimplicialMesh n}
    (h : M₂ = M₁.map (affEquiv A hA b)) (hM₁ : IsOpen M₁.domain)
    (hmeas : MeasurableSet M₂.domain) (hT : affMap A b ⁻¹' M₂.domain = M₁.domain) (k : ℤ)
    {v : L2F ℝ M₂.domain (formIdx n k)} (hv : v ∈ (whitneyElement n).V₀ M₂ k) :
    fieldPull hA b hmeas hT (minorMat A k) v ∈ (whitneyElement n).V₀ M₁ k := by
  subst h
  rcases k with k | k
  · obtain ⟨⟨u, hu⟩, rfl⟩ := hv
    exact ⟨⟨pullPiecewise A hA b M₁ k u, pullPiecewise_mem_globalSpace₀ A hA b M₁ hu⟩,
      glue_pullPiecewise A hA b M₁ hM₁ u hmeas hT⟩
  · have := LocalElement.subsingleton_L2F_negSucc M₁.domain (n := n) k
    rw [Subsingleton.elim (fieldPull hA b hmeas hT (minorMat A _) v) 0]
    exact Submodule.zero_mem _

end WhitneyInvariance

/-! ### The Whitney complexes of the image meshes -/

section WhitneyΩ

/-- **The image `T(M_N)` of the level-`(N + 1)` Freudenthal mesh of `Q`**, a conforming mesh of
`Ω`, shape regular uniformly in `N` (its simplices are `T K` for the simplices `K` of `M_N`, with
`B_{TK} = A B_K`). -/
def mesh (N : ℕ) : SimplicialMesh n := (FEM.mesh n N).map (affEquiv A hA b)

theorem mesh_domain (N : ℕ) : (mesh A hA b N).domain = domain A b := by
  rw [mesh, SimplicialMesh.map_domain, FEM.mesh_domain, coe_affEquiv, ← domain_eq_image A hA b]

theorem isOpen_mesh_domain (N : ℕ) : IsOpen (mesh A hA b N).domain :=
  (mesh_domain A hA b N) ▸ isOpen_domain A b

/-- The image `T(c)` of the centre of `Q`. -/
def center : Fin n → ℝ := affMap A b (FEM.center n)

include hA in
theorem center_mem_domain : center A b ∈ domain A b := by
  rw [domain_eq_image A hA b]; exact ⟨_, FEM.center_mem_cubeDomain n, rfl⟩

theorem strictStar_mesh (N : ℕ) : ∀ x ∈ closure (mesh A hA b N).domain, ∀ t : ℝ, 0 ≤ t → t < 1 →
    center A b + t • (x - center A b) ∈ (mesh A hA b N).domain := by
  rw [mesh_domain]
  exact add_smul_sub_mem_of_convex (isOpen_domain A b) (convex_domain A hA b)
    (center_mem_domain A hA b)

theorem mesh_cube_eq_map (N : ℕ) :
    FEM.mesh n N = (mesh A hA b N).map (affEquiv A⁻¹ (isUnit_det_inv hA) (affInvShift A b)) :=
  (map_map_of_leftInverse _ _ _ fun x => affMap_inv_affMap b hA x).symm

variable [NeZero n]

/-- **The Whitney complex of `T(M_N)`** as a subcomplex of `HΛ(Ω)`. -/
def whitney (N : ℕ) : (complex A b).Subcomplex :=
  (deRham ℝ n).maximalSubcomplexOfEq (mesh_domain A hA b N) (isOpen_mesh_domain A hA b N)
    (isOpen_domain A b) (whitneySubcomplex (mesh A hA b N) (isOpen_mesh_domain A hA b N))

instance (N : ℕ) (k : ℤ) : FiniteDimensional ℝ ((whitney A hA b N).V k) :=
  (deRham ℝ n).finiteDimensional_maximalSubcomplexOfEq _ _ _ _ k

/-- **The Whitney complex of `T(M_N)` with vanishing boundary DOFs** as a subcomplex of
`H̊Λ(Ω)`. -/
def whitneyMin (N : ℕ) : (complexMin A b).Subcomplex :=
  (deRham ℝ n).minimalSubcomplexOfEq (mesh_domain A hA b N) (isOpen_mesh_domain A hA b N)
    (isOpen_domain A b)
    (whitneySubcomplexMin (mesh A hA b N) (isOpen_mesh_domain A hA b N) (center A b)
      (strictStar_mesh A hA b N))

instance (N : ℕ) (k : ℤ) : FiniteDimensional ℝ ((whitneyMin A hA b N).V k) :=
  (deRham ℝ n).finiteDimensional_minimalSubcomplexOfEq _ _ _ _ k

/-- Affine invariance, transported along the domain equalities of the subcomplexes. -/
theorem fieldPull_mem_whitney_cast {M₁ M₂ : SimplicialMesh n}
    (h : M₂ = M₁.map (affEquiv A hA b)) {Ω₁ Ω₂ : Set (Fin n → ℝ)} (h₁ : M₁.domain = Ω₁)
    (h₂ : M₂.domain = Ω₂) (hM₁ : IsOpen M₁.domain) (hM₂ : IsOpen M₂.domain) (hΩ₁ : IsOpen Ω₁)
    (hΩ₂ : IsOpen Ω₂) (hT : affMap A b ⁻¹' Ω₂ = Ω₁) {k : ℤ} {v : L2F ℝ Ω₂ (formIdx n k)}
    (hv : v ∈ ((deRham ℝ n).maximalSubcomplexOfEq h₂ hM₂ hΩ₂ (whitneySubcomplex M₂ hM₂)).V k) :
    fieldPull hA b hΩ₂.measurableSet hT (minorMat A k) v ∈
      ((deRham ℝ n).maximalSubcomplexOfEq h₁ hM₁ hΩ₁ (whitneySubcomplex M₁ hM₁)).V k := by
  subst h₁ h₂
  exact fieldPull_mem_whitney_V A hA b h hM₁ _ hT k hv

theorem fieldPull_mem_whitneyMin_cast {M₁ M₂ : SimplicialMesh n}
    (h : M₂ = M₁.map (affEquiv A hA b)) {Ω₁ Ω₂ : Set (Fin n → ℝ)} (h₁ : M₁.domain = Ω₁)
    (h₂ : M₂.domain = Ω₂) (hM₁ : IsOpen M₁.domain) (hM₂ : IsOpen M₂.domain) (hΩ₁ : IsOpen Ω₁)
    (hΩ₂ : IsOpen Ω₂) (hT : affMap A b ⁻¹' Ω₂ = Ω₁) {x₁ x₂ : Fin n → ℝ}
    (hs₁ : ∀ x ∈ closure M₁.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₁ + t • (x - x₁) ∈ M₁.domain)
    (hs₂ : ∀ x ∈ closure M₂.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → x₂ + t • (x - x₂) ∈ M₂.domain)
    {k : ℤ} {v : L2F ℝ Ω₂ (formIdx n k)}
    (hv : v ∈ ((deRham ℝ n).minimalSubcomplexOfEq h₂ hM₂ hΩ₂
      (whitneySubcomplexMin M₂ hM₂ x₂ hs₂)).V k) :
    fieldPull hA b hΩ₂.measurableSet hT (minorMat A k) v ∈
      ((deRham ℝ n).minimalSubcomplexOfEq h₁ hM₁ hΩ₁ (whitneySubcomplexMin M₁ hM₁ x₁ hs₁)).V k := by
  subst h₁ h₂
  exact fieldPull_mem_whitney_V₀ A hA b h hM₁ _ hT k hv

/-- **Affine invariance of the Whitney spaces on `Ω`**: `v ∈ Vₕᵏ(T(M_N))` iff
`T^* v ∈ Vₕᵏ(M_N)`. -/
theorem mem_whitney_V_iff (N : ℕ) (k : ℤ) (x : L2F ℝ (domain A b) (formIdx n k)) :
    x ∈ (whitney A hA b N).V k ↔ pullEquiv A hA b k x ∈ (FEM.whitney n N).V k := by
  constructor
  · intro hx
    exact fieldPull_mem_whitney_cast A hA b rfl (FEM.mesh_domain n N) (mesh_domain A hA b N)
      (FEM.isOpen_mesh_domain n N) (isOpen_mesh_domain A hA b N) (FEM.isOpen_cubeDomain n)
      (isOpen_domain A b) (preimage_domain A hA b) hx
  · intro hx
    have h := fieldPull_mem_whitney_cast A⁻¹ (isUnit_det_inv hA) (affInvShift A b)
      (mesh_cube_eq_map A hA b N) (mesh_domain A hA b N) (FEM.mesh_domain n N)
      (isOpen_mesh_domain A hA b N) (FEM.isOpen_mesh_domain n N) (isOpen_domain A b)
      (FEM.isOpen_cubeDomain n) (preimage_inv_of_affMap hA b (preimage_domain A hA b)) hx
    have e : fieldPull (isUnit_det_inv hA) (affInvShift A b) (FEM.isOpen_cubeDomain n).measurableSet
        (preimage_inv_of_affMap hA b (preimage_domain A hA b)) (minorMat A⁻¹ k)
        (pullEquiv A hA b k x) = x := (pullEquiv A hA b k).symm_apply_apply x
    rwa [e] at h

/-- **Affine invariance of the Whitney spaces with vanishing boundary DOFs on `Ω`.** -/
theorem mem_whitneyMin_V_iff (N : ℕ) (k : ℤ) (x : L2F ℝ (domain A b) (formIdx n k)) :
    x ∈ (whitneyMin A hA b N).V k ↔ pullEquiv A hA b k x ∈ (FEM.whitneyMin n N).V k := by
  constructor
  · intro hx
    exact fieldPull_mem_whitneyMin_cast A hA b rfl (FEM.mesh_domain n N) (mesh_domain A hA b N)
      (FEM.isOpen_mesh_domain n N) (isOpen_mesh_domain A hA b N) (FEM.isOpen_cubeDomain n)
      (isOpen_domain A b) (preimage_domain A hA b) (FEM.strictStar_mesh n N)
      (strictStar_mesh A hA b N) hx
  · intro hx
    have h := fieldPull_mem_whitneyMin_cast A⁻¹ (isUnit_det_inv hA) (affInvShift A b)
      (mesh_cube_eq_map A hA b N) (mesh_domain A hA b N) (FEM.mesh_domain n N)
      (isOpen_mesh_domain A hA b N) (FEM.isOpen_mesh_domain n N) (isOpen_domain A b)
      (FEM.isOpen_cubeDomain n) (preimage_inv_of_affMap hA b (preimage_domain A hA b))
      (strictStar_mesh A hA b N) (FEM.strictStar_mesh n N) hx
    have e : fieldPull (isUnit_det_inv hA) (affInvShift A b) (FEM.isOpen_cubeDomain n).measurableSet
        (preimage_inv_of_affMap hA b (preimage_domain A hA b)) (minorMat A⁻¹ k)
        (pullEquiv A hA b k x) = x := (pullEquiv A hA b k).symm_apply_apply x
    rwa [e] at h

end WhitneyΩ

/-! ### Poincaré inequalities, closed range and harmonic forms on `Ω` -/

section Hodge

include hA

/-- **Poincaré inequality of `HΛ(Ω)`** with `c_P(A) = ‖(T^*)⁻¹‖ (2π)⁻¹ ‖T^*‖`, from the cube
(`Feec.Models.Cube.FEM.norm_le_of_mem_orthogonal_cycles`) and `IsChainIso.norm_le_of_mem_orthogonal_cycles`. -/
theorem norm_le_of_mem_orthogonal_cycles {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (z : ((complex A b).d i j).domain)
    (hz : (z : L2F ℝ (domain A b) (formIdx n i)) ∈ ((complex A b).cycles i)ᗮ) :
    ‖(z : L2F ℝ (domain A b) (formIdx n i))‖ ≤
      pullConst A⁻¹ * (2 * Real.pi)⁻¹ * pullConst A * ‖(complex A b).d i j z‖ :=
  (isChainIso A hA b).norm_le_of_mem_orthogonal_cycles hij (by positivity)
    (norm_pullEquiv_le A hA b j) (norm_pullEquiv_symm_le A hA b i)
    (fun z hz => FEM.norm_le_of_mem_orthogonal_cycles hij z hz) z hz

/-- **Poincaré inequality of `H̊Λ(Ω)`**. -/
theorem norm_le_of_mem_orthogonal_cycles_min {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (z : ((complexMin A b).d i j).domain)
    (hz : (z : L2F ℝ (domain A b) (formIdx n i)) ∈ ((complexMin A b).cycles i)ᗮ) :
    ‖(z : L2F ℝ (domain A b) (formIdx n i))‖ ≤
      pullConst A⁻¹ * (2 * Real.pi)⁻¹ * pullConst A * ‖(complexMin A b).d i j z‖ :=
  (isChainIsoMin A hA b).norm_le_of_mem_orthogonal_cycles hij (by positivity)
    (norm_pullEquiv_le A hA b j) (norm_pullEquiv_symm_le A hA b i)
    (fun z hz => FEM.norm_le_of_mem_orthogonal_cycles_min hij z hz) z hz

/-- **`HΛ(Ω)` has closed range in every degree.** -/
theorem closedRangeAt (j : ℤ) : (complex A b).ClosedRangeAt j := by
  have hr : (ComplexShape.up ℤ).Rel (j - 1) j := sub_add_cancel j 1
  exact ((complex A b).closedRangeAt_iff_poincare_of_rel hr).2
    ⟨_, fun z hz => norm_le_of_mem_orthogonal_cycles A hA b hr z hz⟩

/-- **`H̊Λ(Ω)` has closed range in every degree.** -/
theorem closedRangeAt_min (j : ℤ) : (complexMin A b).ClosedRangeAt j := by
  have hr : (ComplexShape.up ℤ).Rel (j - 1) j := sub_add_cancel j 1
  exact ((complexMin A b).closedRangeAt_iff_poincare_of_rel hr).2
    ⟨_, fun z hz => norm_le_of_mem_orthogonal_cycles_min A hA b hr z hz⟩

/-- **The harmonic forms of `HΛ(Ω)` are finite-dimensional**, of dimension `[k = 0]` (the
constants; `Ω` is contractible). -/
theorem finiteDimensional_harmonic (k : ℤ) : FiniteDimensional ℝ ((complex A b).harmonic k) :=
  (isChainIso A hA b).finiteDimensional_harmonic k

theorem finrank_harmonic (k : ℤ) :
    Module.finrank ℝ ((complex A b).harmonic k) = if k = 0 then 1 else 0 := by
  rw [(isChainIso A hA b).finrank_harmonic_eq k, FEM.finrank_harmonic]

/-- **The harmonic forms of `H̊Λ(Ω)` are finite-dimensional**, of dimension `[k = n]`. -/
theorem finiteDimensional_harmonic_min (k : ℤ) :
    FiniteDimensional ℝ ((complexMin A b).harmonic k) :=
  (isChainIsoMin A hA b).finiteDimensional_harmonic k

theorem finrank_harmonic_min (k : ℤ) :
    Module.finrank ℝ ((complexMin A b).harmonic k) = if k = n then 1 else 0 := by
  rw [(isChainIsoMin A hA b).finrank_harmonic_eq k, FEM.finrank_harmonic_min]

end Hodge

/-! ### The Whitney finite element method on `Ω` -/

theorem _root_.Feec.HilbertComplex.Subcomplex.CochainProjection.IsGraphBounded.mono'
    {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace ℝ (W i)] [∀ i, CompleteSpace (W i)]
    {H : HilbertComplex ℝ c W} {S : H.Subcomplex} {P : S.CochainProjection} {i j : ι} {C C' : ℝ}
    (h : P.IsGraphBounded i j C) (hC : 0 ≤ C) (hCC : C ≤ C') : P.IsGraphBounded i j C' :=
  fun x => (h x).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC hCC 2) (by positivity))

section WhitneyFEM

/-- The constant `‖(T^*)⁻¹‖ · 2C · ‖T^*‖` of the transported projections, at least `1`. -/
def projConst (C : ℝ) : ℝ := max 1 (pullConst A⁻¹ * (2 * C) * pullConst A)

/-- The Poincaré constant `c_P(A) = ‖(T^*)⁻¹‖ (2π)⁻¹ ‖T^*‖` of `Ω`, at least `1`. -/
def poincareConst : ℝ := max 1 (pullConst A⁻¹ * (2 * Real.pi)⁻¹ * pullConst A)

theorem one_le_projConst (C : ℝ) : 1 ≤ projConst A C := le_max_left _ _

theorem one_le_poincareConst : 1 ≤ poincareConst A := le_max_left _ _

include hA in
theorem poincare (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j)
    (z : ((complex A b).d i j).domain)
    (hz : (z : L2F ℝ (domain A b) (formIdx n i)) ∈ ((complex A b).cycles i)ᗮ) :
    ‖(z : L2F ℝ (domain A b) (formIdx n i))‖ ≤ poincareConst A * ‖(complex A b).d i j z‖ :=
  (norm_le_of_mem_orthogonal_cycles A hA b hij z hz).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

include hA in
theorem poincare_min (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j)
    (z : ((complexMin A b).d i j).domain)
    (hz : (z : L2F ℝ (domain A b) (formIdx n i)) ∈ ((complexMin A b).cycles i)ᗮ) :
    ‖(z : L2F ℝ (domain A b) (formIdx n i))‖ ≤ poincareConst A * ‖(complexMin A b).d i j z‖ :=
  (norm_le_of_mem_orthogonal_cycles_min A hA b hij z hz).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

variable [NeZero n]

/-- **The smoothed projections of `Ω`**: `T^{*-1} π_N T^*` for the smoothed projections `π_N` of
the cube (`Feec.Models.Cube.FEM.SmoothingEstimates.proj`), cochain projections onto the Whitney
complexes of `T(M_N)` by affine invariance. -/
def proj {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} (hE : FEM.SmoothingEstimates n p C)
    (N : ℕ) : (whitney A hA b N).CochainProjection :=
  (isChainIso A hA b).comapProj (whitney A hA b N) (fun i x => mem_whitney_V_iff A hA b N i x)
    (hE.proj N)

/-- The smoothed projections with vanishing boundary DOFs of `Ω`. -/
def projMin {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ} (hE : FEM.SmoothingEstimatesMin n p C)
    (N : ℕ) : (whitneyMin A hA b N).CochainProjection :=
  (isChainIsoMin A hA b).comapProj (whitneyMin A hA b N)
    (fun i x => mem_whitneyMin_V_iff A hA b N i x) (hE.proj N)

section Estimates

variable {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ}

theorem norm_proj_le (hE : FEM.SmoothingEstimates n p C) (N : ℕ) (i : ℤ)
    (x : L2F ℝ (domain A b) (formIdx n i)) :
    ‖(proj A hA b hE N).π i x‖ ≤ projConst A C * ‖x‖ :=
  ((isChainIso A hA b).norm_comapProj_le _ _ (hE.proj N) hE.two_mul_nonneg (hE.norm_proj_le N i)
    (norm_pullEquiv_le A hA b i) (norm_pullEquiv_symm_le A hA b i) x).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

theorem isGraphBounded_proj (hE : FEM.SmoothingEstimates n p C) (N : ℕ) (i j : ℤ) :
    (proj A hA b hE N).IsGraphBounded i j (projConst A C) :=
  ((isChainIso A hA b).isGraphBounded_comapProj _ _ (hE.proj N) (hE.isGraphBounded_proj N i j)
    (norm_pullEquiv_le A hA b) (norm_pullEquiv_symm_le A hA b)).mono'
    (mul_nonneg (mul_nonneg (pullConst_nonneg _) hE.two_mul_nonneg) (pullConst_nonneg _))
    (le_max_right _ _)

theorem norm_projMin_le (hE : FEM.SmoothingEstimatesMin n p C) (N : ℕ) (i : ℤ)
    (x : L2F ℝ (domain A b) (formIdx n i)) :
    ‖(projMin A hA b hE N).π i x‖ ≤ projConst A C * ‖x‖ :=
  ((isChainIsoMin A hA b).norm_comapProj_le _ _ (hE.proj N) hE.two_mul_nonneg
    (hE.norm_proj_le N i) (norm_pullEquiv_le A hA b i) (norm_pullEquiv_symm_le A hA b i) x).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

theorem isGraphBounded_projMin (hE : FEM.SmoothingEstimatesMin n p C) (N : ℕ) (i j : ℤ) :
    (projMin A hA b hE N).IsGraphBounded i j (projConst A C) :=
  ((isChainIsoMin A hA b).isGraphBounded_comapProj _ _ (hE.proj N) (hE.isGraphBounded_proj N i j)
    (norm_pullEquiv_le A hA b) (norm_pullEquiv_symm_le A hA b)).mono'
    (mul_nonneg (mul_nonneg (pullConst_nonneg _) hE.two_mul_nonneg) (pullConst_nonneg _))
    (le_max_right _ _)

/-- **The harmonic gap of the smoothed projections of `Ω` tends to zero.** -/
theorem tendsto_harmonicGap_proj (hE : FEM.SmoothingEstimates n p C) (j : ℤ) :
    Tendsto (fun N => (proj A hA b hE N).harmonicGap j) atTop (𝓝 0) := by
  have := finiteDimensional_harmonic A hA b j
  exact Subcomplex.CochainProjection.tendsto_harmonicGap (proj A hA b hE)
    (zero_le_one.trans (one_le_projConst A C)) (fun N x => norm_proj_le A hA b hE N j x)
    fun q _ => IsChainIso.tendsto_infDist_comapSub (whitney A hA b)
      (fun N i x => mem_whitney_V_iff A hA b N i x) (fun x' => FEM.tendsto_infDist_whitney j x') q

theorem tendsto_harmonicGap_projMin (hE : FEM.SmoothingEstimatesMin n p C) (j : ℤ) :
    Tendsto (fun N => (projMin A hA b hE N).harmonicGap j) atTop (𝓝 0) := by
  have := finiteDimensional_harmonic_min A hA b j
  exact Subcomplex.CochainProjection.tendsto_harmonicGap (projMin A hA b hE)
    (zero_le_one.trans (one_le_projConst A C)) (fun N x => norm_projMin_le A hA b hE N j x)
    fun q _ => IsChainIso.tendsto_infDist_comapSub (whitneyMin A hA b)
      (fun N i x => mem_whitneyMin_V_iff A hA b N i x)
      (fun x' => FEM.tendsto_infDist_whitneyMin j x') q

end Estimates

/-! #### The finite element theorems on `Ω = A · Q + b`, with no hypothesis -/

/-- **Uniformly bounded smoothed cochain projections with vanishing harmonic gap** onto the
Whitney complexes of the image Freudenthal meshes of the parallelepiped `Ω` ([AFW2010], §5.4):
`‖π_N‖ ≤ C` in `L²` and in every graph norm, uniformly in `N`, and
`sup_{q ∈ ℌʲ(Ω), ‖q‖ ≤ 1} ‖q - π_N q‖ → 0`. -/
theorem smoothedProjection_uniform : ∃ (C : ℝ) (π : ∀ N, (whitney A hA b N).CochainProjection),
    1 ≤ C ∧ (∀ N i x, ‖(π N).π i x‖ ≤ C * ‖x‖) ∧ (∀ N i j, (π N).IsGraphBounded i j C) ∧
      ∀ j, Tendsto (fun N => (π N).harmonicGap j) atTop (𝓝 0) := by
  obtain ⟨p, C, hE⟩ := FEM.smoothingEstimates_exists (n := n)
  exact ⟨projConst A C, proj A hA b hE, one_le_projConst A C, norm_proj_le A hA b hE,
    isGraphBounded_proj A hA b hE, tendsto_harmonicGap_proj A hA b hE⟩

/-- **Uniformly bounded smoothed cochain projections onto the Whitney complexes with vanishing
boundary DOFs** of `Ω`, with vanishing harmonic gap. -/
theorem smoothedProjection_uniform_min :
    ∃ (C : ℝ) (π : ∀ N, (whitneyMin A hA b N).CochainProjection),
    1 ≤ C ∧ (∀ N i x, ‖(π N).π i x‖ ≤ C * ‖x‖) ∧ (∀ N i j, (π N).IsGraphBounded i j C) ∧
      ∀ j, Tendsto (fun N => (π N).harmonicGap j) atTop (𝓝 0) := by
  obtain ⟨p, C, hE⟩ := FEM.smoothingEstimatesMin_exists (n := n)
  exact ⟨projConst A C, projMin A hA b hE, one_le_projConst A C, norm_projMin_le A hA b hE,
    isGraphBounded_projMin A hA b hE, tendsto_harmonicGap_projMin A hA b hE⟩

/-- **Uniform discrete Poincaré inequality** on the Whitney complexes of `T(M_N)` ([AFW2010],
Thm 3.6): `‖x‖ ≤ c ‖d x‖` for `x ∈ Vₕⁱ ⊥ 𝔷ₕⁱ`, with `c` independent of `N`. -/
theorem discretePoincare : ∃ c : ℝ, ∀ {i j : ℤ}, (ComplexShape.up ℤ).Rel i j → ∀ (N : ℕ)
    {x : L2F ℝ (domain A b) (formIdx n i)} (hx : x ∈ (whitney A hA b N).V i),
    (∀ y ∈ (whitney A hA b N).cyclesW i, inner ℝ y x = 0) →
      ‖x‖ ≤ c * ‖(complex A b).d i j ⟨x, (whitney A hA b N).le_domain i j hx⟩‖ := by
  obtain ⟨C, π, hC, hπ, -, -⟩ := smoothedProjection_uniform A hA b
  exact ⟨C * poincareConst A, fun {i j} hij N x hx hxo =>
    (π N).norm_le_of_forall_inner_eq_zero hij (poincare A hA b i j hij)
      (zero_le_one.trans hC) (hπ N i) hx hxo⟩

/-- **Uniform discrete Poincaré inequality** with vanishing boundary DOFs on `Ω`. -/
theorem discretePoincare_min : ∃ c : ℝ, ∀ {i j : ℤ}, (ComplexShape.up ℤ).Rel i j → ∀ (N : ℕ)
    {x : L2F ℝ (domain A b) (formIdx n i)} (hx : x ∈ (whitneyMin A hA b N).V i),
    (∀ y ∈ (whitneyMin A hA b N).cyclesW i, inner ℝ y x = 0) →
      ‖x‖ ≤ c * ‖(complexMin A b).d i j ⟨x, (whitneyMin A hA b N).le_domain i j hx⟩‖ := by
  obtain ⟨C, π, hC, hπ, -, -⟩ := smoothedProjection_uniform_min A hA b
  exact ⟨C * poincareConst A, fun {i j} hij N x hx hxo =>
    (π N).norm_le_of_forall_inner_eq_zero hij (poincare_min A hA b i j hij)
      (zero_le_one.trans hC) (hπ N i) hx hxo⟩

/-- **Uniform well-posedness and stability of the discrete mixed Hodge Laplacian** on the
Whitney complexes of `T(M_N)` ([AFW2010], Thm 3.8): unique discrete solutions, bounded by
`C ‖fₕ‖` with `C` independent of `N`. -/
theorem mixed_wellPosed : ∃ C : ℝ, ∀ {i j k : ℤ}, (ComplexShape.up ℤ).Rel i j →
    (ComplexShape.up ℤ).Rel j k → ∀ (N : ℕ) (f : (whitney A hA b N).V j),
    (∃! x, (whitney A hA b N).toHilbertComplex.mixedForm i j k x =
      (whitney A hA b N).toHilbertComplex.mixedRHS i j f) ∧
    ∀ x : (whitney A hA b N).toHilbertComplex.MixedSpace i j,
      (whitney A hA b N).toHilbertComplex.mixedForm i j k x =
        (whitney A hA b N).toHilbertComplex.mixedRHS i j f → ‖x‖ ≤ C * ‖f‖ := by
  refine (smoothedProjection_uniform A hA b).elim fun C hC => hC.elim fun π hπ => ?_
  obtain ⟨hC1, hb, -, -⟩ := hπ
  refine ⟨16 * (C * poincareConst A) ^ 2, fun {i j k} hij hjk N f => ⟨?_, fun x hx => ?_⟩⟩
  · exact (π N).existsUnique_mixed hij hjk (one_le_poincareConst A) hC1
      (poincare A hA b i j hij) (poincare A hA b j k hjk) (hb N i) (hb N j) f
  · exact (π N).norm_le_of_mixed hij hjk (one_le_poincareConst A) hC1
      (poincare A hA b i j hij) (poincare A hA b j k hjk) (hb N i) (hb N j) hx

/-- **Uniform well-posedness and stability of the discrete mixed Hodge Laplacian with vanishing
traces** on `Ω`. -/
theorem mixed_wellPosed_min : ∃ C : ℝ, ∀ {i j k : ℤ}, (ComplexShape.up ℤ).Rel i j →
    (ComplexShape.up ℤ).Rel j k → ∀ (N : ℕ) (f : (whitneyMin A hA b N).V j),
    (∃! x, (whitneyMin A hA b N).toHilbertComplex.mixedForm i j k x =
      (whitneyMin A hA b N).toHilbertComplex.mixedRHS i j f) ∧
    ∀ x : (whitneyMin A hA b N).toHilbertComplex.MixedSpace i j,
      (whitneyMin A hA b N).toHilbertComplex.mixedForm i j k x =
        (whitneyMin A hA b N).toHilbertComplex.mixedRHS i j f → ‖x‖ ≤ C * ‖f‖ := by
  refine (smoothedProjection_uniform_min A hA b).elim fun C hC => hC.elim fun π hπ => ?_
  obtain ⟨hC1, hb, -, -⟩ := hπ
  refine ⟨16 * (C * poincareConst A) ^ 2, fun {i j k} hij hjk N f => ⟨?_, fun x hx => ?_⟩⟩
  · exact (π N).existsUnique_mixed hij hjk (one_le_poincareConst A) hC1
      (poincare_min A hA b i j hij) (poincare_min A hA b j k hjk) (hb N i) (hb N j) f
  · exact (π N).norm_le_of_mixed hij hjk (one_le_poincareConst A) hC1
      (poincare_min A hA b i j hij) (poincare_min A hA b j k hjk) (hb N i) (hb N j) hx

/-- **Quasi-optimality of the Whitney method for the mixed Hodge Laplacian on `Ω`** ([AFW2010],
Thm 3.9): error `≤ K (E(σ) + E(u) + E(q) + μ_j(N) E(P_𝔅 u))` with `μ_j(N) → 0`. -/
theorem mixed_quasiOptimal : ∃ (K : ℝ) (μ : ℤ → ℕ → ℝ), (∀ j, Tendsto (μ j) atTop (𝓝 0)) ∧
    ∀ {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (domain A b) (formIdx n j)} {σ : (complex A b).domainSpace i}
    {u : (complex A b).domainSpace j} {q : (complex A b).harmonic j},
    (complex A b).IsMixedSolution i j k f σ u q → ∀ N : ℕ,
    ‖σ - (whitney A hA b N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney A hA b N) hij hjk f).fst‖ +
        ‖u - (whitney A hA b N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney A hA b N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (domain A b) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitney A hA b N) hij hjk f).snd.snd :
            (whitney A hA b N).V j) : L2F ℝ (domain A b) (formIdx n j))‖ ≤
      K * (Metric.infDist σ ((whitney A hA b N).domainSub i) +
        Metric.infDist u ((whitney A hA b N).domainSub j) +
        Metric.infDist (q : L2F ℝ (domain A b) (formIdx n j)) ((whitney A hA b N).harmonicW j) +
        μ j N * Metric.infDist ((complex A b).boundaryPart j ((complex A b).domainIncl j u))
          ((whitney A hA b N).domainSub j)) := by
  refine (smoothedProjection_uniform A hA b).elim fun C hC => hC.elim fun π hπ => ?_
  obtain ⟨hC1, -, hg, hgap⟩ := hπ
  exact ⟨(1 + 144 * (C * √(1 + poincareConst A ^ 2)) ^ 2) * (1 + C),
    fun j N => (π N).harmonicGap j, hgap,
    fun {i j k} hij hjk _ _ _ _ hs N => (π N).norm_sub_le_infDist_harmonicGap hij hjk hC1
      (poincare A hA b i j hij) (poincare A hA b j k hjk) (hg N i j) (hg N j k) hs⟩

/-- **Quasi-optimality of the Whitney method with vanishing traces on `Ω`.** -/
theorem mixed_quasiOptimal_min : ∃ (K : ℝ) (μ : ℤ → ℕ → ℝ), (∀ j, Tendsto (μ j) atTop (𝓝 0)) ∧
    ∀ {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k)
    {f : L2F ℝ (domain A b) (formIdx n j)} {σ : (complexMin A b).domainSpace i}
    {u : (complexMin A b).domainSpace j} {q : (complexMin A b).harmonic j},
    (complexMin A b).IsMixedSolution i j k f σ u q → ∀ N : ℕ,
    ‖σ - (whitneyMin A hA b N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin A hA b N) hij hjk f).fst‖ +
        ‖u - (whitneyMin A hA b N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitneyMin A hA b N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (domain A b) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitneyMin A hA b N) hij hjk
            f).snd.snd : (whitneyMin A hA b N).V j) : L2F ℝ (domain A b) (formIdx n j))‖ ≤
      K * (Metric.infDist σ ((whitneyMin A hA b N).domainSub i) +
        Metric.infDist u ((whitneyMin A hA b N).domainSub j) +
        Metric.infDist (q : L2F ℝ (domain A b) (formIdx n j))
          ((whitneyMin A hA b N).harmonicW j) +
        μ j N * Metric.infDist ((complexMin A b).boundaryPart j ((complexMin A b).domainIncl j u))
          ((whitneyMin A hA b N).domainSub j)) := by
  refine (smoothedProjection_uniform_min A hA b).elim fun C hC => hC.elim fun π hπ => ?_
  obtain ⟨hC1, -, hg, hgap⟩ := hπ
  exact ⟨(1 + 144 * (C * √(1 + poincareConst A ^ 2)) ^ 2) * (1 + C),
    fun j N => (π N).harmonicGap j, hgap,
    fun {i j k} hij hjk _ _ _ _ hs N => (π N).norm_sub_le_infDist_harmonicGap hij hjk hC1
      (poincare_min A hA b i j hij) (poincare_min A hA b j k hjk) (hg N i j) (hg N j k) hs⟩

end WhitneyFEM

end Feec.Models.Parallelepiped
