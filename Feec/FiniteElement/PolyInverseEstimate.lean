module

public import Feec.FiniteElement.LocalDof
public import Feec.FiniteElement.InverseEstimate

/-!
# Inverse, DOF-scaling and kernel estimates for polynomial forms on homothetic simplices

The higher-order analogue of `Feec.FiniteElement.InverseEstimate` (which treats the affine fields
`P₁⁻Λᵏ`). Let `V ≤ P_rΛᵏ(ℝⁿ)` be a space of `k`-form fields with polynomial coefficients of degree
`≤ r` (`polySpace n r k`, or the trimmed `polyMinusSpace n r k`, `polyMinusSpace_le_polySpace`),
and `K` a nondegenerate reference `n`-simplex. Everything is a finite-dimensional norm comparison
(`exists_norm_le_mul_weight_mul_norm`: a pointwise bounded family of linear maps on a
finite-dimensional space is bounded by any injective linear map, from
`exists_abs_le_mul_norm_of_finite`; `exists_norm_le_mul_norm_of_ker_le`: `‖L v‖ ≤ C ‖D v‖` if
`ker D ≤ ker L`), followed by transport through the homothety `H y = t + h y`
(`affinePullback_scalarMat`: `H^* u = hᵏ u ∘ H` on `k`-forms;
`integral_closedInterior_mapEquiv_boxMap`: `∫_T f = hⁿ ∫_K f ∘ H`, `T = t + h K`;
`partialDeriv_affinePullback_scalarMat`: `∂ⱼ (H^* u) = h^{k+1} (∂ⱼ u) ∘ H`). Squared `L²`
norms are written `formL2Sq S u = Σ_s ∫_S u_s²` and `formGradL2Sq S u = Σⱼ Σ_s ∫_S (∂ⱼ u_s)²`.

**On the reference simplex** (any compact convex `S` with nonempty interior):
* `exists_norm_le_sqrt_formL2Sq`: `sup_S ‖u‖ ≤ A ‖u‖_{L²(S)}` and
  `Lip_S(u) ≤ A ‖u‖_{L²(S)}`;
* `exists_norm_le_sum_abs_dof`: `sup_S ‖u‖ ≤ B Σⱼ |ℓⱼ(u)|` for any unisolvent family of linear
  functionals `ℓⱼ` on `V`;
* `exists_formL2Sq_equiv_sum_sq_dof`: `‖u‖²_{L²(S)} ≍ Σⱼ ℓⱼ(u)²`;
* `exists_formL2Sq_le_formGradL2Sq` (**kernel lemma**): if `L : V → W` is linear and vanishes on
  the constant fields of `V`, then `‖L v‖_{L²(S)} ≤ C ‖Dv‖_{L²(S)}`
  (`exists_formL2Sq_sub_le_formGradL2Sq` for `L = I - P`, `P` reproducing constants). The kernel
  of `v ↦ Dv|_S` on polynomial fields is the constants (`eq_const_of_gradEmbed_eq_zero`: a
  polynomial vanishing on a nonempty open set vanishes, `eq_zero_of_eval_eq_zero_of_isOpen`).

**On `T = t + h K`**, `h > 0`, with constants depending only on `K`, `V` and the DOFs
(`V` stable under homotheties, true for `P_rΛᵏ` and `P_r⁻Λᵏ` by affine invariance):
* `exists_local_inverse_bound_of_le_polySpace`: `h^{n/2} sup_T ‖u‖ ≲ ‖u‖_{L²(T)}` and
  `h^{n/2} h Lip_T(u) ≲ ‖u‖_{L²(T)}`;
* `exists_local_dof_bound_of_le_polySpace`: `hᵏ sup_T ‖u‖ ≲ Σⱼ |ℓⱼ(H^* u)|`;
* `exists_local_formL2Sq_equiv_of_le_polySpace`: the **`ℓ²`-scaling of the DOFs**
  `‖u‖²_{L²(T)} ≍ h^{n-2k} Σⱼ ℓⱼ(H^* u)²` (stated without negative powers:
  `h^{2k} ‖u‖²_{L²(T)} ≤ C hⁿ Σⱼ ℓⱼ(H^* u)²` and conversely);
* `exists_local_kernel_bound`: `‖w‖_{L²(T)} ≤ C h ‖Du‖_{L²(T)}` whenever `H^* w = L(H^* u)`
  (homothetic conjugates `L_T` of a kernel-lemma map `L`, e.g. `u - Π_T u`).

**Moment DOFs.** For every moment `ω ↦ ∫_{T̂_m} (F^* ω ∧ η)_{univ}` along an affine
parametrization `F` of a face (`affineMoment`, and `faceMoment p e η` for every vertex map `e`,
hence every ordering of the vertices), the moment on the corresponding face of `T = t + h K` is
the moment of `H^* ω` on `K` (`affineMoment_homothety`, `faceMoment_mapEquiv_boxMap`; for a general
affine image, `faceMoment_affine`, `faceTrace_affine`). So the abstract estimates apply to every
moment DOF family that is unisolvent on `K`, whatever the face parametrization. For the DOFs of
`Feec.FiniteElement.LocalDof` (`localDof`, `localDofMinus`, on the faces of `K` in the vertex
order of `K`): `exists_local_dof_bound_polySpace`, `exists_local_dof_bound_polyMinusSpace`,
`exists_local_formL2Sq_equiv_polySpace`, `exists_local_formL2Sq_equiv_polyMinusSpace`, with the
moments `∫_f tr_f u ∧ ηᵢ` on the faces of `T` itself.

**Vector-valued fields.** All statements are per field with constants independent of the field,
so for finitely many components `(u_c)_c` (e.g. `P_rΛᵏ ⊗ ℝ^N`) they hold componentwise and
summing them over the components gives the vector-valued versions.

These are the inverse and scaling tools behind the smoothed projections of [AFW2010], §5.4
([ChristiansenWinther2008]) for the higher-order families, and the corrected forms of the norm
equivalences of [QuennevilleBelair2015], Prop 5.8 (whose global `ℓ¹` sums of DOFs are not
uniformly equivalent to the `L²` norm; the local `ℓ²` scaling above, summed over the simplices,
is) and of the scaling argument of [QuennevilleBelair2015], Prop 5.9(1). On meshes whose
simplices are homothetic copies of finitely many reference simplices (Freudenthal–Kuhn meshes)
the constants are uniform without a shape-regularity argument.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.4 (inverse estimates for the smoothed projection)
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §4.5–4.6 (the moment degrees of freedom)
* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], §3.2 (inverse
  inequalities)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Props 5.8–5.9
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset

namespace Feec.FiniteElement

open ExteriorFibre Feec.Mesh

variable {n : ℕ}

/-! ### Uniform bounds on finite-dimensional spaces -/

/-- **Uniform boundedness in finite dimension**: a family `φⱼ` of linear maps on a
finite-dimensional space `V` that is pointwise bounded relative to weights `wⱼ ≥ 0`
(`‖φⱼ v‖ ≤ M_v wⱼ`) is uniformly bounded by any injective linear map `ι` into a normed space:
`‖φⱼ v‖ ≤ A wⱼ ‖ι v‖`. Proof: expand `v` in a basis and bound the coordinates by
`exists_abs_le_mul_norm_of_finite`. -/
theorem exists_norm_le_mul_weight_mul_norm {V E F J : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (ι : V →ₗ[ℝ] E) (hι : Function.Injective ι) (φ : J → V →ₗ[ℝ] F)
    (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (hφ : ∀ v, ∃ M, ∀ j, ‖φ j v‖ ≤ M * w j) :
    ∃ A, 0 ≤ A ∧ ∀ v j, ‖φ j v‖ ≤ A * w j * ‖ι v‖ := by
  set b := Module.finBasis ℝ V
  choose M hM using fun i => hφ (b i)
  obtain ⟨A₀, hA₀, hA⟩ := exists_abs_le_mul_norm_of_finite ι hι fun i => b.coord i
  refine ⟨A₀ * ∑ i, max (M i) 0, mul_nonneg hA₀ (Finset.sum_nonneg fun i _ => le_max_right _ _),
    fun v j => ?_⟩
  have hv : φ j v = ∑ i, b.repr v i • φ j (b i) := by
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    simp only [map_smul]
  rw [hv]
  calc ‖∑ i, b.repr v i • φ j (b i)‖ ≤ ∑ i, |b.repr v i| * ‖φ j (b i)‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, (A₀ * ‖ι v‖) * (max (M i) 0 * w j) := by
        refine Finset.sum_le_sum fun i _ => mul_le_mul ?_ ((hM i j).trans ?_) (norm_nonneg _)
          (by positivity)
        · have := hA v i
          rwa [Module.Basis.coord_apply] at this
        · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hw j)
    _ = (A₀ * ∑ i, max (M i) 0) * w j * ‖ι v‖ := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- Unweighted form of `exists_norm_le_mul_weight_mul_norm`. -/
theorem exists_norm_le_mul_norm_of_bounded {V E F J : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (ι : V →ₗ[ℝ] E) (hι : Function.Injective ι) (φ : J → V →ₗ[ℝ] F)
    (hφ : ∀ v, ∃ M, ∀ j, ‖φ j v‖ ≤ M) :
    ∃ A, 0 ≤ A ∧ ∀ v j, ‖φ j v‖ ≤ A * ‖ι v‖ := by
  obtain ⟨A, hA0, hA⟩ := exists_norm_le_mul_weight_mul_norm ι hι φ (fun _ => 1)
    (fun _ => zero_le_one) fun v => by simpa using hφ v
  exact ⟨A, hA0, fun v j => by simpa using hA v j⟩

/-- **Factorization through a kernel in finite dimension**: if `ker D ≤ ker L` for linear maps
`D`, `L` on a finite-dimensional space into normed spaces, then `‖L v‖ ≤ C ‖D v‖`. -/
theorem exists_norm_le_mul_norm_of_ker_le {V E F : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (D : V →ₗ[ℝ] E) (L : V →ₗ[ℝ] F) (h : LinearMap.ker D ≤ LinearMap.ker L) :
    ∃ C, 0 ≤ C ∧ ∀ v, ‖L v‖ ≤ C * ‖D v‖ := by
  set L' : LinearMap.range D →ₗ[ℝ] F :=
    (LinearMap.ker D).liftQ L h ∘ₗ D.quotKerEquivRange.symm.toLinearMap
  have hL' : ∀ v, L' ⟨D v, LinearMap.mem_range_self D v⟩ = L v := by
    intro v
    have e : D.quotKerEquivRange.symm ⟨D v, LinearMap.mem_range_self D v⟩ =
        Submodule.Quotient.mk v := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [L', LinearMap.comp_apply, LinearEquiv.coe_coe, e, Submodule.liftQ_apply]
  have hc : Continuous L' := LinearMap.continuous_of_finiteDimensional L'
  set Lc : LinearMap.range D →L[ℝ] F := ⟨L', hc⟩
  refine ⟨‖Lc‖, norm_nonneg Lc, fun v => ?_⟩
  rw [← hL']
  exact Lc.le_opNorm _

/-! ### `L²` norms of form fields -/

/-- The squared `L²(S)` norm `Σ_s ∫_S u_s²` of a form field (coefficients in the basis
`dx_s`). -/
def formL2Sq (S : Set (Fin n → ℝ)) (u : FormField n) : ℝ := ∑ s, ∫ x in S, (u x s) ^ 2

/-- The squared `L²(S)` norm `Σ_j Σ_s ∫_S (∂_j u_s)²` of the first derivatives of a form
field. -/
def formGradL2Sq (S : Set (Fin n → ℝ)) (u : FormField n) : ℝ :=
  ∑ j, ∑ s, ∫ x in S, (partialDeriv j (fun y => u y s) x) ^ 2

theorem formL2Sq_nonneg {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) (u : FormField n) :
    0 ≤ formL2Sq S u :=
  Finset.sum_nonneg fun _ _ => setIntegral_nonneg hS fun _ _ => sq_nonneg _

theorem formGradL2Sq_nonneg {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) (u : FormField n) :
    0 ≤ formGradL2Sq S u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    setIntegral_nonneg hS fun _ _ => sq_nonneg _

theorem memLp_coeff_of_continuous {S : Set (Fin n → ℝ)} (hS : IsCompact S) {u : FormField n}
    (hu : Continuous u) (s : Finset (Fin n)) :
    MemLp (fun y => u y s) 2 (volume.restrict S) :=
  Domain.memLp_of_continuous hS.measurableSet hS.isBounded ((continuous_apply s).comp hu)

/-- The `L²(S)` map of a space of continuous form fields (`S` compact). -/
def l2EmbedOf (V : Submodule ℝ (FormField n)) (hV : V ≤ contForms n) {S : Set (Fin n → ℝ)}
    (hS : IsCompact S) : V →ₗ[ℝ] Domain.L2F ℝ S (Finset (Fin n)) where
  toFun v := Domain.toL2F fun s => memLp_coeff_of_continuous hS (hV v.2) s
  map_add' v w := by
    refine PiLp.ext fun s => ?_
    rw [PiLp.add_apply]
    exact MemLp.toLp_add (memLp_coeff_of_continuous hS (hV v.2) s)
      (memLp_coeff_of_continuous hS (hV w.2) s)
  map_smul' c v := by
    refine PiLp.ext fun s => ?_
    rw [PiLp.smul_apply]
    exact MemLp.toLp_const_smul c (memLp_coeff_of_continuous hS (hV v.2) s)

theorem norm_sq_l2EmbedOf (V : Submodule ℝ (FormField n)) (hV : V ≤ contForms n)
    {S : Set (Fin n → ℝ)} (hS : IsCompact S) (v : V) :
    ‖l2EmbedOf V hV hS v‖ ^ 2 = formL2Sq S v := by
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ (l2EmbedOf V hV hS v) (Domain.toL2F _) = _
  rw [Domain.inner_toL2F]
  refine Finset.sum_congr rfl fun s _ => integral_congr_ae ?_
  have h := (memLp_coeff_of_continuous hS (hV v.2) s).coeFn_toLp
  filter_upwards [h] with y hy
  change (starRingEnd ℝ) ((memLp_coeff_of_continuous hS (hV v.2) s).toLp _ y) * _ = _
  rw [RCLike.conj_to_real, hy, sq]

theorem norm_l2EmbedOf (V : Submodule ℝ (FormField n)) (hV : V ≤ contForms n)
    {S : Set (Fin n → ℝ)} (hS : IsCompact S) (v : V) :
    ‖l2EmbedOf V hV hS v‖ = √(formL2Sq S v) := by
  rw [← norm_sq_l2EmbedOf V hV hS v, Real.sqrt_sq (norm_nonneg _)]

/-- The `L²(S)` map is injective on a space of continuous fields that vanish as soon as they
vanish on a nonempty open set, if `S` has nonempty interior. -/
theorem l2EmbedOf_injective (V : Submodule ℝ (FormField n)) (hV : V ≤ contForms n)
    (hV0 : ∀ v ∈ V, ∀ U : Set (Fin n → ℝ), IsOpen U → U.Nonempty → (∀ y ∈ U, v y = 0) → v = 0)
    {S : Set (Fin n → ℝ)} (hS : IsCompact S) (hSi : (interior S).Nonempty) :
    Function.Injective (l2EmbedOf V hV hS) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have hs : ∀ s, ∀ y ∈ interior S, (v : FormField n) y s = 0 := by
    intro s
    have h0 : (l2EmbedOf V hV hS v) s = 0 := by rw [hv]; rfl
    have h := (memLp_coeff_of_continuous hS (hV v.2) s).coeFn_toLp
    change (memLp_coeff_of_continuous hS (hV v.2) s).toLp _ = 0 at h0
    rw [h0] at h
    have hz := Lp.coeFn_zero ℝ 2 (volume.restrict S)
    have hae : (fun y => (v : FormField n) y s) =ᵐ[volume.restrict (interior S)] 0 :=
      ae_restrict_of_ae_restrict_of_subset interior_subset ((h.symm.trans hz))
    exact fun y hy => Measure.eqOn_open_of_ae_eq hae isOpen_interior
      ((continuous_apply s).comp (hV v.2 : Continuous (v : FormField n))).continuousOn
      continuousOn_const hy
  exact Subtype.ext (hV0 v v.2 _ isOpen_interior hSi fun y hy => funext fun s => hs s y hy)

/-! ### Polynomial form fields -/

/-- A polynomial vanishing on a nonempty open set vanishes. -/
theorem eq_zero_of_eval_eq_zero_of_isOpen {q : MvPolynomial (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    (hU : IsOpen U) {y₀ : Fin n → ℝ} (hy₀ : y₀ ∈ U) (h : ∀ y ∈ U, MvPolynomial.eval y q = 0) :
    q = 0 := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU y₀ hy₀
  refine MvPolynomial.funext_set (fun i => Set.Ioo (y₀ i - δ / 2) (y₀ i + δ / 2))
    (fun _ => Set.Ioo_infinite (by linarith)) fun x hx => ?_
  rw [map_zero]
  refine h x (hball ?_)
  rw [Metric.mem_ball, dist_pi_lt_iff hδ]
  intro i
  have hi := hx i (Set.mem_univ _)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hi.1, hi.2]

theorem isDeg_of_mem_polySpace {r k : ℕ} {u : FormField n} (hu : u ∈ polySpace n r k)
    (x : Fin n → ℝ) : IsDeg k (u x) := by
  obtain ⟨Ω, hΩ, rfl⟩ := hu
  intro s hs
  rw [evalForm_apply, hΩ.1 s hs, map_zero]

theorem polySpace_le_contForms (r k : ℕ) : polySpace n r k ≤ contForms n :=
  fun _ hu => (polySpace_le_c1 hu).continuous

/-- A polynomial form field vanishing on a nonempty open set vanishes. -/
theorem eq_zero_of_mem_polySpace_of_eqOn {r k : ℕ} {u : FormField n} (hu : u ∈ polySpace n r k)
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hne : U.Nonempty) (h : ∀ y ∈ U, u y = 0) : u = 0 := by
  obtain ⟨Ω, -, rfl⟩ := hu
  obtain ⟨y₀, hy₀⟩ := hne
  have : Ω = 0 := funext fun s => eq_zero_of_eval_eq_zero_of_isOpen hU hy₀ fun y hy => by
    have := congrFun (h y hy) s
    rwa [evalForm_apply] at this
  rw [this, map_zero]

theorem affinePullback_mem_polySpace_scalarMat {r k : ℕ} (h : ℝ) (t : Fin n → ℝ)
    {u : FormField n} (hu : u ∈ polySpace n r k) :
    affinePullback (scalarMat n h) t u ∈ polySpace n r k :=
  affinePullback_mem_polySpace _ _ hu

theorem affinePullback_mem_polyMinusSpace_scalarMat {r k : ℕ} (h : ℝ) (t : Fin n → ℝ)
    {u : FormField n} (hu : u ∈ polyMinusSpace n r k) :
    affinePullback (scalarMat n h) t u ∈ polyMinusSpace n r k :=
  affinePullback_mem_polyMinusSpace _ _ hu

/-! ### Reference estimates on a fixed compact set

`V` is any space of polynomial `k`-form fields of degree `≤ r` (`V ≤ P_rΛᵏ(ℝⁿ)`), e.g.
`P_rΛᵏ` itself or `P_r⁻Λᵏ` (`polyMinusSpace_le_polySpace`). -/

section Reference

variable {r k : ℕ} {V : Submodule ℝ (FormField n)}

theorem le_contForms_of_le_polySpace (hV : V ≤ polySpace n r k) : V ≤ contForms n :=
  hV.trans (polySpace_le_contForms r k)

theorem finiteDimensional_of_le_polySpace (hV : V ≤ polySpace n r k) : FiniteDimensional ℝ V :=
  Submodule.finiteDimensional_of_le hV

theorem l2EmbedOf_injective_of_le_polySpace (hV : V ≤ polySpace n r k) {S : Set (Fin n → ℝ)}
    (hS : IsCompact S) (hSi : (interior S).Nonempty) :
    Function.Injective (l2EmbedOf V (le_contForms_of_le_polySpace hV) hS) :=
  l2EmbedOf_injective V _
    (fun _ hv _ hU hne h0 => eq_zero_of_mem_polySpace_of_eqOn (hV hv) hU hne h0)
    hS hSi

/-- Evaluation `v ↦ v(x)` as a linear map on a space of form fields. -/
def evalₗ (V : Submodule ℝ (FormField n)) (x : Fin n → ℝ) : V →ₗ[ℝ] Finset (Fin n) → ℝ :=
  (LinearMap.proj x) ∘ₗ V.subtype

@[simp] theorem evalₗ_apply (V : Submodule ℝ (FormField n)) (x : Fin n → ℝ) (v : V) :
    evalₗ V x v = (v : FormField n) x := rfl

/-- **Reference inverse estimates** for polynomial forms: on a compact convex `S` with nonempty
interior (e.g. a nondegenerate simplex `K`), every `u ∈ V ≤ P_rΛᵏ` satisfies
`sup_S ‖u‖ ≤ A ‖u‖_{L²(S)}` and `Lip_S(u) ≤ A ‖u‖_{L²(S)}`, with `A` depending only on `S`
and `V`. -/
theorem exists_norm_le_sqrt_formL2Sq (hV : V ≤ polySpace n r k) {S : Set (Fin n → ℝ)}
    (hS : IsCompact S) (hSi : (interior S).Nonempty) (hSc : Convex ℝ S) :
    ∃ A, 0 ≤ A ∧ ∀ u ∈ V, (∀ x ∈ S, ‖u x‖ ≤ A * √(formL2Sq S u)) ∧
      (∀ x ∈ S, ∀ x' ∈ S, ‖u x - u x'‖ ≤ A * ‖x - x'‖ * √(formL2Sq S u)) := by
  have := finiteDimensional_of_le_polySpace hV
  set ι := l2EmbedOf V (le_contForms_of_le_polySpace hV) hS
  have hι := l2EmbedOf_injective_of_le_polySpace hV hS hSi
  -- sup bound
  obtain ⟨A₁, hA₁0, hA₁⟩ := exists_norm_le_mul_norm_of_bounded ι hι
    (fun x : S => evalₗ V x) fun v => by
      obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn
        (le_contForms_of_le_polySpace hV v.2 : Continuous (v : FormField n)).continuousOn
      exact ⟨C, fun x => hC x x.2⟩
  -- Lipschitz bound
  obtain ⟨A₂, hA₂0, hA₂⟩ := exists_norm_le_mul_weight_mul_norm ι hι
    (fun p : S × S => evalₗ V p.1 - evalₗ V p.2) (fun p => ‖(p.1 : Fin n → ℝ) - p.2‖)
    (fun _ => norm_nonneg _) fun v => by
      have hv : ContDiff ℝ ⊤ (v : FormField n) := polySpace_le_c1 (hV v.2)
      obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn
        (hv.continuous_fderiv (by simp)).continuousOn
      refine ⟨C, fun p => ?_⟩
      have h := hSc.norm_image_sub_le_of_norm_fderiv_le
        (fun x _ => (hv.differentiable (by simp)) x) hC p.2.2 p.1.2
      simpa using h
  refine ⟨max A₁ A₂, le_max_of_le_left hA₁0, fun u hu => ⟨fun x hx => ?_, fun x hx x' hx' => ?_⟩⟩
  · have h := hA₁ ⟨u, hu⟩ ⟨x, hx⟩
    rw [norm_l2EmbedOf] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  · have h := hA₂ ⟨u, hu⟩ (⟨x, hx⟩, ⟨x', hx'⟩)
    rw [norm_l2EmbedOf] at h
    simp only [LinearMap.sub_apply, evalₗ_apply] at h
    refine h.trans ?_
    gcongr
    exact le_max_right _ _

/-- **Reference DOF estimate**: for a unisolvent family of linear functionals `ℓⱼ` on `V`
(`LinearMap.pi ℓ` injective), `sup_S ‖u‖ ≤ B Σⱼ |ℓⱼ(u)|` on a compact `S`. -/
theorem exists_norm_le_sum_abs_dof (hV : V ≤ polySpace n r k) {S : Set (Fin n → ℝ)}
    (hS : IsCompact S) {J : Type*} [Fintype J] (ℓ : J → V →ₗ[ℝ] ℝ)
    (hℓ : Function.Injective (LinearMap.pi ℓ)) :
    ∃ B, 0 ≤ B ∧ ∀ u : V, ∀ x ∈ S, ‖(u : FormField n) x‖ ≤ B * ∑ j, |ℓ j u| := by
  have := finiteDimensional_of_le_polySpace hV
  obtain ⟨B, hB0, hB⟩ := exists_norm_le_mul_norm_of_bounded (LinearMap.pi ℓ) hℓ
    (fun x : S => evalₗ V x) fun v => by
      obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn
        (le_contForms_of_le_polySpace hV v.2 : Continuous (v : FormField n)).continuousOn
      exact ⟨C, fun x => hC x x.2⟩
  refine ⟨B, hB0, fun u x hx => (hB u ⟨x, hx⟩).trans (mul_le_mul_of_nonneg_left ?_ hB0)⟩
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).2 fun j => ?_
  rw [LinearMap.pi_apply, Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun j => |ℓ j u|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)

theorem sq_norm_pi_le_sum_sq {J : Type*} [Fintype J] (c : J → ℝ) : ‖c‖ ^ 2 ≤ ∑ j, c j ^ 2 := by
  have h : ‖c‖ ≤ √(∑ j, c j ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => c j ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j))
  calc ‖c‖ ^ 2 ≤ √(∑ j, c j ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- **Reference `ℓ²`-equivalence of the DOFs**: for a unisolvent family `ℓⱼ` on `V`, the squared
`L²(S)` norm and `Σⱼ ℓⱼ(u)²` are equivalent on `V` (`S` compact with nonempty interior). -/
theorem exists_formL2Sq_equiv_sum_sq_dof (hV : V ≤ polySpace n r k) {S : Set (Fin n → ℝ)}
    (hS : IsCompact S) (hSi : (interior S).Nonempty) {J : Type*} [Fintype J]
    (ℓ : J → V →ₗ[ℝ] ℝ) (hℓ : Function.Injective (LinearMap.pi ℓ)) :
    ∃ C, 0 ≤ C ∧ ∀ u : V, ∑ j, (ℓ j u) ^ 2 ≤ C * formL2Sq S u ∧
      formL2Sq S u ≤ C * ∑ j, (ℓ j u) ^ 2 := by
  have := finiteDimensional_of_le_polySpace hV
  set ι := l2EmbedOf V (le_contForms_of_le_polySpace hV) hS
  have hι := l2EmbedOf_injective_of_le_polySpace hV hS hSi
  obtain ⟨A, hA0, hA⟩ := exists_abs_le_mul_norm_of_finite ι hι ℓ
  obtain ⟨B, hB0, hB⟩ := exists_norm_le_mul_norm_of_bounded (LinearMap.pi ℓ) hℓ
    (fun _ : Unit => ι) fun v => ⟨‖ι v‖, fun _ => le_rfl⟩
  refine ⟨max (Fintype.card J * A ^ 2) (B ^ 2), le_max_of_le_right (sq_nonneg _),
    fun u => ⟨?_, ?_⟩⟩
  · have h1 : ∀ j, (ℓ j u) ^ 2 ≤ A ^ 2 * formL2Sq S u := fun j => by
      rw [← norm_sq_l2EmbedOf V (le_contForms_of_le_polySpace hV) hS u, ← mul_pow, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hA u j) 2
    calc ∑ j, (ℓ j u) ^ 2 ≤ ∑ _j : J, A ^ 2 * formL2Sq S u := Finset.sum_le_sum fun j _ => h1 j
      _ = Fintype.card J * A ^ 2 * formL2Sq S u := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _)
          (formL2Sq_nonneg hS.measurableSet _)
  · have h := hB u ()
    rw [← norm_sq_l2EmbedOf V (le_contForms_of_le_polySpace hV) hS u]
    calc ‖ι u‖ ^ 2 ≤ (B * ‖LinearMap.pi ℓ u‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = B ^ 2 * ‖LinearMap.pi ℓ u‖ ^ 2 := by ring
      _ ≤ max (Fintype.card J * A ^ 2) (B ^ 2) * ∑ j, (ℓ j u) ^ 2 :=
          mul_le_mul (le_max_right _ _) (sq_norm_pi_le_sum_sq _) (sq_nonneg _)
            (le_max_of_le_right (sq_nonneg _))

end Reference

/-! ### Pullback by a homothety -/

section Homothety

theorem affinePullback_scalarMat_apply_of_isDeg {k : ℕ} {h : ℝ} {t : Fin n → ℝ}
    {u : FormField n} (hu : ∀ x, IsDeg k (u x)) (y : Fin n → ℝ) :
    affinePullback (scalarMat n h) t u y = h ^ k • u (t + h • y) := by
  rw [affinePullback_scalarMat h t hu y, add_comm]

/-- `‖H^* u‖²_{L²(K)} = h^{2k - n} ‖u‖²_{L²(T)}` for a `k`-form and `T = t + h K`. -/
theorem formL2Sq_affinePullback_scalarMat (K : Affine.Simplex ℝ (Fin n → ℝ) n) {k : ℕ}
    {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {u : FormField n} (hu : ∀ x, IsDeg k (u x)) :
    h ^ n * formL2Sq K.closedInterior (affinePullback (scalarMat n h) t u) =
      (h ^ k) ^ 2 * formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior u := by
  simp only [formL2Sq, affinePullback_scalarMat_apply_of_isDeg hu, Pi.smul_apply, smul_eq_mul,
    integral_closedInterior_mapEquiv_boxMap K t hh, mul_pow, integral_const_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- Chain rule for the pullback of a `k`-form by `y ↦ t + h y`:
`∂ⱼ (H^* u)_s (y) = h^{k+1} (∂ⱼ u_s)(t + h y)`. -/
theorem partialDeriv_affinePullback_scalarMat {k : ℕ} {h : ℝ} {t : Fin n → ℝ}
    {u : FormField n} (hu : ∀ x, IsDeg k (u x)) (hd : Differentiable ℝ u) (j : Fin n)
    (s : Finset (Fin n)) (y : Fin n → ℝ) :
    partialDeriv j (fun z => affinePullback (scalarMat n h) t u z s) y =
      h ^ (k + 1) * partialDeriv j (fun x => u x s) (t + h • y) := by
  have hds : Differentiable ℝ (fun x => u x s) := fun x => differentiableAt_pi.1 (hd x) s
  have e : (fun z => affinePullback (scalarMat n h) t u z s) =
      fun z => h ^ k • (fun x => u x s) (affine (scalarMat n h) t z) := by
    funext z
    rw [affinePullback_scalarMat_apply_of_isDeg hu, affine_scalarMat, add_comm]
    rfl
  rw [e, partialDeriv_const_smul (f := fun z => (fun x => u x s) (affine (scalarMat n h) t z))
      ((hds _).comp _ (differentiable_affine _ _ _)),
    partialDeriv_comp_affine _ _ (hds _), affine_scalarMat, add_comm (h • y)]
  simp only [scalarMat, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    smul_eq_mul, pow_succ]
  ring

/-- `‖D H^* u‖²_{L²(K)} = h^{2k + 2 - n} ‖D u‖²_{L²(T)}` for a differentiable `k`-form and
`T = t + h K`. -/
theorem formGradL2Sq_affinePullback_scalarMat (K : Affine.Simplex ℝ (Fin n → ℝ) n) {k : ℕ}
    {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {u : FormField n} (hu : ∀ x, IsDeg k (u x))
    (hd : Differentiable ℝ u) :
    h ^ n * formGradL2Sq K.closedInterior (affinePullback (scalarMat n h) t u) =
      (h ^ (k + 1)) ^ 2 * formGradL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior u := by
  simp only [formGradL2Sq, partialDeriv_affinePullback_scalarMat hu hd,
    integral_closedInterior_mapEquiv_boxMap K t hh, mul_pow, integral_const_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => by ring

theorem sqrt_mul_sqrt_eq_of_mul_eq {a b c d : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hrel : a * b = c ^ 2 * d) : √a * √b = c * √d := by
  rw [← Real.sqrt_mul ha, hrel, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]

theorem mem_mapEquiv_boxMap {K : Affine.Simplex ℝ (Fin n → ℝ) n} {h : ℝ} (hh : h ≠ 0)
    {t x : Fin n → ℝ} (hx : x ∈ (mapEquiv (boxMap t h hh) K).closedInterior) :
    ∃ y ∈ K.closedInterior, t + h • y = x := by
  rw [closedInterior_mapEquiv_boxMap] at hx
  exact hx

variable {r k : ℕ} {V : Submodule ℝ (FormField n)}

/-- **Local inverse estimates on homothetic simplices** for polynomial forms: for `T = t + h K`
and `u ∈ V ≤ P_rΛᵏ` (`V` stable under homotheties),
`h^{n/2} sup_T ‖u‖ ≤ A ‖u‖_{L²(T)}` and `h^{n/2} h Lip_T(u) ≤ A ‖u‖_{L²(T)}`, with `A`
depending only on `K` and `V` ([Ciarlet2002], §3.2; [AFW2010], §5.4). -/
theorem exists_local_inverse_bound_of_le_polySpace (hV : V ≤ polySpace n r k)
    (hVH : ∀ (h : ℝ) (t : Fin n → ℝ), ∀ u ∈ V, affinePullback (scalarMat n h) t u ∈ V)
    (K : Affine.Simplex ℝ (Fin n → ℝ) n) :
    ∃ A, 0 ≤ A ∧ ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ), ∀ u ∈ V,
      (∀ x ∈ (mapEquiv (boxMap t h hh.ne') K).closedInterior,
        √h ^ n * ‖u x‖ ≤ A * √(formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior u)) ∧
      (∀ x ∈ (mapEquiv (boxMap t h hh.ne') K).closedInterior,
        ∀ x' ∈ (mapEquiv (boxMap t h hh.ne') K).closedInterior,
        √h ^ n * h * ‖u x - u x'‖ ≤
          A * ‖x - x'‖ * √(formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior u)) := by
  obtain ⟨A, hA0, hA⟩ := exists_norm_le_sqrt_formL2Sq hV K.isCompact_closedInterior
    (interior_closedInterior_nonempty K) (convex_closedInterior K)
  refine ⟨A, hA0, fun {h} hh t u hu => ?_⟩
  set T := mapEquiv (boxMap t h hh.ne') K
  set v := affinePullback (scalarMat n h) t u
  have hdeg := isDeg_of_mem_polySpace (hV hu)
  have hv : ∀ y, v y = h ^ k • u (t + h • y) := affinePullback_scalarMat_apply_of_isDeg hdeg
  obtain ⟨hA1, hA2⟩ := hA v (hVH h t u hu)
  have hhk : 0 < h ^ k := pow_pos hh k
  have hsq : 0 ≤ √h ^ n := pow_nonneg (Real.sqrt_nonneg _) n
  have hkey : √h ^ n * √(formL2Sq K.closedInterior v) = h ^ k * √(formL2Sq T.closedInterior u) := by
    rw [← sqrt_pow_eq hh.le]
    exact sqrt_mul_sqrt_eq_of_mul_eq (pow_nonneg hh.le n) hhk.le
      (formL2Sq_affinePullback_scalarMat K hh t hdeg)
  constructor
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_mapEquiv_boxMap hh.ne' hx
    have h1 := hA1 y hy
    rw [hv, norm_smul, Real.norm_of_nonneg hhk.le] at h1
    refine le_of_mul_le_mul_left ?_ hhk
    calc h ^ k * (√h ^ n * ‖u (t + h • y)‖) = √h ^ n * (h ^ k * ‖u (t + h • y)‖) := by ring
      _ ≤ √h ^ n * (A * √(formL2Sq K.closedInterior v)) := mul_le_mul_of_nonneg_left h1 hsq
      _ = A * (√h ^ n * √(formL2Sq K.closedInterior v)) := by ring
      _ = h ^ k * (A * √(formL2Sq T.closedInterior u)) := by rw [hkey]; ring
  · intro x hx x' hx'
    obtain ⟨y, hy, rfl⟩ := mem_mapEquiv_boxMap hh.ne' hx
    obtain ⟨y', hy', rfl⟩ := mem_mapEquiv_boxMap hh.ne' hx'
    have h2 := hA2 y hy y' hy'
    rw [hv, hv, ← smul_sub, norm_smul, Real.norm_of_nonneg hhk.le] at h2
    have hyy : ‖t + h • y - (t + h • y')‖ = h * ‖y - y'‖ := by
      rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg hh.le]
    rw [hyy]
    refine le_of_mul_le_mul_left ?_ hhk
    calc h ^ k * (√h ^ n * h * ‖u (t + h • y) - u (t + h • y')‖)
        = √h ^ n * h * (h ^ k * ‖u (t + h • y) - u (t + h • y')‖) := by ring
      _ ≤ √h ^ n * h * (A * ‖y - y'‖ * √(formL2Sq K.closedInterior v)) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hsq hh.le)
      _ = A * (h * ‖y - y'‖) * (√h ^ n * √(formL2Sq K.closedInterior v)) := by ring
      _ = h ^ k * (A * (h * ‖y - y'‖) * √(formL2Sq T.closedInterior u)) := by rw [hkey]; ring

/-- **Local DOF estimate on homothetic simplices**: for a unisolvent family `ℓⱼ` on `V` (the
DOFs on `K`) and `T = t + h K`, `hᵏ sup_T ‖u‖ ≤ B Σⱼ |ℓⱼ(H^* u)|`, `H y = t + h y`, with `B`
depending only on `K` and `ℓ`. For moment DOFs, `ℓⱼ(H^* u)` is the corresponding moment of `u`
on `T` (`faceMoment_mapEquiv_boxMap`, `affineMoment_homothety`). -/
theorem exists_local_dof_bound_of_le_polySpace (hV : V ≤ polySpace n r k)
    (hVH : ∀ (h : ℝ) (t : Fin n → ℝ), ∀ u ∈ V, affinePullback (scalarMat n h) t u ∈ V)
    (K : Affine.Simplex ℝ (Fin n → ℝ) n) {J : Type*} [Fintype J] (ℓ : J → V →ₗ[ℝ] ℝ)
    (hℓ : Function.Injective (LinearMap.pi ℓ)) :
    ∃ B, 0 ≤ B ∧ ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) (u : FormField n) (hu : u ∈ V),
      ∀ x ∈ (mapEquiv (boxMap t h hh.ne') K).closedInterior,
        h ^ k * ‖u x‖ ≤ B * ∑ j, |ℓ j ⟨affinePullback (scalarMat n h) t u, hVH h t u hu⟩| := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_le_sum_abs_dof hV K.isCompact_closedInterior ℓ hℓ
  refine ⟨B, hB0, fun {h} hh t u hu x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := mem_mapEquiv_boxMap hh.ne' hx
  have h1 := hB ⟨affinePullback (scalarMat n h) t u, hVH h t u hu⟩ y hy
  change ‖affinePullback (scalarMat n h) t u y‖ ≤ _ at h1
  rwa [affinePullback_scalarMat_apply_of_isDeg (isDeg_of_mem_polySpace (hV hu)), norm_smul,
    Real.norm_of_nonneg (pow_nonneg hh.le k)] at h1

/-- **`ℓ²`-scaling of the DOFs on homothetic simplices** (the corrected tool behind
[QuennevilleBelair2015], Prop 5.8): for a unisolvent family `ℓⱼ` on `V` and `T = t + h K`,
`‖u‖²_{L²(T)} ≍ h^{n - 2k} Σⱼ ℓⱼ(H^* u)²`, i.e.
`h^{2k} ‖u‖²_{L²(T)} ≤ C hⁿ Σⱼ ℓⱼ(H^* u)²` and `hⁿ Σⱼ ℓⱼ(H^* u)² ≤ C h^{2k} ‖u‖²_{L²(T)}`,
with `C` depending only on `K` and `ℓ`. -/
theorem exists_local_formL2Sq_equiv_of_le_polySpace (hV : V ≤ polySpace n r k)
    (hVH : ∀ (h : ℝ) (t : Fin n → ℝ), ∀ u ∈ V, affinePullback (scalarMat n h) t u ∈ V)
    (K : Affine.Simplex ℝ (Fin n → ℝ) n) {J : Type*} [Fintype J] (ℓ : J → V →ₗ[ℝ] ℝ)
    (hℓ : Function.Injective (LinearMap.pi ℓ)) :
    ∃ C, 0 ≤ C ∧ ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) (u : FormField n) (hu : u ∈ V),
      (h ^ k) ^ 2 * formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior u ≤
          C * (h ^ n * ∑ j, (ℓ j ⟨affinePullback (scalarMat n h) t u, hVH h t u hu⟩) ^ 2) ∧
        h ^ n * ∑ j, (ℓ j ⟨affinePullback (scalarMat n h) t u, hVH h t u hu⟩) ^ 2 ≤
          C * ((h ^ k) ^ 2 * formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior u) := by
  obtain ⟨C, hC0, hC⟩ := exists_formL2Sq_equiv_sum_sq_dof hV K.isCompact_closedInterior
    (interior_closedInterior_nonempty K) ℓ hℓ
  refine ⟨C, hC0, fun {h} hh t u hu => ?_⟩
  have hrel := formL2Sq_affinePullback_scalarMat K hh t (isDeg_of_mem_polySpace (hV hu))
  obtain ⟨h1, h2⟩ := hC ⟨affinePullback (scalarMat n h) t u, hVH h t u hu⟩
  have hn : 0 ≤ h ^ n := pow_nonneg hh.le n
  constructor
  · rw [← hrel]
    calc h ^ n * formL2Sq K.closedInterior (affinePullback (scalarMat n h) t u)
        ≤ h ^ n * (C * _) := mul_le_mul_of_nonneg_left h2 hn
      _ = _ := by ring
  · rw [← hrel]
    calc h ^ n * _ ≤ h ^ n * (C * formL2Sq K.closedInterior
          (affinePullback (scalarMat n h) t u)) := mul_le_mul_of_nonneg_left h1 hn
      _ = _ := by ring

end Homothety

/-! ### Moment degrees of freedom under affine maps -/

section Moments

/-- **Traces under affine maps**: the trace on the face `G ∘ p ∘ e` of the affine image
`G ∘ p` (`G y = A y + a`) is the trace of `G^* ω` on the face `p ∘ e`. -/
theorem faceTrace_affine {m : ℕ} (A : Fin n → Fin n → ℝ) (a : Fin n → ℝ)
    (p : Fin (n + 1) → Fin n → ℝ) (e : Fin (m + 1) → Fin (n + 1)) (ω : FormField n) :
    faceTrace (fun i => affine A a (p i)) e ω = faceTrace p e (affinePullback A a ω) := by
  rw [faceTrace_apply, faceTrace_apply, affinePullback_affinePullback]
  have h : ((fun i => affine A a (p i)) ∘ e) = fun i => affine A a ((p ∘ e) i) := rfl
  rw [h, simplexMatrix_comp_affine]

/-- **Moments under affine maps**: `∫_{G(f)} tr ω ∧ η = ∫_f tr (G^* ω) ∧ η`, for every face
(every vertex map `e`, hence every ordering of the vertices) and every test form `η`. -/
theorem faceMoment_affine {m : ℕ} (A : Fin n → Fin n → ℝ) (a : Fin n → ℝ)
    (p : Fin (n + 1) → Fin n → ℝ) (e : Fin (m + 1) → Fin (n + 1)) (η : FormField m)
    (ω : FormField n) :
    faceMoment (fun i => affine A a (p i)) e η ω = faceMoment p e η (affinePullback A a ω) := by
  rw [faceMoment, faceMoment, faceTrace_affine]

theorem points_mapEquiv_boxMap (K : Affine.Simplex ℝ (Fin n → ℝ) n) (t : Fin n → ℝ) {h : ℝ}
    (hh : h ≠ 0) :
    (mapEquiv (boxMap t h hh) K).points = fun i => affine (scalarMat n h) t (K.points i) := by
  funext i
  rw [mapEquiv_points, boxMap_apply, affine_scalarMat, add_comm]

/-- **Moments on `T = t + h K`**: every moment on a face of `T` is the moment of `H^* ω` on the
corresponding face of `K` (`H y = t + h y`). -/
theorem faceMoment_mapEquiv_boxMap (K : Affine.Simplex ℝ (Fin n → ℝ) n) (t : Fin n → ℝ)
    {h : ℝ} (hh : h ≠ 0) {m : ℕ} (e : Fin (m + 1) → Fin (n + 1)) (η : FormField m)
    (ω : FormField n) :
    faceMoment (mapEquiv (boxMap t h hh) K).points e η ω =
      faceMoment K.points e η (affinePullback (scalarMat n h) t ω) := by
  rw [points_mapEquiv_boxMap, faceMoment_affine]

/-- The moment `ω ↦ ∫_{T̂_m} (F^* ω ∧ η)_{univ}` along an arbitrary affine parametrization
`F x̂ = B x̂ + b` of an `m`-dimensional face. -/
def affineMoment {m : ℕ} (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (η : FormField m)
    (ω : FormField n) : ℝ :=
  simplexIntegral (refVertex m) (wedgeField (affinePullback B b ω) η)

theorem faceMoment_eq_affineMoment {m : ℕ} (p : Fin (n + 1) → Fin n → ℝ)
    (e : Fin (m + 1) → Fin (n + 1)) (η : FormField m) (ω : FormField n) :
    faceMoment p e η ω = affineMoment (simplexMatrix (p ∘ e)) (p (e 0)) η ω := rfl

/-- **Moments along affine parametrizations under homotheties**: the moment along
`H ∘ F` (`H y = t + h y`, `F x̂ = B x̂ + b`, so `H ∘ F x̂ = h B x̂ + (t + h b)`) is the moment of
`H^* ω` along `F`. This covers every moment DOF on `T = t + h K` whatever the parametrization of
the faces of `K`. -/
theorem affineMoment_homothety {m : ℕ} (B : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (h : ℝ)
    (t : Fin n → ℝ) (η : FormField m) (ω : FormField n) :
    affineMoment (fun i l => h * B i l) (t + h • b) η ω =
      affineMoment B b η (affinePullback (scalarMat n h) t ω) := by
  rw [affineMoment, affineMoment, affinePullback_affinePullback, affine_scalarMat, add_comm]
  congr 3
  funext i l
  simp [scalarMat]

end Moments

/-! ### The moment DOFs of `P_rΛᵏ` and `P_r⁻Λᵏ` on homothetic simplices -/

section LocalDof

variable {r k : ℕ}

/-- The DOFs `ω ↦ ∫_f tr_f ω ∧ ηᵢ` of `P_rΛᵏ(K)` ([AFW2006], §4.5), as functionals on
`P_rΛᵏ(ℝⁿ) = P_rΛᵏ(K)`. -/
def polyDofOn (K : Affine.Simplex ℝ (Fin n → ℝ) n) (r k : ℕ)
    (i : Σ f : Face n, DofIndex r k f) : polySpace n r k →ₗ[ℝ] ℝ :=
  localDof K.points r k i ∘ₗ
    (LinearEquiv.ofEq _ _ (localPolySpace_eq (isUnit_det_edgeMatrix K) r k).symm).toLinearMap

/-- The DOFs of `P_r⁻Λᵏ(K)` ([AFW2006], §4.6), as functionals on `P_r⁻Λᵏ(ℝⁿ)`. -/
def polyMinusDofOn (K : Affine.Simplex ℝ (Fin n → ℝ) n) (r k : ℕ)
    (i : Σ f : Face n, DofIndexMinus r k f) : polyMinusSpace n r k →ₗ[ℝ] ℝ :=
  localDofMinus K.points r k i ∘ₗ
    (LinearEquiv.ofEq _ _ (localPolyMinusSpace_eq (isUnit_det_edgeMatrix K) r k).symm).toLinearMap

theorem polyDofOn_apply (K : Affine.Simplex ℝ (Fin n → ℝ) n) (i : Σ f : Face n, DofIndex r k f)
    (u : polySpace n r k) :
    polyDofOn K r k i u =
      faceMoment K.points i.1.emb (testBasis r k i.1.dim i.2 : FormField i.1.dim) u := rfl

theorem polyMinusDofOn_apply (K : Affine.Simplex ℝ (Fin n → ℝ) n)
    (i : Σ f : Face n, DofIndexMinus r k f) (u : polyMinusSpace n r k) :
    polyMinusDofOn K r k i u =
      faceMoment K.points i.1.emb (testBasisMinus r k i.1.dim i.2 : FormField i.1.dim) u := rfl

theorem injective_pi_polyDofOn (K : Affine.Simplex ℝ (Fin n → ℝ) n) (hr : 1 ≤ r) (hk : k ≤ n) :
    Function.Injective (LinearMap.pi (polyDofOn K r k)) := by
  intro u v huv
  have h := (isUnisolvent_localDof (isUnit_det_edgeMatrix K) hr hk).ext fun i =>
    congrFun huv i
  exact (LinearEquiv.ofEq _ _ _).injective h

theorem injective_pi_polyMinusDofOn (K : Affine.Simplex ℝ (Fin n → ℝ) n) (hr : 1 ≤ r)
    (hk : k ≤ n) : Function.Injective (LinearMap.pi (polyMinusDofOn K r k)) := by
  intro u v huv
  have h := (isUnisolvent_localDofMinus (isUnit_det_edgeMatrix K) hr hk).ext fun i =>
    congrFun huv i
  exact (LinearEquiv.ofEq _ _ _).injective h

/-- **DOF estimate for `P_rΛᵏ` on `T = t + h K`**: `hᵏ sup_T ‖u‖ ≤ B Σᵢ |ℓᵢᵀ(u)|`, where
`ℓᵢᵀ(u) = ∫_f tr_f u ∧ ηᵢ` are the moment DOFs on the faces of `T` (vertices `t + h pⱼ`, in the
order of `K`), and `B` depends only on `K`, `r`, `k`. -/
theorem exists_local_dof_bound_polySpace (K : Affine.Simplex ℝ (Fin n → ℝ) n) (hr : 1 ≤ r)
    (hk : k ≤ n) :
    ∃ B, 0 ≤ B ∧ ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {u : FormField n},
      u ∈ polySpace n r k → ∀ x ∈ (mapEquiv (boxMap t h hh.ne') K).closedInterior,
        h ^ k * ‖u x‖ ≤ B * ∑ i : Σ f : Face n, DofIndex r k f,
          |faceMoment (mapEquiv (boxMap t h hh.ne') K).points i.1.emb
            (testBasis r k i.1.dim i.2 : FormField i.1.dim) u| := by
  obtain ⟨B, hB0, hB⟩ := exists_local_dof_bound_of_le_polySpace le_rfl
    (fun h t _ hu => affinePullback_mem_polySpace_scalarMat h t hu) K (polyDofOn K r k)
    (injective_pi_polyDofOn K hr hk)
  refine ⟨B, hB0, fun {h} hh t u hu x hx => (hB hh t u hu x hx).trans_eq ?_⟩
  simp only [polyDofOn_apply, faceMoment_mapEquiv_boxMap]

/-- **DOF estimate for `P_r⁻Λᵏ` on `T = t + h K`** (moment DOFs of the trimmed family). -/
theorem exists_local_dof_bound_polyMinusSpace (K : Affine.Simplex ℝ (Fin n → ℝ) n)
    (hr : 1 ≤ r) (hk : k ≤ n) :
    ∃ B, 0 ≤ B ∧ ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {u : FormField n},
      u ∈ polyMinusSpace n r k → ∀ x ∈ (mapEquiv (boxMap t h hh.ne') K).closedInterior,
        h ^ k * ‖u x‖ ≤ B * ∑ i : Σ f : Face n, DofIndexMinus r k f,
          |faceMoment (mapEquiv (boxMap t h hh.ne') K).points i.1.emb
            (testBasisMinus r k i.1.dim i.2 : FormField i.1.dim) u| := by
  obtain ⟨B, hB0, hB⟩ := exists_local_dof_bound_of_le_polySpace (polyMinusSpace_le_polySpace hr)
    (fun h t _ hu => affinePullback_mem_polyMinusSpace_scalarMat h t hu) K
    (polyMinusDofOn K r k) (injective_pi_polyMinusDofOn K hr hk)
  refine ⟨B, hB0, fun {h} hh t u hu x hx => (hB hh t u hu x hx).trans_eq ?_⟩
  simp only [polyMinusDofOn_apply, faceMoment_mapEquiv_boxMap]

/-- **`ℓ²`-scaling of the DOFs of `P_rΛᵏ` on `T = t + h K`** (the corrected form of
[QuennevilleBelair2015], Prop 5.8): `‖u‖²_{L²(T)} ≍ h^{n - 2k} Σᵢ ℓᵢᵀ(u)²`. -/
theorem exists_local_formL2Sq_equiv_polySpace (K : Affine.Simplex ℝ (Fin n → ℝ) n)
    (hr : 1 ≤ r) (hk : k ≤ n) :
    ∃ C, 0 ≤ C ∧ ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {u : FormField n},
      u ∈ polySpace n r k →
      (h ^ k) ^ 2 * formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior u ≤
          C * (h ^ n * ∑ i : Σ f : Face n, DofIndex r k f,
            (faceMoment (mapEquiv (boxMap t h hh.ne') K).points i.1.emb
              (testBasis r k i.1.dim i.2 : FormField i.1.dim) u) ^ 2) ∧
        h ^ n * ∑ i : Σ f : Face n, DofIndex r k f,
            (faceMoment (mapEquiv (boxMap t h hh.ne') K).points i.1.emb
              (testBasis r k i.1.dim i.2 : FormField i.1.dim) u) ^ 2 ≤
          C * ((h ^ k) ^ 2 * formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior u) := by
  obtain ⟨C, hC0, hC⟩ := exists_local_formL2Sq_equiv_of_le_polySpace le_rfl
    (fun h t _ hu => affinePullback_mem_polySpace_scalarMat h t hu) K (polyDofOn K r k)
    (injective_pi_polyDofOn K hr hk)
  refine ⟨C, hC0, fun {h} hh t u hu => ?_⟩
  have e : ∀ i : Σ f : Face n, DofIndex r k f,
      faceMoment (mapEquiv (boxMap t h hh.ne') K).points i.1.emb
        (testBasis r k i.1.dim i.2 : FormField i.1.dim) u =
      polyDofOn K r k i ⟨affinePullback (scalarMat n h) t u,
        affinePullback_mem_polySpace_scalarMat h t hu⟩ := fun i => by
    rw [polyDofOn_apply, faceMoment_mapEquiv_boxMap]
  simp only [e]
  exact hC hh t u hu

/-- **`ℓ²`-scaling of the DOFs of `P_r⁻Λᵏ` on `T = t + h K`**. -/
theorem exists_local_formL2Sq_equiv_polyMinusSpace (K : Affine.Simplex ℝ (Fin n → ℝ) n)
    (hr : 1 ≤ r) (hk : k ≤ n) :
    ∃ C, 0 ≤ C ∧ ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) {u : FormField n},
      u ∈ polyMinusSpace n r k →
      (h ^ k) ^ 2 * formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior u ≤
          C * (h ^ n * ∑ i : Σ f : Face n, DofIndexMinus r k f,
            (faceMoment (mapEquiv (boxMap t h hh.ne') K).points i.1.emb
              (testBasisMinus r k i.1.dim i.2 : FormField i.1.dim) u) ^ 2) ∧
        h ^ n * ∑ i : Σ f : Face n, DofIndexMinus r k f,
            (faceMoment (mapEquiv (boxMap t h hh.ne') K).points i.1.emb
              (testBasisMinus r k i.1.dim i.2 : FormField i.1.dim) u) ^ 2 ≤
          C * ((h ^ k) ^ 2 * formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior u) := by
  obtain ⟨C, hC0, hC⟩ := exists_local_formL2Sq_equiv_of_le_polySpace
    (polyMinusSpace_le_polySpace hr)
    (fun h t _ hu => affinePullback_mem_polyMinusSpace_scalarMat h t hu) K
    (polyMinusDofOn K r k) (injective_pi_polyMinusDofOn K hr hk)
  refine ⟨C, hC0, fun {h} hh t u hu => ?_⟩
  have e : ∀ i : Σ f : Face n, DofIndexMinus r k f,
      faceMoment (mapEquiv (boxMap t h hh.ne') K).points i.1.emb
        (testBasisMinus r k i.1.dim i.2 : FormField i.1.dim) u =
      polyMinusDofOn K r k i ⟨affinePullback (scalarMat n h) t u,
        affinePullback_mem_polyMinusSpace_scalarMat h t hu⟩ := fun i => by
    rw [polyMinusDofOn_apply, faceMoment_mapEquiv_boxMap]
  simp only [e]
  exact hC hh t u hu

end LocalDof

/-! ### The kernel lemma -/

section Kernel

variable {r k : ℕ} {V : Submodule ℝ (FormField n)}

theorem differentiable_coeff_of_mem_polySpace {u : FormField n} (hu : u ∈ polySpace n r k)
    (s : Finset (Fin n)) : Differentiable ℝ (fun y => u y s) := by
  obtain ⟨Ω, -, rfl⟩ := hu
  exact differentiable_eval (Ω s)

theorem partialDeriv_coeff_evalForm (Ω : Koszul.PolyForm ℝ (Fin n)) (j : Fin n)
    (s : Finset (Fin n)) :
    partialDeriv j (fun y => evalForm n Ω y s) = fun x => MvPolynomial.eval x
      (MvPolynomial.pderiv j (Ω s)) :=
  funext fun x => partialDeriv_eval (Ω s) j x

theorem continuous_partialDeriv_coeff_of_mem_polySpace {u : FormField n}
    (hu : u ∈ polySpace n r k) (j : Fin n) (s : Finset (Fin n)) :
    Continuous (partialDeriv j (fun y => u y s)) := by
  obtain ⟨Ω, -, rfl⟩ := hu
  rw [partialDeriv_coeff_evalForm]
  exact (differentiable_eval _).continuous

/-- The first derivatives `(∂ⱼ v_s)_{j, s}` of the fields of `V ≤ P_rΛᵏ`, in `L²(S)`. -/
def gradEmbed (hV : V ≤ polySpace n r k) {S : Set (Fin n → ℝ)} (hS : IsCompact S) :
    V →ₗ[ℝ] Domain.L2F ℝ S (Fin n × Finset (Fin n)) where
  toFun v := Domain.toL2F fun p => Domain.memLp_of_continuous hS.measurableSet hS.isBounded
    (continuous_partialDeriv_coeff_of_mem_polySpace (hV v.2) p.1 p.2)
  map_add' v w := by
    refine PiLp.ext fun p => ?_
    simp only [Domain.toL2F, PiLp.add_apply, PiLp.toLp_apply]
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => ?_)
    exact partialDeriv_add (differentiable_coeff_of_mem_polySpace (hV v.2) p.2 x)
      (differentiable_coeff_of_mem_polySpace (hV w.2) p.2 x) p.1
  map_smul' c v := by
    refine PiLp.ext fun p => ?_
    simp only [Domain.toL2F, PiLp.smul_apply, PiLp.toLp_apply, RingHom.id_apply]
    rw [← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => ?_)
    exact partialDeriv_const_smul (differentiable_coeff_of_mem_polySpace (hV v.2) p.2 x) c p.1

theorem norm_gradEmbed (hV : V ≤ polySpace n r k) {S : Set (Fin n → ℝ)} (hS : IsCompact S)
    (v : V) : ‖gradEmbed hV hS v‖ = √(formGradL2Sq S v) := by
  rw [← Real.sqrt_sq (norm_nonneg (gradEmbed hV hS v)), ← real_inner_self_eq_norm_sq]
  congr 1
  change inner ℝ (gradEmbed hV hS v) (Domain.toL2F _) = _
  rw [Domain.inner_toL2F, formGradL2Sq, ← Fintype.sum_prod_type']
  refine Finset.sum_congr rfl fun p _ => integral_congr_ae ?_
  have h := (Domain.memLp_of_continuous hS.measurableSet hS.isBounded
    (continuous_partialDeriv_coeff_of_mem_polySpace (hV v.2) p.1 p.2)).coeFn_toLp
  filter_upwards [h] with y hy
  change (starRingEnd ℝ) ((Domain.memLp_of_continuous hS.measurableSet hS.isBounded
    (continuous_partialDeriv_coeff_of_mem_polySpace (hV v.2) p.1 p.2)).toLp _ y) * _ = _
  rw [RCLike.conj_to_real, hy, sq]

/-- A field of `V ≤ P_rΛᵏ` whose first derivatives vanish in `L²(S)` (`S` with nonempty
interior) is constant. -/
theorem eq_const_of_gradEmbed_eq_zero (hV : V ≤ polySpace n r k) {S : Set (Fin n → ℝ)}
    (hS : IsCompact S) (hSi : (interior S).Nonempty) {v : V} (hv : gradEmbed hV hS v = 0)
    (x : Fin n → ℝ) : (v : FormField n) x = (v : FormField n) 0 := by
  obtain ⟨Ω, -, hΩ⟩ := hV v.2
  have hpd : ∀ j s, MvPolynomial.pderiv j (Ω s) = 0 := by
    intro j s
    have hc := continuous_partialDeriv_coeff_of_mem_polySpace (hV v.2) j s
    have hmem := Domain.memLp_of_continuous hS.measurableSet hS.isBounded hc
    have h0 : (gradEmbed hV hS v) (j, s) = 0 := by rw [hv]; rfl
    have h := hmem.coeFn_toLp
    change hmem.toLp _ = 0 at h0
    rw [h0] at h
    have hz := Lp.coeFn_zero ℝ 2 (volume.restrict S)
    have hae : partialDeriv j (fun y => (v : FormField n) y s) =ᵐ[volume.restrict (interior S)] 0 :=
      ae_restrict_of_ae_restrict_of_subset interior_subset ((h.symm.trans hz))
    obtain ⟨y₀, hy₀⟩ := hSi
    refine eq_zero_of_eval_eq_zero_of_isOpen isOpen_interior hy₀ fun y hy => ?_
    have := Measure.eqOn_open_of_ae_eq hae isOpen_interior hc.continuousOn continuousOn_const hy
    rw [← hΩ, partialDeriv_coeff_evalForm] at this
    exact this
  funext s
  refine is_const_of_fderiv_eq_zero (differentiable_coeff_of_mem_polySpace (hV v.2) s)
    (fun y => ?_) x 0
  refine ContinuousLinearMap.ext fun z => ?_
  rw [fderiv_apply_eq_sum_partialDeriv, zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← hΩ, partialDeriv_coeff_evalForm]
  simp [hpd]

/-- **The kernel lemma on a reference set** (behind [QuennevilleBelair2015], Prop 5.9(1); the
finite-dimensional form of the Bramble–Hilbert argument): if `L : V → W` is linear
(`V, W` spaces of polynomial forms) and vanishes on the constant fields of `V`, then
`‖L v‖_{L²(S)} ≤ C ‖Dv‖_{L²(S)}` (`S` compact with nonempty interior). -/
theorem exists_formL2Sq_le_formGradL2Sq {r' k' : ℕ} {W : Submodule ℝ (FormField n)}
    (hV : V ≤ polySpace n r k) (hW : W ≤ polySpace n r' k') (L : V →ₗ[ℝ] W)
    (hL : ∀ v : V, (∀ x, (v : FormField n) x = (v : FormField n) 0) → L v = 0)
    {S : Set (Fin n → ℝ)} (hS : IsCompact S) (hSi : (interior S).Nonempty) :
    ∃ C, 0 ≤ C ∧ ∀ v : V, √(formL2Sq S (L v)) ≤ C * √(formGradL2Sq S v) := by
  have := finiteDimensional_of_le_polySpace hV
  obtain ⟨C, hC0, hC⟩ := exists_norm_le_mul_norm_of_ker_le (gradEmbed hV hS)
    (l2EmbedOf W (le_contForms_of_le_polySpace hW) hS ∘ₗ L) fun v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [LinearMap.comp_apply, hL v (eq_const_of_gradEmbed_eq_zero hV hS hSi hv), map_zero]
  refine ⟨C, hC0, fun v => ?_⟩
  have h := hC v
  rwa [LinearMap.comp_apply, norm_l2EmbedOf, norm_gradEmbed] at h

/-- **The kernel lemma on homothetic simplices** (behind [QuennevilleBelair2015], Prop 5.9(1)):
let `L : V → W` (`V, W ≤ P Λᵏ` polynomial `k`-forms, `V` stable under homotheties) vanish on
the constant fields of `V`. For `T = t + h K` and `u ∈ V`, any `k`-form `w` with
`H^* w = L(H^* u)` (`H y = t + h y`; e.g. `w = L_T u` for the homothetic conjugate `L_T`, such as
`u - Π_T u` for local projections `Π_T` reproducing constants) satisfies
`‖w‖_{L²(T)} ≤ C h ‖Du‖_{L²(T)}`, `C` depending only on `K` and `L`. -/
theorem exists_local_kernel_bound {r' : ℕ} {W : Submodule ℝ (FormField n)}
    (hV : V ≤ polySpace n r k)
    (hVH : ∀ (h : ℝ) (t : Fin n → ℝ), ∀ u ∈ V, affinePullback (scalarMat n h) t u ∈ V)
    (hW : W ≤ polySpace n r' k) (L : V →ₗ[ℝ] W)
    (hL : ∀ v : V, (∀ x, (v : FormField n) x = (v : FormField n) 0) → L v = 0)
    (K : Affine.Simplex ℝ (Fin n → ℝ) n) :
    ∃ C, 0 ≤ C ∧ ∀ {h : ℝ} (hh : 0 < h) (t : Fin n → ℝ) (u : FormField n) (hu : u ∈ V)
      (w : FormField n), (∀ x, IsDeg k (w x)) →
      affinePullback (scalarMat n h) t w =
        (L ⟨affinePullback (scalarMat n h) t u, hVH h t u hu⟩ : FormField n) →
      √(formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior w) ≤
        C * h * √(formGradL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior u) := by
  obtain ⟨C, hC0, hC⟩ := exists_formL2Sq_le_formGradL2Sq hV hW L hL K.isCompact_closedInterior
    (interior_closedInterior_nonempty K)
  refine ⟨C, hC0, fun {h} hh t u hu w hw hLw => ?_⟩
  set v : V := ⟨affinePullback (scalarMat n h) t u, hVH h t u hu⟩
  have hdeg := isDeg_of_mem_polySpace (hV hu)
  have hhk : 0 < h ^ k := pow_pos hh k
  have hn : 0 ≤ h ^ n := pow_nonneg hh.le n
  have h1 : √(h ^ n) * √(formL2Sq K.closedInterior (L v)) =
      h ^ k * √(formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior w) := by
    rw [← hLw]
    exact sqrt_mul_sqrt_eq_of_mul_eq hn hhk.le (formL2Sq_affinePullback_scalarMat K hh t hw)
  have h2 : √(h ^ n) * √(formGradL2Sq K.closedInterior v) =
      h ^ (k + 1) * √(formGradL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior u) :=
    sqrt_mul_sqrt_eq_of_mul_eq hn (pow_nonneg hh.le _)
      (formGradL2Sq_affinePullback_scalarMat K hh t hdeg
        ((polySpace_le_c1 (hV hu)).differentiable (by simp)))
  refine le_of_mul_le_mul_left ?_ hhk
  calc h ^ k * √(formL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior w)
      = √(h ^ n) * √(formL2Sq K.closedInterior (L v)) := h1.symm
    _ ≤ √(h ^ n) * (C * √(formGradL2Sq K.closedInterior v)) :=
        mul_le_mul_of_nonneg_left (hC v) (Real.sqrt_nonneg _)
    _ = C * (√(h ^ n) * √(formGradL2Sq K.closedInterior v)) := by ring
    _ = h ^ k * (C * h * √(formGradL2Sq (mapEquiv (boxMap t h hh.ne') K).closedInterior u)) := by
        rw [h2]; ring

/-- The kernel lemma for `u - P u`, `P : V → V` linear and reproducing the constant fields of
`V`. -/
theorem exists_formL2Sq_sub_le_formGradL2Sq (hV : V ≤ polySpace n r k) (P : V →ₗ[ℝ] V)
    (hP : ∀ v : V, (∀ x, (v : FormField n) x = (v : FormField n) 0) → P v = v)
    {S : Set (Fin n → ℝ)} (hS : IsCompact S) (hSi : (interior S).Nonempty) :
    ∃ C, 0 ≤ C ∧ ∀ v : V,
      √(formL2Sq S ((v : FormField n) - (P v : FormField n))) ≤ C * √(formGradL2Sq S v) := by
  obtain ⟨C, hC0, hC⟩ := exists_formL2Sq_le_formGradL2Sq hV hV (LinearMap.id - P)
    (fun v hv => by rw [LinearMap.sub_apply, LinearMap.id_apply, hP v hv, sub_self]) hS hSi
  exact ⟨C, hC0, fun v => by simpa using hC v⟩

end Kernel

end Feec.FiniteElement
