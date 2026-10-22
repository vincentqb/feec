module

public import Feec.HilbertComplex.Transport
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Reweighting a Hilbert complex: conjugation by bounded isomorphisms

For a Hilbert complex `H` and bounded isomorphisms `a i : W i ≃L[𝕜] W' i` (the **weights**),
the **conjugated complex** `H.conj a` has the differentials `d' i j = a j ∘ d i j ∘ (a i)⁻¹` on
`a i D(d i j)`. In applications `W' = W` and the weights are positive self-adjoint, e.g.
`a = ε^{1/2}` on the electric fields and `a = μ^{-1/2}` on the magnetic fluxes of a medium: the
standard inner product of the conjugated variables `a x` is then the weighted inner product
`⟪x, y⟫_G = ⟪G x, y⟫` with `G = a† a` (`⟪ε E, E⟫`, `⟪μ⁻¹ B, B⟫`), so the conjugated complex
realizes the weighted `L²` structure of a medium on the standard spaces.

Unlike `Feec.HilbertComplex.transport`, the weights need not be scaled isometries; the price is
that adjoints pick up the adjoint weights: `(d')† = (a i)⁻† ∘ d† ∘ (a j)†`.

## Main definitions

* `ContinuousLinearEquiv.adjoint a : F ≃L[𝕜] E`: the adjoint `a†` of `a : E ≃L[𝕜] F`, with
  inverse `(a⁻¹)†`.
* `LinearPMap.conj T a b = b ∘ T ∘ a⁻¹` for `T : E →ₗ.[𝕜] F`.
* `HilbertComplex.conj H a`: the conjugated (reweighted) complex.

## Main results

* `LinearPMap.adjoint_conj`: `(b T a⁻¹)† = (a⁻¹)† T† b†`.
* `HilbertComplex.ReducingSubcomplex.conj`: a reducing subcomplex `S` of `H` gives the reducing
  subcomplex `S'` of `H.conj a` whenever `a S ⊆ S'` and `a Sᗮ ⊆ S'ᗮ` (e.g. `S' = S` when the
  weights commute with the projections).
* `ShortHilbertComplex.conj`: the same for short complexes.
* `Evolution.isStrongSolution_conj_symm_iff`, `Evolution.isClassicalSolution_conj_symm_iff`,
  `Evolution.ForcingClass.admissible.conjEquiv`, `Evolution.existsUnique_conj_symm`: evolution
  equations `U' = Φ⁻¹ A Φ U + F` are similar to `V' = A V + Φ F`, and well-posedness transfers.
* `ContinuousLinearMap.exists_selfAdjoint_equiv_adjoint_comp_eq`: over `ℂ` every bounded,
  self-adjoint, uniformly positive `ε` is `e† e` for a self-adjoint isomorphism `e` (`e = ε^{1/2}`,
  the continuous functional calculus square root), so the weights of every medium exist.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.1 (Hilbert complexes; weighted inner products define equivalent complexes)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 4 (Hilbert complexes)
* [J. Brüning, M. Lesch, *Hilbert complexes*][BruningLesch1992] (Hilbert complexes of closed densely
  defined operators)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

/-! ### The adjoint of a continuous linear equivalence -/

namespace ContinuousLinearEquiv

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The **adjoint** `a† : F ≃L[𝕜] E` of a continuous linear equivalence `a : E ≃L[𝕜] F`; its
inverse is `(a⁻¹)†`. -/
def adjoint (a : E ≃L[𝕜] F) : F ≃L[𝕜] E :=
  ContinuousLinearEquiv.equivOfInverse (ContinuousLinearMap.adjoint (a : E →L[𝕜] F))
    (ContinuousLinearMap.adjoint (a.symm : F →L[𝕜] E))
    (fun y => by
      rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp,
        ContinuousLinearEquiv.coe_comp_coe_symm, ContinuousLinearMap.adjoint_id]; rfl)
    (fun x => by
      rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp,
        ContinuousLinearEquiv.coe_symm_comp_coe, ContinuousLinearMap.adjoint_id]; rfl)

theorem inner_adjoint_apply (a : E ≃L[𝕜] F) (y : F) (x : E) :
    ⟪a.adjoint y, x⟫_𝕜 = ⟪y, a x⟫_𝕜 :=
  ContinuousLinearMap.adjoint_inner_left _ _ _

theorem inner_adjoint_symm_apply (a : E ≃L[𝕜] F) (x : E) (y : F) :
    ⟪a.adjoint.symm x, y⟫_𝕜 = ⟪x, a.symm y⟫_𝕜 :=
  ContinuousLinearMap.adjoint_inner_left _ _ _

/-- `a†† = a`. -/
theorem adjoint_adjoint (a : E ≃L[𝕜] F) : a.adjoint.adjoint = a := by
  ext x
  change ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint (a : E →L[𝕜] F)) x = a x
  rw [ContinuousLinearMap.adjoint_adjoint]
  rfl

/-- `((a⁻¹)†)† = a⁻¹`. -/
theorem adjoint_symm_adjoint_apply (a : E ≃L[𝕜] F) (x : F) : a.adjoint.symm.adjoint x = a.symm x := by
  change ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint (a.symm : F →L[𝕜] E)) x = _
  rw [ContinuousLinearMap.adjoint_adjoint]
  rfl

@[simp] theorem adjoint_apply_adjoint_symm_apply (a : E ≃L[𝕜] F) (x : E) :
    a.adjoint (a.adjoint.symm x) = x :=
  a.adjoint.apply_symm_apply x

end ContinuousLinearEquiv

namespace Submodule

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The image of a subspace with an orthogonal projection under a continuous linear isomorphism
of Hilbert spaces has an orthogonal projection (it is closed). -/
instance hasOrthogonalProjection_map_continuousLinearEquiv [CompleteSpace F] (a : E ≃L[𝕜] F)
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
    (K.map (a : E →ₗ[𝕜] F)).HasOrthogonalProjection := by
  have hc : IsClosed ((K.map (a : E →ₗ[𝕜] F) : Submodule 𝕜 F) : Set F) := by
    rw [Submodule.map_coe]
    exact a.toHomeomorph.isClosed_image.2 K.isClosed_of_hasOrthogonalProjection
  have : CompleteSpace (K.map (a : E →ₗ[𝕜] F)) := hc.completeSpace_coe
  infer_instance

end Submodule

/-! ### Conjugation of a partial map -/

namespace LinearPMap

section Conj

variable {𝕜 E F E' F' : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- The **conjugate** `b ∘ T ∘ a⁻¹ : E' → F'` of `T : E → F` by isomorphisms `a : E ≃ E'`,
`b : F ≃ F'`, on the domain `a D(T)`. -/
def conj (T : E →ₗ.[𝕜] F) (a : E ≃L[𝕜] E') (b : F ≃L[𝕜] F') : E' →ₗ.[𝕜] F' where
  domain := T.domain.comap (a.symm : E' →ₗ[𝕜] E)
  toFun := (b : F →ₗ[𝕜] F').comp (T.toFun.comp
    (((a.symm : E' →ₗ[𝕜] E)).restrict (p := T.domain.comap (a.symm : E' →ₗ[𝕜] E))
      (q := T.domain) fun _ hy => hy))

variable {T : E →ₗ.[𝕜] F} {a : E ≃L[𝕜] E'} {b : F ≃L[𝕜] F'}

theorem mem_conj_domain {y : E'} : y ∈ (T.conj a b).domain ↔ a.symm y ∈ T.domain := Iff.rfl

theorem conj_apply (y : (T.conj a b).domain) :
    T.conj a b y = b (T ⟨a.symm y, show a.symm (y : E') ∈ T.domain from y.2⟩) := rfl

theorem apply_mem_conj_domain {x : E} : a x ∈ (T.conj a b).domain ↔ x ∈ T.domain := by
  rw [mem_conj_domain, ContinuousLinearEquiv.symm_apply_apply]

/-- `(b T a⁻¹) (a x) = b (T x)`. -/
theorem conj_apply_apply (x : T.domain) :
    T.conj a b ⟨a x, apply_mem_conj_domain.2 x.2⟩ = b (T x) := by
  rw [conj_apply]
  exact congrArg b (apply_congr' _ _ _ (a.symm_apply_apply _))

theorem mem_conj_graph_iff {p : E' × F'} :
    p ∈ (T.conj a b).graph ↔ (a.symm p.1, b.symm p.2) ∈ T.graph := by
  rw [mem_graph_iff, mem_graph_iff]
  constructor
  · rintro ⟨y, hy1, hy2⟩
    refine ⟨⟨_, y.2⟩, by simp [← hy1], ?_⟩
    rw [← hy2, conj_apply, ContinuousLinearEquiv.symm_apply_apply]
    rfl
  · rintro ⟨x, hx1, hx2⟩
    have hx1' : (x : E) = a.symm p.1 := hx1
    have hp : p.1 ∈ (T.conj a b).domain := show a.symm p.1 ∈ _ from hx1' ▸ x.2
    refine ⟨⟨p.1, hp⟩, rfl, ?_⟩
    rw [conj_apply, ← (b.apply_symm_apply p.2), ← show T x = b.symm p.2 from hx2]
    exact congrArg b (apply_congr' _ _ _ hx1'.symm)

/-- The conjugate of a closed operator is closed. -/
theorem isClosed_conj (hT : T.IsClosed) : (T.conj a b).IsClosed := by
  have hg : ((T.conj a b).graph : Set (E' × F')) =
      (fun p : E' × F' => (a.symm p.1, b.symm p.2)) ⁻¹' (T.graph : Set (E × F)) := by
    ext p; exact mem_conj_graph_iff
  unfold LinearPMap.IsClosed
  rw [hg]
  exact hT.preimage ((a.symm.continuous.comp continuous_fst).prodMk
    (b.symm.continuous.comp continuous_snd))

/-- The conjugate of a densely defined operator is densely defined. -/
theorem dense_conj_domain (hT : Dense (T.domain : Set E)) :
    Dense ((T.conj a b).domain : Set E') :=
  hT.preimage a.symm.toHomeomorph.isOpenMap

theorem conj_eq_zero (hT : T = 0) : T.conj a b = 0 := by
  refine LinearPMap.ext ?_ fun x y _ => ?_
  · ext y
    change a.symm y ∈ T.domain ↔ y ∈ (⊤ : Submodule 𝕜 E')
    rw [hT]; exact ⟨fun _ => Submodule.mem_top, fun _ => Submodule.mem_top⟩
  · rw [conj_apply, apply_eq_zero_of_eq_zero hT, _root_.map_zero, apply_eq_zero_of_eq_zero rfl]

/-- Conjugating back by the inverses recovers `T`. -/
theorem conj_symm_conj : (T.conj a b).conj a.symm b.symm = T := by
  refine LinearPMap.ext ?_ fun x y hxy => ?_
  · ext x
    change a.symm.symm x ∈ (T.conj a b).domain ↔ _
    rw [ContinuousLinearEquiv.symm_symm, apply_mem_conj_domain]
  · rw [conj_apply, conj_apply, ContinuousLinearEquiv.symm_apply_apply]
    exact apply_congr' _ _ _ (by simp)

end Conj

section Adjoint

variable {𝕜 E F E' F' : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [CompleteSpace F']
  {T : E →ₗ.[𝕜] F} (a : E ≃L[𝕜] E') (b : F ≃L[𝕜] F')

/-- **The adjoint of a conjugate**: `(b T a⁻¹)† = (a⁻¹)† T† b†`. -/
theorem adjoint_conj (hT : Dense (T.domain : Set E)) :
    (T.conj a b)† = T†.conj b.adjoint.symm a.adjoint.symm := by
  have hd := dense_conj_domain (a := a) (b := b) hT
  have hle : T†.conj b.adjoint.symm a.adjoint.symm ≤ (T.conj a b)† := by
    refine IsFormalAdjoint.le_adjoint hd fun x y => ?_
    have h := adjoint_isFormalAdjoint hT ⟨b.adjoint.symm.symm y, y.2⟩ ⟨a.symm x, x.2⟩
    rw [conj_apply, conj_apply]
    conv_rhs => rw [← inner_conj_symm, ContinuousLinearEquiv.inner_adjoint_symm_apply]
    rw [h]
    simp only [ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.inner_adjoint_apply,
      inner_conj_symm]
  refine (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun y hy => ?_)).symm
  change b.adjoint.symm.symm y ∈ T†.domain
  rw [ContinuousLinearEquiv.symm_symm]
  set z := (T.conj a b)† ⟨y, hy⟩
  refine mem_adjoint_domain_of_exists _ ⟨a.adjoint z, fun x => ?_⟩
  have h := adjoint_isFormalAdjoint hd ⟨y, hy⟩ ⟨a x, apply_mem_conj_domain.2 x.2⟩
  rw [conj_apply_apply] at h
  rw [ContinuousLinearEquiv.inner_adjoint_apply, ContinuousLinearEquiv.inner_adjoint_apply]
  exact h

end Adjoint

end LinearPMap

/-! ### The conjugated complex -/

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W W' : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace 𝕜 (W' i)]
  [∀ i, CompleteSpace (W' i)]
  (H : HilbertComplex 𝕜 c W) (a : ∀ i, W i ≃L[𝕜] W' i)

/-- The **conjugated** (reweighted) complex `d' i j = a j ∘ d i j ∘ (a i)⁻¹`, on `a i D(d i j)`.
For positive self-adjoint weights this is the complex of the weighted inner products
`⟪(a i)† a i x, y⟫`. -/
def conj : HilbertComplex 𝕜 c W' where
  d i j := (H.d i j).conj (a i) (a j)
  shape i j h := conj_eq_zero (H.shape i j h)
  dense i j := dense_conj_domain (H.dense i j)
  closed i j := isClosed_conj (H.closed i j)
  mapsTo i j k y := by
    rw [conj_apply]
    exact apply_mem_conj_domain.2 (H.mapsTo i j k _)
  d_comp_d i j k y := by
    have h := H.d_comp_d i j k ⟨_, show (a i).symm (y : W' i) ∈ (H.d i j).domain from y.2⟩
    rw [conj_apply]
    rw [← (a k).map_zero, ← h]
    exact congrArg (a k) (apply_congr' _ _ _ (by
      change (a j).symm ((H.d i j).conj (a i) (a j) y) = _
      rw [conj_apply, ContinuousLinearEquiv.symm_apply_apply]))

/-- Conjugating back by the inverse weights recovers `H`. -/
theorem conj_symm_conj : (H.conj a).conj (fun i => (a i).symm) = H :=
  ext_d (funext fun _ => funext fun _ => LinearPMap.conj_symm_conj)

/-! ### Reducing subcomplexes and invariant cores of the conjugated complex -/

variable {H a}

omit [∀ i, CompleteSpace (W i)] [∀ i, CompleteSpace (W' i)] in
/-- If `a K ⊆ K'` and `a Kᗮ ⊆ K'ᗮ`, then `P_{K'} a = a P_K`. -/
theorem starProjection_apply_of_map_le {i : ι} {K : Submodule 𝕜 (W i)}
    {K' : Submodule 𝕜 (W' i)} [K.HasOrthogonalProjection] [K'.HasOrthogonalProjection]
    (h : K.map (a i : W i →ₗ[𝕜] W' i) ≤ K')
    (ho : Kᗮ.map (a i : W i →ₗ[𝕜] W' i) ≤ K'ᗮ) (x : W i) :
    K'.starProjection (a i x) = a i (K.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_orthogonal
    (h (Submodule.mem_map_of_mem (K.starProjection_apply_mem x))) ?_
  rw [← _root_.map_sub]
  exact ho (Submodule.mem_map_of_mem (K.sub_starProjection_mem_orthogonal x))

namespace ReducingSubcomplex

variable {S : ∀ i, Submodule 𝕜 (W i)} [∀ i, (S i).HasOrthogonalProjection]
  {S' : ∀ i, Submodule 𝕜 (W' i)} [∀ i, (S' i).HasOrthogonalProjection]

/-- **Reducing subcomplexes transport to the conjugated complex**: if `S` is a reducing
subcomplex of `H` and the weights map `S i` into `S' i` and `(S i)ᗮ` into `(S' i)ᗮ`, then `S'`
is a reducing subcomplex of `H.conj a`.

Since `a i` is bijective and `W i = S i ⊕ (S i)ᗮ`, the hypotheses force `a i (S i) = S' i` and
`a i (S i)ᗮ = (S' i)ᗮ`: the weights must carry the orthogonal splitting to an orthogonal
splitting (e.g. unitary weights, or weights commuting with the projections). For general weights
`a i S i` is only invariant along the oblique splitting `a i S i ⊕ a i (S i)ᗮ`; the weighted Gauss
laws of a medium (`Maxwell.Medium.gauss`) are therefore obtained from the `divFreeSub` of the
conjugated complex itself rather than from this lemma. -/
theorem conj (h : H.ReducingSubcomplex S) (hS : ∀ i, (S i).map (a i : W i →ₗ[𝕜] W' i) ≤ S' i)
    (hSo : ∀ i, (S i)ᗮ.map (a i : W i →ₗ[𝕜] W' i) ≤ (S' i)ᗮ) :
    (H.conj a).ReducingSubcomplex S' := by
  have hP : ∀ i (y : W' i), (a i).symm ((S' i).starProjection y) =
      (S i).starProjection ((a i).symm y) := fun i y => by
    conv_lhs => rw [← (a i).apply_symm_apply y, starProjection_apply_of_map_le (hS i) (hSo i)]
    exact (a i).symm_apply_apply _
  refine ⟨fun i j => ⟨fun y => ?_, fun y => ?_⟩⟩
  · change (a i).symm ((S' i).starProjection (y : W' i)) ∈ (H.d i j).domain
    rw [hP]
    exact (h.reduces i j).proj_mem ⟨_, y.2⟩
  · change (a j) ((H.d i j) ⟨(a i).symm ((S' i).starProjection (y : W' i)), _⟩) =
      (S' j).starProjection ((a j) ((H.d i j) ⟨(a i).symm y, y.2⟩))
    rw [starProjection_apply_of_map_le (hS j) (hSo j),
      ← (h.reduces i j).comm ⟨(a i).symm (y : W' i), y.2⟩]
    exact congrArg (a j) (apply_congr' _ _ _ (hP i y))

variable [Fintype ι] [∀ i, NormedSpace ℝ (W' i)] [∀ i, IsScalarTower ℝ 𝕜 (W' i)]

end ReducingSubcomplex

end Feec.HilbertComplex

/-! ### Weights of a medium: square roots of uniformly positive operators -/

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- `⟪e† e x, y⟫ = ⟪e x, e y⟫`: the weighted inner product of `G = e† e`. -/
theorem inner_adjoint_comp_self_apply (e : E →L[𝕜] E) (x y : E) :
    ⟪(ContinuousLinearMap.adjoint e ∘L e) x, y⟫_𝕜 = ⟪e x, e y⟫_𝕜 := by
  rw [comp_apply, adjoint_inner_left]

/-- `re ⟪e† e x, x⟫ = ‖e x‖²`. -/
theorem re_inner_adjoint_comp_self_apply (e : E →L[𝕜] E) (x : E) :
    RCLike.re ⟪(ContinuousLinearMap.adjoint e ∘L e) x, x⟫_𝕜 = ‖e x‖ ^ 2 := by
  rw [inner_adjoint_comp_self_apply, inner_self_eq_norm_sq]

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Every medium has weights** (over `ℂ`): a bounded, self-adjoint, uniformly positive `ε`
(`c ‖x‖² ≤ re ⟪ε x, x⟫`, `c > 0`; e.g. multiplication by a measurable matrix field with
`λ ≤ ε(x) ≤ Λ`) is `e† e = e e` for the self-adjoint isomorphism `e = ε^{1/2}` (the continuous
functional calculus square root `CFC.sqrt ε`). -/
theorem exists_selfAdjoint_equiv_adjoint_comp_eq {ε : E →L[ℂ] E} (hε : IsSelfAdjoint ε)
    {c : ℝ} (hc : 0 < c) (hcε : ∀ x, c * ‖x‖ ^ 2 ≤ RCLike.re ⟪ε x, x⟫_ℂ) :
    ∃ e : E ≃L[ℂ] E, IsSelfAdjoint (e : E →L[ℂ] E) ∧
      ContinuousLinearMap.adjoint (e : E →L[ℂ] E) ∘L (e : E →L[ℂ] E) = ε := by
  have hpos : ε.IsPositive :=
    ⟨hε.isSymmetric, fun x => (by positivity : (0 : ℝ) ≤ c * ‖x‖ ^ 2).trans (hcε x)⟩
  have h0 : 0 ≤ ε := ContinuousLinearMap.nonneg_iff_isPositive.2 hpos
  set s := CFC.sqrt ε
  have hs : IsSelfAdjoint s := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg ε)
  have hss : s * s = ε := CFC.sqrt_mul_sqrt_self ε
  have hsadj : ContinuousLinearMap.adjoint s = s := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hs.star_eq
  have hcomp : ContinuousLinearMap.adjoint s ∘L s = ε := by rw [hsadj]; exact hss
  -- `s` is bounded below: `c ‖x‖² ≤ ‖s x‖²`
  have hbelow : ∀ x, c * ‖x‖ ^ 2 ≤ ‖s x‖ ^ 2 := fun x => by
    rw [← re_inner_adjoint_comp_self_apply, hcomp]; exact hcε x
  have hinj : Function.Injective s := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have := hbelow x
    rw [hx, norm_zero] at this
    have h2 : ‖x‖ ^ 2 ≤ 0 := by nlinarith
    exact norm_eq_zero.1 (by nlinarith [norm_nonneg x])
  have hclosed : IsClosed (LinearMap.range (s : E →ₗ[ℂ] E) : Set E) := by
    have hanti : AntilipschitzWith (⟨(Real.sqrt c)⁻¹, by positivity⟩) s := by
      refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
      rw [dist_eq_norm, dist_eq_norm, ← _root_.map_sub]
      have h := hbelow (x - y)
      have hsq : Real.sqrt c * ‖x - y‖ ≤ ‖s (x - y)‖ := by
        rw [← Real.sqrt_sq (norm_nonneg (s (x - y))), ← Real.sqrt_sq (norm_nonneg (x - y)),
          ← Real.sqrt_mul hc.le]
        exact Real.sqrt_le_sqrt h
      change ‖x - y‖ ≤ (Real.sqrt c)⁻¹ * ‖s (x - y)‖
      rw [le_inv_mul_iff₀ (Real.sqrt_pos.2 hc)]
      exact hsq
    exact hanti.isClosed_range s.uniformContinuous
  have hdense : (LinearMap.range (s : E →ₗ[ℂ] E))ᗮ = ⊥ := by
    have := ContinuousLinearMap.orthogonal_range s
    rw [hsadj] at this
    exact this.trans (LinearMap.ker_eq_bot.2 hinj)
  have hsurj : Function.Surjective s := by
    have hK : (LinearMap.range (s : E →ₗ[ℂ] E)) = ⊤ := by
      have : CompleteSpace (LinearMap.range (s : E →ₗ[ℂ] E)) := hclosed.completeSpace_coe
      rw [← Submodule.orthogonal_orthogonal (LinearMap.range (s : E →ₗ[ℂ] E)), hdense,
        Submodule.bot_orthogonal_eq_top]
    exact LinearMap.range_eq_top.1 hK
  refine ⟨ContinuousLinearEquiv.ofBijective s (LinearMap.ker_eq_bot.2 hinj)
    (LinearMap.range_eq_top.2 hsurj), ?_, ?_⟩
  · exact hs
  · exact hcomp

end ContinuousLinearMap

/-! ### Short complexes -/

namespace Feec.ShortHilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {W₀ W₁ W₂ W₀' W₁' W₂' : Type*}
  [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [CompleteSpace W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [CompleteSpace W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace 𝕜 W₂] [CompleteSpace W₂]
  [NormedAddCommGroup W₀'] [InnerProductSpace 𝕜 W₀'] [CompleteSpace W₀']
  [NormedAddCommGroup W₁'] [InnerProductSpace 𝕜 W₁'] [CompleteSpace W₁']
  [NormedAddCommGroup W₂'] [InnerProductSpace 𝕜 W₂'] [CompleteSpace W₂']
  (S : ShortHilbertComplex 𝕜 W₀ W₁ W₂)

/-- The conjugated short complex `a₁ d₀ a₀⁻¹ : W₀' → W₁'`, `a₂ d₁ a₁⁻¹ : W₁' → W₂'`. -/
def conj (a₀ : W₀ ≃L[𝕜] W₀') (a₁ : W₁ ≃L[𝕜] W₁') (a₂ : W₂ ≃L[𝕜] W₂') :
    ShortHilbertComplex 𝕜 W₀' W₁' W₂' where
  d₀ := S.d₀.conj a₀ a₁
  d₁ := S.d₁.conj a₁ a₂
  dense₀ := dense_conj_domain S.dense₀
  dense₁ := dense_conj_domain S.dense₁
  closed₀ := isClosed_conj S.closed₀
  closed₁ := isClosed_conj S.closed₁
  mapsTo x := by
    rw [conj_apply]
    exact apply_mem_conj_domain.2 (S.mapsTo _)
  comp x := by
    have h := S.comp ⟨_, show a₀.symm (x : W₀') ∈ S.d₀.domain from x.2⟩
    rw [conj_apply, ← a₂.map_zero, ← h]
    exact congrArg a₂ (apply_congr' _ _ _ (by
      change a₁.symm (S.d₀.conj a₀ a₁ x) = _
      rw [conj_apply, ContinuousLinearEquiv.symm_apply_apply]))

@[simp] theorem conj_d₀ (a₀ : W₀ ≃L[𝕜] W₀') (a₁ : W₁ ≃L[𝕜] W₁') (a₂ : W₂ ≃L[𝕜] W₂') :
    (S.conj a₀ a₁ a₂).d₀ = S.d₀.conj a₀ a₁ := rfl

end Feec.ShortHilbertComplex

/-! ### Similar evolution equations -/

namespace Feec.Evolution

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  [IsScalarTower ℝ 𝕜 E] {A : E →ₗ.[𝕜] E} (Φ : E ≃L[𝕜] E) {I : Set ℝ} {F U : ℝ → E}

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem mem_graph_conj_self_iff {x v : E} :
    (Φ x, Φ v) ∈ (A.conj Φ Φ).graph ↔ (x, v) ∈ A.graph := by
  rw [mem_conj_graph_iff]; simp

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- `(A.conj Φ⁻¹ Φ⁻¹).conj Φ Φ = A`. -/
theorem conj_conj_symm : (A.conj Φ.symm Φ.symm).conj Φ Φ = A := by
  simpa using LinearPMap.conj_symm_conj (T := A) (a := Φ.symm) (b := Φ.symm)

/-- **Similarity of evolution equations**: if `U` solves `U' = A U + F`, then `Φ U` solves
`V' = (Φ A Φ⁻¹) V + Φ F`. -/
theorem IsStrongSolution.conjEquiv (hU : IsStrongSolution A I F U) :
    IsStrongSolution (A.conj Φ Φ) I (fun t => Φ (F t)) (fun t => Φ (U t)) := by
  refine ⟨(Φ : E →L[𝕜] E).continuous.comp_continuousOn hU.continuousOn, fun t ht => ?_⟩
  obtain ⟨v, hv, hd⟩ := hU.deriv t ht
  refine ⟨Φ v, (mem_graph_conj_self_iff Φ).2 hv, ?_⟩
  have := (Φ : E →L[𝕜] E).hasDerivWithinAt_apply_of_hasDerivWithinAt hd
  rw [_root_.map_add] at this
  exact this

theorem IsClassicalSolution.conjEquiv (hU : IsClassicalSolution A I F U) :
    IsClassicalSolution (A.conj Φ Φ) I (fun t => Φ (F t)) (fun t => Φ (U t)) := by
  obtain ⟨V, hVc, hV⟩ := hU.deriv_cont
  exact ⟨hU.toIsStrongSolution.conjEquiv Φ, ⟨fun t => Φ (V t),
    (Φ : E →L[𝕜] E).continuous.comp_continuousOn hVc,
    fun t ht => (mem_graph_conj_self_iff Φ).2 (hV t ht)⟩⟩

/-- Strong solutions of `U' = Φ⁻¹ A Φ U + F` are the `Φ⁻¹`-images of the strong solutions of
`V' = A V + Φ F`. -/
theorem isStrongSolution_conj_symm_iff :
    IsStrongSolution (A.conj Φ.symm Φ.symm) I F U ↔
      IsStrongSolution A I (fun t => Φ (F t)) (fun t => Φ (U t)) := by
  constructor
  · intro h
    have := h.conjEquiv Φ
    rwa [conj_conj_symm] at this
  · intro h
    simpa using h.conjEquiv Φ.symm

theorem isClassicalSolution_conj_symm_iff :
    IsClassicalSolution (A.conj Φ.symm Φ.symm) I F U ↔
      IsClassicalSolution A I (fun t => Φ (F t)) (fun t => Φ (U t)) := by
  constructor
  · intro h
    have := h.conjEquiv Φ
    rwa [conj_conj_symm] at this
  · intro h
    simpa using h.conjEquiv Φ.symm

omit [IsScalarTower ℝ 𝕜 E] in
/-- Admissible forcing is carried along a similarity. -/
theorem ForcingClass.admissible.conjEquiv [CompleteSpace E] {a b : ℝ}
    (hF : ForcingClass.admissible A a b F) :
    ForcingClass.admissible (A.conj Φ Φ) a b (fun t => Φ (F t)) := by
  obtain ⟨hc, hw | hl⟩ := hF
  · refine ⟨(Φ : E →L[𝕜] E).continuous.comp_continuousOn hc, Or.inl ?_⟩
    obtain ⟨x₀, g, hg, hFg⟩ := hw
    refine ⟨Φ x₀, fun s => Φ (g s), (Φ : E →L[𝕜] E).integrable_comp hg, ?_⟩
    filter_upwards [hFg, MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t h ht
    have hgi : IntervalIntegrable g MeasureTheory.volume a t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1.le).2
        (hg.mono_set (Ioc_subset_Ioc_right ht.2.le))
    change Φ (F t) = Φ x₀ + ∫ s in a..t, (Φ : E →L[𝕜] E) (g s)
    rw [h, (Φ : E →L[𝕜] E).intervalIntegral_comp_comm hgi, _root_.map_add]
    rfl
  · refine ⟨(Φ : E →L[𝕜] E).continuous.comp_continuousOn hc, Or.inr ?_⟩
    obtain ⟨H, hH, hFH⟩ := hl
    refine ⟨fun s => Φ (H s), (Φ : E →L[𝕜] E).integrable_comp hH, ?_⟩
    filter_upwards [hFH] with t ⟨h, hA⟩
    exact ⟨apply_mem_conj_domain.2 h, by rw [conj_apply_apply ⟨F t, h⟩, hA]⟩

omit [IsScalarTower ℝ 𝕜 E] in
theorem ForcingClass.admissible.conjEquiv_symm [CompleteSpace E] {a b : ℝ}
    (hF : ForcingClass.admissible (A.conj Φ.symm Φ.symm) a b F) :
    ForcingClass.admissible A a b (fun t => Φ (F t)) := by
  have := hF.conjEquiv Φ
  rwa [conj_conj_symm] at this

/-- **Well-posedness is invariant under similarity**: if `U' = A U + F` has a classical solution
for every `U₀ ∈ D(A)` and admissible `F`, unique among strong solutions, then so has
`U' = Φ⁻¹ A Φ U + F`. -/
theorem existsUnique_conj_symm [CompleteSpace E] {a b : ℝ}
    (h : ∀ U₀ ∈ A.domain, ∀ F, ForcingClass.admissible A a b F →
      ∃ U, U a = U₀ ∧ IsClassicalSolution A (Icc a b) F U ∧
        ∀ V, V a = U₀ → IsStrongSolution A (Icc a b) F V → EqOn V U (Icc a b))
    {U₀ : E} (hU₀ : U₀ ∈ (A.conj Φ.symm Φ.symm).domain)
    (hF : ForcingClass.admissible (A.conj Φ.symm Φ.symm) a b F) :
    ∃ U, U a = U₀ ∧ IsClassicalSolution (A.conj Φ.symm Φ.symm) (Icc a b) F U ∧
      ∀ V, V a = U₀ → IsStrongSolution (A.conj Φ.symm Φ.symm) (Icc a b) F V →
        EqOn V U (Icc a b) := by
  have hU₀' : Φ U₀ ∈ A.domain := by simpa [mem_conj_domain] using hU₀
  obtain ⟨U, hU0, hU, huniq⟩ := h (Φ U₀) hU₀' _ (hF.conjEquiv_symm Φ)
  refine ⟨fun t => Φ.symm (U t), by simp [hU0], ?_, fun V hV0 hV => fun t ht => ?_⟩
  · rw [isClassicalSolution_conj_symm_iff]
    simpa using hU
  · have := huniq (fun t => Φ (V t)) (by simp [hV0]) ((isStrongSolution_conj_symm_iff Φ).1 hV) ht
    simp only at this
    simp [← this]

end Feec.Evolution
