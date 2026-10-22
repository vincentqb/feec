module

public import Feec.FiniteElement.BrambleHilbert
public import Feec.Mesh.ShapeRegular
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Interpolation error on shape-regular simplicial meshes

Every `n`-simplex `T` of `ℝⁿ` is `T = F_T(T̂)` with `F_T xh = B_T xh + p₀`
(`Affine.Simplex.refMap`, `Affine.Simplex.linearEquiv`; `Feec.Mesh`). A reference interpolant
`I` (`Feec.FiniteElement.IsRefInterpolant`) is transported to `T` through `F_T` and a fibre
isomorphism `Φ_T : G ≃L[ℝ] G`: the identity for scalar functions, the pullback
`ω ↦ ω ∘ (B_T, …, B_T)` for alternating `k`-forms, and for vector proxies
the corresponding Piola map (covariant `û = B_Tᵀ u ∘ F_T` for `1`-forms, contravariant
`û = det B_T · B_T⁻¹ u ∘ F_T` for `(n-1)`-forms), not the identity. All of these satisfy
`‖Φ_T‖ ≤ A ‖B_T‖^k`, `‖Φ_T⁻¹‖ ≤ A ‖B_T⁻¹‖^k` with `A` depending only on `n` and `k`:
`û = Φ_T ∘ u ∘ F_T` (`refPullback`) and `Π_T u = Φ_T⁻¹ ∘ (I û) ∘ F_T⁻¹` (`transportInterp`).

The chain rule `D^j (u ∘ F_T)(xh) = D^j u(F_T xh) ∘ (B_T, …, B_T)` (`iteratedFDeriv_comp_refMap`)
gives `‖D^j û‖ ≤ ‖Φ_T‖ ‖B_T‖^j ‖D^j u ∘ F_T‖`, and the reference estimate
(`IsRefInterpolant.norm_sub_le`) transports to
`sup_T ‖u - Π_T u‖ ≤ ‖Φ_T⁻¹‖ ‖Φ_T‖ (1 + C (m + 1)) ‖B_T‖^{r+1} sup_T ‖D^{r+1} u‖`
(`norm_sub_transportInterp_le`) ([Ciarlet2002], Thm 3.1.4; [Arnold2018], Ch. 7).
For a shape-regular family (`Feec.Mesh.IsShapeRegular`: `‖B_T‖ ≤ C₀ h_T`, `‖B_T⁻¹‖ ≤ C₀ / h_T`)
this is
`sup_T ‖u - Π_T u‖ ≤ A² C₀^{2k} (1 + C (m + 1)) (C₀ h_T)^{r+1} sup_T ‖D^{r+1} u‖`
(`norm_sub_transportInterp_le_of_isShapeRegular`; [Ciarlet2002], Thm 3.1.5). With the chain rule for
`F_T⁻¹` (`iteratedFDeriv_comp_refMapInv`), a reference estimate of order `j`
(`HasRefDerivEstimate`) gives the derivative estimates
`sup_T ‖D^j (u - Π_T u)‖ ≤ A² C₀^{2k} K C₀^{2j} (C₀ h_T)^{r+1-j} sup_T ‖D^{r+1} u‖`, `j ≤ r + 1`
(`norm_iteratedFDeriv_sub_transportInterp_le_of_isShapeRegular`).

On a mesh, a piecewise interpolant `Π_h u` is only required to equal `Π_T u` on the *interior*
of each simplex, which is all that tangentially conforming (Whitney) or discontinuous
interpolants satisfy; the simplex frontiers are null (`Convex.addHaar_frontier`), so almost
every point of `closure Ω` lies in the interior of a simplex
(`Feec.FiniteElement.ae_mem_interior`, in `Feec.FiniteElement.Conformity`).

The change of variables `∫_T g = |det B_T| ∫_{T̂} g ∘ F_T` is `lintegral_closedInterior_eq`
(and `volume_closedInterior_eq`: `|T| = |det B_T| |T̂|`). The sharper transport of Sobolev
seminorms (`|v̂|_{m,p,T̂} ≤ C ‖B_T‖^m |det B_T|^{-1/p} |v|_{m,p,T}`) is not attempted, since
this classical form has no Sobolev spaces. Constructing a conforming `Π_h` and instantiating `I`
for Whitney forms are not done here: the hypotheses on the reference interpolant are stated
explicitly in `IsRefInterpolant` and `HasRefDerivEstimate`. As in
`Feec.FiniteElement.BrambleHilbert`, the value space `G` is in `Type`.

## Main definitions

* `Feec.FiniteElement.refMapInv T`: `F_T⁻¹`.
* `Feec.FiniteElement.refPullback T Φ u`: `û = Φ ∘ u ∘ F_T`.
* `Feec.FiniteElement.transportInterp T Φ I u`: `Π_T u = Φ⁻¹ ∘ I û ∘ F_T⁻¹`.

## Main results

* `iteratedFDeriv_comp_affine`, `iteratedFDeriv_comp_refMap`, `iteratedFDeriv_comp_refMapInv`,
  `norm_iteratedFDeriv_refPullback_le`: chain rules and scaling.
* `lintegral_closedInterior_eq`, `volume_closedInterior_eq`: change of variables.
* `norm_sub_transportInterp_le`, `norm_sub_transportInterp_le_of_isShapeRegular`: local
  estimates.
* `norm_iteratedFDeriv_sub_transportInterp_le`,
  `norm_iteratedFDeriv_sub_transportInterp_le_of_isShapeRegular`: local derivative estimates.

## References

* [P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*][Ciarlet2002], Thm 3.1.4
  (interpolation error for affine-equivalent families), Thm 3.1.5 (regular families)
* [J. H. Bramble, S. R. Hilbert, *Estimation of Linear Functionals on Sobolev Spaces with Application to Fourier Transforms and Spline Interpolation*][BrambleHilbert1970]
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (approximation
  estimates on shape regular meshes)

Bibliography: [references.bib](../../docs/references.bib)
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory Feec.Mesh

namespace Feec.FiniteElement

variable {n : ℕ} {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! ### The affine map `F_T` and its inverse -/

/-- `F_T⁻¹ x = B_T⁻¹ (x - p₀)`. -/
def refMapInv (T : Affine.Simplex ℝ (Fin n → ℝ) n) (x : Fin n → ℝ) : Fin n → ℝ :=
  T.linearEquiv.symm (x - T.points 0)

@[simp] theorem refMapInv_refMap (T : Affine.Simplex ℝ (Fin n → ℝ) n) (x : Fin n → ℝ) :
    refMapInv T (T.refMap x) = x := by
  rw [refMapInv, Affine.Simplex.refMap_apply, add_sub_cancel_right,
    ← Affine.Simplex.linearEquiv_apply, ContinuousLinearEquiv.symm_apply_apply]

@[simp] theorem refMap_refMapInv (T : Affine.Simplex ℝ (Fin n → ℝ) n) (x : Fin n → ℝ) :
    T.refMap (refMapInv T x) = x := by
  rw [refMapInv, Affine.Simplex.refMap_apply, ← Affine.Simplex.linearEquiv_apply,
    ContinuousLinearEquiv.apply_symm_apply, sub_add_cancel]

theorem contDiff_refMap (T : Affine.Simplex ℝ (Fin n → ℝ) n) {N : WithTop ℕ∞} :
    ContDiff ℝ N T.refMap := by
  have : (T.refMap : (Fin n → ℝ) → Fin n → ℝ) = fun x => T.linearEquiv x + T.points 0 := rfl
  rw [this]
  exact T.linearEquiv.contDiff.add contDiff_const

theorem hasFDerivAt_refMap (T : Affine.Simplex ℝ (Fin n → ℝ) n) (x : Fin n → ℝ) :
    HasFDerivAt T.refMap (T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ) x :=
  (T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ).hasFDerivAt.add_const (T.points 0)

/-! ### Chain rule and change of variables -/

/-- **Chain rule** for an affine isomorphism `y ↦ L y + c`:
`D^j (u ∘ (L · + c))(x) = D^j u(L x + c) ∘ (L, …, L)`. No smoothness is needed. -/
theorem iteratedFDeriv_comp_affine (L : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) (c : Fin n → ℝ)
    (u : (Fin n → ℝ) → G) (j : ℕ) (x : Fin n → ℝ) :
    iteratedFDeriv ℝ j (fun y => u (L y + c)) x =
      (iteratedFDeriv ℝ j u (L x + c)).compContinuousLinearMap
        fun _ => (L : (Fin n → ℝ) →L[ℝ] Fin n → ℝ) := by
  have hcomp : (fun y => u (L y + c)) = (fun z => u (z + c)) ∘ L := rfl
  have h := L.iteratedFDerivWithin_comp_right (x := x) (fun z => u (z + c))
    uniqueDiffOn_univ (mem_univ _) j
  rw [preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ,
    iteratedFDeriv_comp_add_right'] at h
  rw [hcomp, h]

/-- **Chain rule** for `F_T`: `D^j (u ∘ F_T)(xh) = D^j u(F_T xh) ∘ (B_T, …, B_T)`. -/
theorem iteratedFDeriv_comp_refMap (T : Affine.Simplex ℝ (Fin n → ℝ) n) (u : (Fin n → ℝ) → G)
    (j : ℕ) (x : Fin n → ℝ) :
    iteratedFDeriv ℝ j (fun y => u (T.refMap y)) x =
      (iteratedFDeriv ℝ j u (T.refMap x)).compContinuousLinearMap
        fun _ => (T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ) :=
  iteratedFDeriv_comp_affine T.linearEquiv (T.points 0) u j x

theorem refMapInv_eq (T : Affine.Simplex ℝ (Fin n → ℝ) n) (x : Fin n → ℝ) :
    refMapInv T x = T.linearEquiv.symm x + -T.linearEquiv.symm (T.points 0) := by
  rw [refMapInv, map_sub, sub_eq_add_neg]

/-- **Chain rule** for `F_T⁻¹`: `D^j (g ∘ F_T⁻¹)(x) = D^j g(F_T⁻¹ x) ∘ (B_T⁻¹, …, B_T⁻¹)`. -/
theorem iteratedFDeriv_comp_refMapInv (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    (g : (Fin n → ℝ) → G) (j : ℕ) (x : Fin n → ℝ) :
    iteratedFDeriv ℝ j (fun y => g (refMapInv T y)) x =
      (iteratedFDeriv ℝ j g (refMapInv T x)).compContinuousLinearMap
        fun _ => (T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ) := by
  have : (fun y => g (refMapInv T y)) =
      fun y => g (T.linearEquiv.symm y + -T.linearEquiv.symm (T.points 0)) :=
    funext fun y => by rw [refMapInv_eq]
  rw [this, iteratedFDeriv_comp_affine, ← refMapInv_eq]

/-- The reference pullback `û = Φ ∘ u ∘ F_T`. -/
def refPullback (T : Affine.Simplex ℝ (Fin n → ℝ) n) (Φ : G ≃L[ℝ] G) (u : (Fin n → ℝ) → G) :
    (Fin n → ℝ) → G :=
  fun x => Φ (u (T.refMap x))

theorem iteratedFDeriv_refPullback (T : Affine.Simplex ℝ (Fin n → ℝ) n) (Φ : G ≃L[ℝ] G)
    (u : (Fin n → ℝ) → G) (j : ℕ) (x : Fin n → ℝ) :
    iteratedFDeriv ℝ j (refPullback T Φ u) x =
      (Φ : G →L[ℝ] G).compContinuousMultilinearMap
        ((iteratedFDeriv ℝ j u (T.refMap x)).compContinuousLinearMap
          fun _ => (T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)) := by
  have : refPullback T Φ u = Φ ∘ fun y => u (T.refMap y) := rfl
  rw [this, ContinuousLinearEquiv.iteratedFDeriv_comp_left, iteratedFDeriv_comp_refMap]

/-- **Scaling of derivatives**: `‖D^j û(xh)‖ ≤ ‖Φ‖ ‖B_T‖^j ‖D^j u(F_T xh)‖`. -/
theorem norm_iteratedFDeriv_refPullback_le (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    (Φ : G ≃L[ℝ] G) (u : (Fin n → ℝ) → G) (j : ℕ) (x : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ j (refPullback T Φ u) x‖ ≤
      ‖(Φ : G →L[ℝ] G)‖ * ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ j *
        ‖iteratedFDeriv ℝ j u (T.refMap x)‖ := by
  rw [iteratedFDeriv_refPullback]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  rw [mul_assoc]
  gcongr
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]

theorem contDiffOn_refPullback (T : Affine.Simplex ℝ (Fin n → ℝ) n) (Φ : G ≃L[ℝ] G)
    {u : (Fin n → ℝ) → G} {U : Set (Fin n → ℝ)} {N : WithTop ℕ∞} (hu : ContDiffOn ℝ N u U) :
    ContDiffOn ℝ N (refPullback T Φ u) (T.refMap ⁻¹' U) :=
  Φ.contDiff.comp_contDiffOn (hu.comp (contDiff_refMap T).contDiffOn fun _ hx => hx)

theorem mem_closedInterior_iff_refMapInv (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    {x : Fin n → ℝ} :
    x ∈ T.closedInterior ↔ refMapInv T x ∈ (refSimplex n).closedInterior := by
  rw [T.closedInterior_eq_image_refMap]
  constructor
  · rintro ⟨y, hy, rfl⟩; rwa [refMapInv_refMap]
  · intro h; exact ⟨_, h, refMap_refMapInv T x⟩

/-- **Change of variables** on a simplex: `∫_T g = |det B_T| ∫_{T̂} g ∘ F_T`. -/
theorem lintegral_closedInterior_eq (T : Affine.Simplex ℝ (Fin n → ℝ) n)
    (g : (Fin n → ℝ) → ENNReal) :
    ∫⁻ x in T.closedInterior, g x =
      ENNReal.ofReal |LinearMap.det T.linearPart| *
        ∫⁻ x in (refSimplex n).closedInterior, g (T.refMap x) := by
  rw [T.closedInterior_eq_image_refMap,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (measurableSet_closedInterior _)
      (fun x _ => (hasFDerivAt_refMap T x).hasFDerivWithinAt) (T.refMap_injective.injOn),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rfl

/-- `|T| = |det B_T| |T̂|`. -/
theorem volume_closedInterior_eq (T : Affine.Simplex ℝ (Fin n → ℝ) n) :
    volume T.closedInterior =
      ENNReal.ofReal |LinearMap.det T.linearPart| * volume (refSimplex n).closedInterior := by
  have h := lintegral_closedInterior_eq T fun _ => 1
  simpa only [lintegral_const, Measure.restrict_apply_univ, one_mul] using h

/-! ### The transported interpolant -/

/-- The interpolant transported from `T̂` to `T`: `Π_T u = Φ⁻¹ ∘ I (Φ ∘ u ∘ F_T) ∘ F_T⁻¹`. -/
def transportInterp (T : Affine.Simplex ℝ (Fin n → ℝ) n) (Φ : G ≃L[ℝ] G)
    (I : ((Fin n → ℝ) → G) → (Fin n → ℝ) → G) (u : (Fin n → ℝ) → G) : (Fin n → ℝ) → G :=
  fun x => Φ.symm (I (refPullback T Φ u) (refMapInv T x))

variable {r m : ℕ} {I : ((Fin n → ℝ) → G) → (Fin n → ℝ) → G} {C : ℝ}

/-- **Local interpolation error** ([Ciarlet2002], Thm 3.1.4, classical form): for `u` of class
`C^{r+1}` near `T`,
`sup_T ‖u - Π_T u‖ ≤ ‖Φ⁻¹‖ ‖Φ‖ (1 + C (m + 1)) ‖B_T‖^{r+1} sup_T ‖D^{r+1} u‖`. -/
theorem norm_sub_transportInterp_le (hI : IsRefInterpolant n r m G I C)
    (T : Affine.Simplex ℝ (Fin n → ℝ) n) (Φ : G ≃L[ℝ] G) {u : (Fin n → ℝ) → G}
    {U : Set (Fin n → ℝ)} {M : ℝ} (hU : IsOpen U) (hTU : T.closedInterior ⊆ U)
    (hu : ContDiffOn ℝ (r + 1) u U)
    (hM : ∀ y ∈ T.closedInterior, ‖iteratedFDeriv ℝ (r + 1) u y‖ ≤ M)
    {x : Fin n → ℝ} (hx : x ∈ T.closedInterior) :
    ‖u x - transportInterp T Φ I u x‖ ≤
      ‖(Φ.symm : G →L[ℝ] G)‖ * ((1 + C * (m + 1)) *
        (‖(Φ : G →L[ℝ] G)‖ * ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ (r + 1) *
          M)) := by
  set xh := refMapInv T x
  have hxh : xh ∈ (refSimplex n).closedInterior := (mem_closedInterior_iff_refMapInv T).1 hx
  have hmem : ∀ y ∈ (refSimplex n).closedInterior, T.refMap y ∈ T.closedInterior :=
    fun y hy => by rw [T.closedInterior_eq_image_refMap]; exact mem_image_of_mem _ hy
  have hTU' : (refSimplex n).closedInterior ⊆ T.refMap ⁻¹' U := fun y hy => hTU (hmem y hy)
  have hM' : ∀ y ∈ (refSimplex n).closedInterior,
      ‖iteratedFDeriv ℝ (r + 1) (refPullback T Φ u) y‖ ≤
        ‖(Φ : G →L[ℝ] G)‖ * ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ (r + 1) * M :=
    fun y hy => (norm_iteratedFDeriv_refPullback_le T Φ u _ y).trans (by
      gcongr
      exact hM _ (hmem y hy))
  have hest := hI.norm_sub_le (hU.preimage (contDiff_refMap T (N := 0)).continuous) hTU'
    (contDiffOn_refPullback T Φ hu) hM' hxh
  have hux : u x = Φ.symm (refPullback T Φ u xh) := by
    simp [refPullback, xh]
  rw [transportInterp, hux, ← map_sub]
  exact (ContinuousLinearMap.le_opNorm (Φ.symm : G →L[ℝ] G) _).trans (by gcongr)

/-- `(C₀ h)^k (C₀ / h)^k ≤ C₀^{2k}`. -/
theorem pow_mul_div_pow_le {C₀ h : ℝ} (hh : 0 ≤ h) (k : ℕ) :
    (C₀ * h) ^ k * (C₀ / h) ^ k ≤ C₀ ^ (2 * k) := by
  rw [← mul_pow, pow_mul]
  rcases hh.eq_or_lt with rfl | hh
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · simp [zero_pow hk.ne']; positivity
  · rw [show C₀ * h * (C₀ / h) = C₀ ^ 2 by field_simp]

/-- The fibre-map constant on a shape-regular family: `‖Φ_T⁻¹‖ ‖Φ_T‖ ≤ A² C₀^{2k}` if
`‖Φ_T‖ ≤ A ‖B_T‖^k` and `‖Φ_T⁻¹‖ ≤ A ‖B_T⁻¹‖^k`. -/
theorem norm_symm_mul_norm_le_of_isShapeRegular {S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)}
    {C₀ c : ℝ} (hS : IsShapeRegular S C₀ c) {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ S)
    (Φ : G ≃L[ℝ] G) {A : ℝ} {k : ℕ}
    (hΦ : ‖(Φ : G →L[ℝ] G)‖ ≤ A * ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ k)
    (hΦs : ‖(Φ.symm : G →L[ℝ] G)‖ ≤
      A * ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ k) :
    ‖(Φ.symm : G →L[ℝ] G)‖ * ‖(Φ : G →L[ℝ] G)‖ ≤ A ^ 2 * C₀ ^ (2 * k) := by
  obtain ⟨hB, hBs, -⟩ := hS T hT
  have hh := diam_nonneg T
  set nB := ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖
  set nBs := ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖
  calc ‖(Φ.symm : G →L[ℝ] G)‖ * ‖(Φ : G →L[ℝ] G)‖ ≤ (A * nBs ^ k) * (A * nB ^ k) :=
        mul_le_mul hΦs hΦ (norm_nonneg _) ((norm_nonneg _).trans hΦs)
    _ = A ^ 2 * (nB ^ k * nBs ^ k) := by ring
    _ ≤ A ^ 2 * ((C₀ * diam T) ^ k * (C₀ / diam T) ^ k) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hB k)
          (pow_le_pow_left₀ (norm_nonneg _) hBs k) (by positivity)
          (pow_nonneg ((norm_nonneg _).trans hB) k)) (sq_nonneg A)
    _ ≤ A ^ 2 * C₀ ^ (2 * k) := by gcongr; exact pow_mul_div_pow_le hh k

/-- The geometric constant of the derivative estimates on a shape-regular family:
`‖B_T⁻¹‖^j ‖B_T‖^{r+1} ≤ C₀^{2j} (C₀ h_T)^{r+1-j}` for `j ≤ r + 1`. -/
theorem norm_symm_pow_mul_norm_pow_le_of_isShapeRegular
    {S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)} {C₀ c : ℝ} (hS : IsShapeRegular S C₀ c)
    {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ S) {j r : ℕ} (hj : j ≤ r + 1) :
    ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ j *
        ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ (r + 1) ≤
      C₀ ^ (2 * j) * (C₀ * diam T) ^ (r + 1 - j) := by
  obtain ⟨hB, hBs, -⟩ := hS T hT
  have hh := diam_nonneg T
  set nB := ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖
  set nBs := ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖
  have hCh : 0 ≤ C₀ * diam T := (norm_nonneg _).trans hB
  have hsplit : nB ^ (r + 1) = nB ^ j * nB ^ (r + 1 - j) := by
    rw [← pow_add, Nat.add_sub_cancel' hj]
  calc nBs ^ j * nB ^ (r + 1) = (nB ^ j * nBs ^ j) * nB ^ (r + 1 - j) := by rw [hsplit]; ring
    _ ≤ ((C₀ * diam T) ^ j * (C₀ / diam T) ^ j) * (C₀ * diam T) ^ (r + 1 - j) := by
        have h0 : 0 ≤ (C₀ * diam T) ^ j * (C₀ / diam T) ^ j := by
          rw [← mul_pow, show C₀ * diam T * (C₀ / diam T) = diam T * (C₀ * C₀ / diam T) by ring]
          have := mul_self_nonneg C₀
          positivity
        gcongr
    _ ≤ C₀ ^ (2 * j) * (C₀ * diam T) ^ (r + 1 - j) := by
        gcongr; exact pow_mul_div_pow_le hh j

/-- **Local interpolation error on a shape-regular family**: if `‖B_T‖ ≤ C₀ h_T`,
`‖B_T⁻¹‖ ≤ C₀ / h_T`, `‖Φ_T‖ ≤ A ‖B_T‖^k` and `‖Φ_T⁻¹‖ ≤ A ‖B_T⁻¹‖^k` (the scaling of `k`-form
pullbacks), then
`sup_T ‖u - Π_T u‖ ≤ A² C₀^{2k} (1 + C (m + 1)) (C₀ h_T)^{r+1} sup_T ‖D^{r+1} u‖`. -/
theorem norm_sub_transportInterp_le_of_isShapeRegular (hI : IsRefInterpolant n r m G I C)
    (hC : 0 ≤ C) {S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)} {C₀ c : ℝ}
    (hS : IsShapeRegular S C₀ c) {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ S)
    (Φ : G ≃L[ℝ] G) {A : ℝ} {k : ℕ}
    (hΦ : ‖(Φ : G →L[ℝ] G)‖ ≤ A * ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ k)
    (hΦs : ‖(Φ.symm : G →L[ℝ] G)‖ ≤
      A * ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ k)
    {u : (Fin n → ℝ) → G} {U : Set (Fin n → ℝ)} {M : ℝ} (hU : IsOpen U)
    (hTU : T.closedInterior ⊆ U) (hu : ContDiffOn ℝ (r + 1) u U)
    (hM : ∀ y ∈ T.closedInterior, ‖iteratedFDeriv ℝ (r + 1) u y‖ ≤ M)
    {x : Fin n → ℝ} (hx : x ∈ T.closedInterior) :
    ‖u x - transportInterp T Φ I u x‖ ≤
      A ^ 2 * C₀ ^ (2 * k) * (1 + C * (m + 1)) * (C₀ * diam T) ^ (r + 1) * M := by
  obtain ⟨hB, -, -⟩ := hS T hT
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x hx)
  set nB := ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖
  have hΦΦ := norm_symm_mul_norm_le_of_isShapeRegular hS hT Φ hΦ hΦs
  have hC1 : 0 ≤ 1 + C * (m + 1) := by positivity
  calc ‖u x - transportInterp T Φ I u x‖ ≤
        ‖(Φ.symm : G →L[ℝ] G)‖ * ((1 + C * (m + 1)) * (‖(Φ : G →L[ℝ] G)‖ * nB ^ (r + 1) * M)) :=
        norm_sub_transportInterp_le hI T Φ hU hTU hu hM hx
    _ = (‖(Φ.symm : G →L[ℝ] G)‖ * ‖(Φ : G →L[ℝ] G)‖) * (1 + C * (m + 1)) * nB ^ (r + 1) * M := by
        ring
    _ ≤ (A ^ 2 * C₀ ^ (2 * k)) * (1 + C * (m + 1)) * (C₀ * diam T) ^ (r + 1) * M := by
        have h2k : 0 ≤ C₀ ^ (2 * k) := by rw [pow_mul]; positivity
        refine mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_right hΦΦ hC1)
          (pow_le_pow_left₀ (norm_nonneg _) hB _) (by positivity) (by positivity)) hM0

/-! ### Derivative estimates -/

/-- The interpolation error on `T` is the transported reference error:
`u - Π_T u = Φ⁻¹ ∘ (û - I û) ∘ F_T⁻¹` on all of `ℝⁿ`. -/
theorem sub_transportInterp_eq (T : Affine.Simplex ℝ (Fin n → ℝ) n) (Φ : G ≃L[ℝ] G)
    (I : ((Fin n → ℝ) → G) → (Fin n → ℝ) → G) (u : (Fin n → ℝ) → G) :
    (fun x => u x - transportInterp T Φ I u x) = fun x =>
      Φ.symm ((fun y => refPullback T Φ u y - I (refPullback T Φ u) y) (refMapInv T x)) := by
  funext x
  simp [transportInterp, refPullback, map_sub]

/-- **Local derivative estimate**: if the reference interpolant has the order-`j` estimate with
constant `K` (`HasRefDerivEstimate`), then on `T`
`sup_T ‖D^j (u - Π_T u)‖ ≤ ‖Φ⁻¹‖ ‖B_T⁻¹‖^j K ‖Φ‖ ‖B_T‖^{r+1} sup_T ‖D^{r+1} u‖`. -/
theorem norm_iteratedFDeriv_sub_transportInterp_le {j : ℕ} {K : ℝ}
    (hI : HasRefDerivEstimate n r j G I K) (T : Affine.Simplex ℝ (Fin n → ℝ) n) (Φ : G ≃L[ℝ] G)
    {u : (Fin n → ℝ) → G} {U : Set (Fin n → ℝ)} {M : ℝ} (hU : IsOpen U)
    (hTU : T.closedInterior ⊆ U) (hu : ContDiffOn ℝ (r + 1) u U)
    (hM : ∀ y ∈ T.closedInterior, ‖iteratedFDeriv ℝ (r + 1) u y‖ ≤ M)
    {x : Fin n → ℝ} (hx : x ∈ T.closedInterior) :
    ‖iteratedFDeriv ℝ j (fun x => u x - transportInterp T Φ I u x) x‖ ≤
      ‖(Φ.symm : G →L[ℝ] G)‖ * ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ j *
        (K * (‖(Φ : G →L[ℝ] G)‖ *
          ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ (r + 1) * M)) := by
  have hxh : refMapInv T x ∈ (refSimplex n).closedInterior :=
    (mem_closedInterior_iff_refMapInv T).1 hx
  have hmem : ∀ y ∈ (refSimplex n).closedInterior, T.refMap y ∈ T.closedInterior :=
    fun y hy => by rw [T.closedInterior_eq_image_refMap]; exact mem_image_of_mem _ hy
  have hTU' : (refSimplex n).closedInterior ⊆ T.refMap ⁻¹' U := fun y hy => hTU (hmem y hy)
  have hM' : ∀ y ∈ (refSimplex n).closedInterior,
      ‖iteratedFDeriv ℝ (r + 1) (refPullback T Φ u) y‖ ≤
        ‖(Φ : G →L[ℝ] G)‖ * ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ (r + 1) * M :=
    fun y hy => (norm_iteratedFDeriv_refPullback_le T Φ u _ y).trans (by
      gcongr
      exact hM _ (hmem y hy))
  have hest := hI _ _ _ (hU.preimage (contDiff_refMap T (N := 0)).continuous) hTU'
    (contDiffOn_refPullback T Φ hu) hM' _ hxh
  set e := fun y => refPullback T Φ u y - I (refPullback T Φ u) y
  have hcomp : (fun x => u x - transportInterp T Φ I u x) = Φ.symm ∘ fun x => e (refMapInv T x) :=
    sub_transportInterp_eq T Φ I u
  rw [hcomp, ContinuousLinearEquiv.iteratedFDeriv_comp_left, iteratedFDeriv_comp_refMapInv]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  rw [mul_assoc]
  gcongr
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]
  gcongr

/-- **Local derivative estimate on a shape-regular family** (the classical form of
[Ciarlet2002], Thm 3.1.5): for `j ≤ r + 1`,
`sup_T ‖D^j (u - Π_T u)‖ ≤ A² C₀^{2k} K C₀^{2j} (C₀ h_T)^{r+1-j} sup_T ‖D^{r+1} u‖`. -/
theorem norm_iteratedFDeriv_sub_transportInterp_le_of_isShapeRegular {j : ℕ} {K : ℝ}
    (hI : HasRefDerivEstimate n r j G I K) (hK : 0 ≤ K) (hj : j ≤ r + 1)
    {S : Set (Affine.Simplex ℝ (Fin n → ℝ) n)} {C₀ c : ℝ}
    (hS : IsShapeRegular S C₀ c) {T : Affine.Simplex ℝ (Fin n → ℝ) n} (hT : T ∈ S)
    (Φ : G ≃L[ℝ] G) {A : ℝ} {k : ℕ}
    (hΦ : ‖(Φ : G →L[ℝ] G)‖ ≤ A * ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ k)
    (hΦs : ‖(Φ.symm : G →L[ℝ] G)‖ ≤
      A * ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ k)
    {u : (Fin n → ℝ) → G} {U : Set (Fin n → ℝ)} {M : ℝ} (hU : IsOpen U)
    (hTU : T.closedInterior ⊆ U) (hu : ContDiffOn ℝ (r + 1) u U)
    (hM : ∀ y ∈ T.closedInterior, ‖iteratedFDeriv ℝ (r + 1) u y‖ ≤ M)
    {x : Fin n → ℝ} (hx : x ∈ T.closedInterior) :
    ‖iteratedFDeriv ℝ j (fun x => u x - transportInterp T Φ I u x) x‖ ≤
      A ^ 2 * C₀ ^ (2 * k) * K * C₀ ^ (2 * j) * (C₀ * diam T) ^ (r + 1 - j) * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x hx)
  have hΦΦ := norm_symm_mul_norm_le_of_isShapeRegular hS hT Φ hΦ hΦs
  have hBB := norm_symm_pow_mul_norm_pow_le_of_isShapeRegular hS hT (r := r) hj
  have hBB0 : 0 ≤ ‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ j *
      ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ (r + 1) := by positivity
  calc _ ≤ _ := norm_iteratedFDeriv_sub_transportInterp_le hI T Φ hU hTU hu hM hx
    _ = (‖(Φ.symm : G →L[ℝ] G)‖ * ‖(Φ : G →L[ℝ] G)‖) * K *
          (‖(T.linearEquiv.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ j *
            ‖(T.linearEquiv : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)‖ ^ (r + 1)) * M := by ring
    _ ≤ (A ^ 2 * C₀ ^ (2 * k)) * K * (C₀ ^ (2 * j) * (C₀ * diam T) ^ (r + 1 - j)) * M := by
        have h2k : 0 ≤ C₀ ^ (2 * k) := by rw [pow_mul]; positivity
        have : 0 ≤ A ^ 2 * C₀ ^ (2 * k) * K := mul_nonneg (mul_nonneg (sq_nonneg A) h2k) hK
        gcongr
    _ = _ := by ring

end Feec.FiniteElement
