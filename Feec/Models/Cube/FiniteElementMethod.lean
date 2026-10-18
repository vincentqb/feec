module

public import Feec.FiniteElement.SmoothedProjection
public import Feec.FiniteElement.WhitneyComplex
public import Feec.Domain.StarShapedSmoothing
public import Feec.HilbertComplex.Approximation.Convergence

/-!
# Smoothed projections and the finite element method on cube meshes

**The smoothed canonical interpolant.** For an element family `E` on a conforming simplicial
mesh `M` of an open `Ω ⊆ ℝⁿ` star-shaped with respect to a ball `B(x₀, s₀)` (cubes, convex
domains), and maximal-family smoothing parameters `p` (dilation factor `½ ≤ c < 1` about `x₀`,
bump radius `< s₀ (1 - c) / 4`, `Feec.Domain.SmoothingParam.IsMaximal`):

* `smoothForm`: the smoothed `k`-form `x ↦ Σₛ cᵏ (ū ⋆ ρ)(x₀ + c (x - x₀)) dxₛ` of
  `u ∈ L²(Ω; Λᵏ)`, smooth on `ℝⁿ`; `d` of it is the smoothed form of `d_max u` on `cl Ω`
  (`extDeriv_smoothForm_of_maximal`: the pullback by the dilation commutes with `d`);
* `LocalElement.smoothedInterp`: `Q = Π_h R`, the glued canonical interpolant of the smoothed
  form; **`d_max Q u = Q d_max u`** (`LocalElement.maximal_smoothedInterp`, using that `Π_h`
  commutes with `d` on smooth forms and only sees `cl Ω`, `LocalElement.globalInterp_congr`);
* **`LocalElement.smoothedCommutingMap`**: `Q` as a `Feec.HilbertComplex.Subcomplex.CommutingMap`
  into the finite element subcomplex `Vₕ ⊆ HΛ(Ω)`, the input of the smoothed-projection
  construction `π = J⁻¹ Q` (`Feec.FiniteElement.SmoothedProjection`).

**The cube.** On `Q = (0, ½)ⁿ` (`FEM.cubeDomain`, star-shaped with respect to `B((¼, …, ¼), ¼)`,
`FEM.starBall`) with the level-`(N + 1)` Freudenthal meshes (`FEM.mesh`, mesh size
`h_N = 1 / (2 (N + 1))`, `FEM.meshSize`), the Whitney complexes `FEM.whitney N` (Lagrange `P₁`,
Nédélec, Raviart–Thomas, piecewise constants; transported to one Hilbert complex
`FEM.complex = HΛ(Q)`) carry the concrete smoothed interpolants `FEM.smoothed N p`. Under the
**estimates of [AFW2010], §5.4 and [ChristiansenWinther2008]** for these maps (uniform `L²`
bound `C` and `‖v - Q_N v‖ ≤ ½ ‖v‖` on `Vₕ`; `FEM.SmoothingEstimates`, an explicit hypothesis:
the elementwise inverse estimates behind it are not formalized), every consequence is proved:

* uniformly bounded cochain projections `π_N` with `‖π_N‖ ≤ 2C` in `L²` and in the graph norm
  (`SmoothingEstimates.proj`, `norm_proj_le`, `isGraphBounded_proj`);
* the uniform discrete Poincaré inequality (`SmoothingEstimates.norm_le_of_forall_inner_eq_zero`)
  and the uniform well-posedness and stability of the discrete mixed Hodge Laplacian
  (`SmoothingEstimates.existsUnique_mixed`, `SmoothingEstimates.norm_le_of_mixed`), given the
  Poincaré inequality of `HΛ(Q)`;
* quasi-optimality with an `N`-independent constant (`SmoothingEstimates.norm_sub_le_infDist`) and
  `O(h)` convergence when the solution is approximated at rate `h`
  (`SmoothingEstimates.norm_sub_le_meshSize`);
* the harmonic gap tends to zero (`SmoothingEstimates.tendsto_harmonicGap`), when `ℌ` is
  finite-dimensional and approximated by the Whitney spaces;
* for the Hodge wave equation of any window, the Whitney windows are approximating as soon as they
  are dense (`FEM.isApproximating_window`), hence convergence of the semi-discrete solutions
  (`FEM.exists_tendstoUniformlyOn_window`), and the rate `‖ξ(t) - ξₕ(t)‖ ≤ A (1 + t - t₀)² K h_N`
  when the solution and its time derivative are approximable at rate `h`
  (`FEM.norm_sub_le_meshSize_window`, from `Feec.HodgeWave.norm_sub_le_of_semidiscrete`, which needs
  no smoothed projection); **Maxwell's equations** (perfect
  magnetic conductor, `n = 3`, window `HΛ⁰ → HΛ¹ → L²Λ²`) are the instance
  `FEM.maxwell_exists_tendstoUniformlyOn`.

**Remaining hypotheses.** (1) `FEM.SmoothingEstimates` (the analytic core of [AFW2010], §5.4:
inverse estimates and the interpolation error of `Π_h` on smoothed fields with `ε ≈ h`);
(2) the Poincaré inequality of `HΛ(Q)` (proved in the parity model `Feec.Models.Cube.DeRham`, whose
identification with `HΛ(Q)` is not formalized); (3) approximation properties of the Whitney spaces
(interpolation error for smooth forms; [Arnold2018], Ch. 7; `Feec.FiniteElement.InterpolationError`
gives it for reference interpolants satisfying `IsRefInterpolant`, which is not instantiated for
Whitney forms). For the Einstein–Bianchi (BGG) system, `Feec.BGG.Discrete` needs subcomplexes of
both rows with cochain projections satisfying `Π S = S_h Π'`; vector-valued Whitney forms and such
a pair of projections are not constructed, so that structure remains an explicit hypothesis of
`Feec.HilbertComplex.BGG.Discrete`. The vanishing-trace family `H̊Λ(Q)` (minimal smoother of
`Feec.Domain.StarShapedSmoothing` with zero boundary DOFs) is not treated here.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.4 (smoothed projections), Thm 3.6, Thm 3.8, Thm 3.9
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §5 (canonical interpolants, Whitney forms)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (bounded commuting
  projections, approximation)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 4.14 (convergence of the semi-discrete Hodge wave equation)
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped ContDiff

namespace Feec.FiniteElement

open Feec.Domain Feec.Mesh Feec.ExteriorFibre

variable {n : ℕ}

/-! ## The smoothed form field -/

section SmoothForm

variable {Ω : Set (Fin n → ℝ)} (p : SmoothingParam (Fin n → ℝ))

/-- The coefficients `cᵏ R̃ uₛ` of the smoothed `k`-form (pullback by the dilation, then
mollification). -/
def smoothCoeff (p : SmoothingParam (Fin n → ℝ)) (k : ℤ) (u : L2F ℝ Ω (formIdx n k)) (s : formIdx n k) : (Fin n → ℝ) → ℝ :=
  fun x => p.factor ^ k * smoothExt Ω p ((u s : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) x

theorem contDiff_smoothCoeff (hΩ : MeasurableSet Ω) (k : ℤ) (u : L2F ℝ Ω (formIdx n k)) (s : formIdx n k) :
    ContDiff ℝ ∞ (smoothCoeff p k u s) :=
  contDiff_const.mul (contDiff_smoothExt ((memLp_indicator hΩ _).locallyIntegrable (by norm_num)))

/-- **The smoothed `k`-form** `x ↦ Σₛ cᵏ (R̃ uₛ)(x) dxₛ`, a smooth form field on `ℝⁿ`, as a
linear map `L²(Ω; Λᵏ) → C¹Λᵏ`. -/
def smoothForm (p : SmoothingParam (Fin n → ℝ)) (hΩ : MeasurableSet Ω) (k : ℤ) : L2F ℝ Ω (formIdx n k) →ₗ[ℝ] c1Forms n where
  toFun u := ⟨fun x t => formExt (smoothCoeff p k u) t x,
    mem_c1Forms.2 (contDiff_pi.2 fun t =>
      (contDiff_formExt (contDiff_smoothCoeff p hΩ k u) t).of_le (by exact_mod_cast le_top))⟩
  map_add' u v := by
    refine Subtype.ext (funext fun x => funext fun t => ?_)
    change formExt (smoothCoeff p k (u + v)) t x =
      formExt (smoothCoeff p k u) t x + formExt (smoothCoeff p k v) t x
    unfold formExt
    split_ifs with h
    · simp only [smoothCoeff, PiLp.add_apply, smoothExt_coe_add hΩ, Pi.add_apply]; ring
    · simp
  map_smul' a u := by
    refine Subtype.ext (funext fun x => funext fun t => ?_)
    change formExt (smoothCoeff p k (a • u)) t x = a * formExt (smoothCoeff p k u) t x
    unfold formExt
    split_ifs with h
    · simp only [smoothCoeff, PiLp.smul_apply, smoothExt_coe_smul hΩ, Pi.smul_apply,
        smul_eq_mul]; ring
    · simp

theorem smoothForm_apply (hΩ : MeasurableSet Ω) (k : ℤ) (u : L2F ℝ Ω (formIdx n k)) (x : Fin n → ℝ)
    (t : Finset (Fin n)) :
    (smoothForm p hΩ k u : FormField n) x t = formExt (smoothCoeff p k u) t x := rfl

theorem isDeg_smoothForm (hΩ : MeasurableSet Ω) (k : ℕ) (u : L2F ℝ Ω (formIdx n k)) (x : Fin n → ℝ) :
    IsDeg k ((smoothForm p hΩ k u : FormField n) x) := by
  intro t ht
  rw [smoothForm_apply]
  unfold formExt
  split_ifs with h
  · exact absurd (by exact_mod_cast h) ht
  · rfl

theorem formComp_smoothForm (hΩ : MeasurableSet Ω) (k : ℕ) (u : L2F ℝ Ω (formIdx n k)) :
    formComp (k := (k : ℤ)) (smoothForm p hΩ k u : FormField n) =
      fun s => p.factor ^ (k : ℤ) • smoothExt Ω p ((u s : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) := by
  funext s x
  change formExt (smoothCoeff p k u) s.1 x = _
  rw [formExt_val]
  rfl

/-- **`d` of the smoothed form is the smoothed form of `d_max u`** on `cl Ω` (maximal family,
`Ω` star-shaped with respect to `B(x₀, s₀)`): the pullback by the dilation commutes with `d`. -/
theorem extDeriv_smoothForm_of_maximal (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω) {x₀ : Fin n → ℝ} {s₀ : ℝ}
    (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ Ω) (hp : p.IsMaximal x₀ s₀)
    (k : ℕ) (u : ((extDerivOp ℝ n k).maximal Ω).domain) {x : Fin n → ℝ} (hx : x ∈ closure Ω) :
    extDeriv (smoothForm p hΩ k u : FormField n) x =
      (smoothForm p hΩ ((k : ℤ) + 1) ((extDerivOp ℝ n k).maximal Ω u) : FormField n) x := by
  funext t
  by_cases ht : (#t : ℤ) = (k : ℤ) + 1
  · have h1 := extDerivOp_apply_formComp (isDeg_smoothForm p hΩ k (u : L2F ℝ Ω (formIdx n k)))
      ⟨t, ht⟩ x
    rw [formComp_smoothForm] at h1
    rw [← h1, apply_smoothExt_of_maximal hΩo hstar hp (extDerivOp_isRowHomogeneous k) u _ _ hx,
      smoothForm_apply, formExt_of_card _ ht]
    change _ = p.factor ^ ((k : ℤ) + 1) * _
    rw [pow_one, zpow_add_one₀ p.factor_pos.ne']
  · have h0 := IsDeg.extDeriv (isDeg_smoothForm p hΩ k (u : L2F ℝ Ω (formIdx n k))) x t
      (fun h => ht (by exact_mod_cast h))
    rw [h0, smoothForm_apply]
    simp [formExt, ht]

end SmoothForm

/-! ## The smoothed canonical interpolant of an element family -/

namespace LocalElement

variable (E : LocalElement n) (M : SimplicialMesh n)

/-- **`Π_h` only sees values on `cl Ω`**: continuous forms agreeing on the closure of the meshed
domain have the same canonical interpolant. -/
theorem globalInterp_congr (k : ℕ) {w w' : contForms n}
    (h : ∀ x ∈ closure M.domain, (w : FormField n) x = (w' : FormField n) x) :
    E.globalInterp M k w = E.globalInterp M k w' := by
  refine E.globalInterp_piecewise M k _ w fun T g hg i => ?_
  rw [localDof_globalInterp _ _ _ _ _ _ hg]
  refine E.dof_congr i fun x hx V _ => ?_
  have hxT : x ∈ (T : Affine.Simplex ℝ (Fin n → ℝ) n).closedInterior := by
    rw [← Mesh.convexHull_vertexSet]
    exact convexHull_mono (Finset.coe_subset.2 hg) hx
  have hxΩ : x ∈ closure M.domain := by
    rw [← M.biUnion_closedInterior]
    exact Set.mem_biUnion T.2 hxT
  rw [h x hxΩ]

variable (p : SmoothingParam (Fin n → ℝ))

/-- **The smoothed canonical interpolant** `Q = Π_h R : L²(Ω; Λᵏ) → Vₕᵏ`: glue the canonical
interpolant of the smoothed form ([AFW2010], §5.4); zero in negative degrees. -/
def smoothedInterp (p : SmoothingParam (Fin n → ℝ)) (hΩ : MeasurableSet M.domain) : ∀ k : ℤ, L2F ℝ M.domain (formIdx n k) →ₗ[ℝ] L2F ℝ M.domain (formIdx n k)
  | Int.ofNat k => E.glue M k ∘ₗ (E.globalSpace M k).subtype ∘ₗ E.globalInterp M k ∘ₗ
      Submodule.inclusion c1Forms_le_contForms ∘ₗ smoothForm p hΩ k
  | Int.negSucc _ => 0

theorem smoothedInterp_natCast (hΩ : MeasurableSet M.domain) (k : ℕ) (u : L2F ℝ M.domain (formIdx n k)) :
    E.smoothedInterp M p hΩ k u = E.glue M k (E.globalInterp M k
      (Submodule.inclusion c1Forms_le_contForms (smoothForm p hΩ k u)) : E.Piecewise M k) := rfl

theorem smoothedInterp_mem_V (hΩ : MeasurableSet M.domain) (k : ℤ) (u : L2F ℝ M.domain (formIdx n k)) :
    E.smoothedInterp M p hΩ k u ∈ E.V M k := by
  rcases k with k | k
  · exact ⟨_, rfl⟩
  · exact Submodule.zero_mem _

/-- **`d_max Q u = Q d_max u`** (maximal family): the canonical interpolant commutes with `d` on
smooth forms (`globalInterp_extDeriv`), sees only `cl Ω` (`globalInterp_congr`), and the
smoother commutes with `d_max` there (`extDeriv_smoothForm_of_maximal`). -/
theorem maximal_smoothedInterp [NeZero n] (hΩ : MeasurableSet M.domain) (hΩo : IsOpen M.domain) {x₀ : Fin n → ℝ} {s₀ : ℝ}
    (hstar : ∀ y ∈ M.domain, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ M.domain)
    (hp : p.IsMaximal x₀ s₀) (k : ℕ) (u : ((extDerivOp ℝ n k).maximal M.domain).domain) :
    ∃ h : E.smoothedInterp M p hΩ k u ∈ ((extDerivOp ℝ n k).maximal M.domain).domain,
      (extDerivOp ℝ n k).maximal M.domain ⟨_, h⟩ =
        E.smoothedInterp M p hΩ ((k : ℤ) + 1) ((extDerivOp ℝ n k).maximal M.domain u) := by
  set w := smoothForm p hΩ k (u : L2F ℝ M.domain (formIdx n k))
  obtain ⟨h, hval⟩ := E.glue_mem_maximal M hΩo k
    (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w))
  refine ⟨h, hval.trans ?_⟩
  have h1 : E.dPiecewise M k
      (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w) : E.Piecewise M k) =
      (E.dGlobal M k (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w)) :
        E.Piecewise M (k + 1)) := rfl
  rw [h1, ← globalInterp_extDeriv]
  have h2 : E.globalInterp M (k + 1) (extDerivC1 w) = E.globalInterp M (k + 1)
      (Submodule.inclusion c1Forms_le_contForms
        (smoothForm p hΩ ((k + 1 : ℕ) : ℤ) ((extDerivOp ℝ n k).maximal M.domain u))) :=
    E.globalInterp_congr M (k + 1) fun x hx =>
      extDeriv_smoothForm_of_maximal p hΩ hΩo hstar hp k u hx
  rw [h2]
  rfl

/-- Evaluating equal partial maps. -/
theorem _root_.LinearPMap.apply_eq_of_eq' {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {T T' : V →ₗ.[ℝ] W} (h : T = T') (x : T.domain) :
    T x = T' ⟨x, h ▸ x.2⟩ := by
  subst h; rfl

/-- **The smoothed canonical interpolant as a commuting map** into the finite element subcomplex
`Vₕ ⊆ HΛ(Ω)` (maximal family, `Ω` star-shaped with respect to `B(x₀, s₀)`): `Q = Π_h R` with
`d Q = Q d` in every degree. -/
def smoothedCommutingMap [NeZero n] (hΩo : IsOpen M.domain) {x₀ : Fin n → ℝ} {s₀ : ℝ}
    (hstar : ∀ y ∈ M.domain, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ M.domain)
    (hp : p.IsMaximal x₀ s₀) : (E.subcomplex M hΩo).CommutingMap where
  Q := E.smoothedInterp M p hΩo.measurableSet
  mem i x := E.smoothedInterp_mem_V M p hΩo.measurableSet i x
  comm i j x := by
    by_cases hij : i + 1 = j
    · subst hij
      have hd := deRham_maximalComplex_d (𝕜 := ℝ) (n := n) hΩo i
      rcases i with k | k
      · rw [LinearPMap.apply_eq_of_eq' hd, LinearPMap.apply_eq_of_eq' hd x]
        obtain ⟨h, hv⟩ := E.maximal_smoothedInterp M p hΩo.measurableSet hΩo hstar hp k
          ⟨x.1, hd ▸ x.2⟩
        exact hv
      · have h0 : ∀ y : (((deRham ℝ n).maximalComplex hΩo).d (Int.negSucc k)
            (Int.negSucc k + 1)).domain, ((deRham ℝ n).maximalComplex hΩo).d _ _ y = 0 := by
          intro y
          have : y = 0 := Subtype.ext ((subsingleton_L2F_negSucc M.domain k).elim _ _)
          rw [this, LinearPMap.map_zero]
        rw [h0, h0]
        exact (E.smoothedInterp M p hΩo.measurableSet _).map_zero.symm
    · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hij),
        HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hij)]
      exact (E.smoothedInterp M p hΩo.measurableSet j).map_zero.symm

@[simp] theorem smoothedCommutingMap_Q [NeZero n] (hΩo : IsOpen M.domain) {x₀ : Fin n → ℝ}
    {s₀ : ℝ} (hstar : ∀ y ∈ M.domain, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ M.domain)
    (hp : p.IsMaximal x₀ s₀) (i : ℤ) :
    (E.smoothedCommutingMap M p hΩo hstar hp).Q i = E.smoothedInterp M p hΩo.measurableSet i :=
  rfl

end LocalElement

end Feec.FiniteElement

/-! ## Transport of subcomplexes along an equality of domains -/

namespace Feec.Domain.ConstCoeffComplex

variable {n : ℕ} (C : ConstCoeffComplex (Fin n → ℝ) ℝ)

/-- A subcomplex of the maximal complex on `Ω`, as a subcomplex of the maximal complex on
`Ω' = Ω`. -/
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

end Feec.Domain.ConstCoeffComplex

/-! ## Windows of subcomplexes -/

namespace Feec.HilbertComplex.Subcomplex

variable {𝕜 : Type*} [RCLike 𝕜] {V : ℤ → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace 𝕜 (V i)] [∀ i, CompleteSpace (V i)]
  {H : HilbertComplex 𝕜 (ComplexShape.up ℤ) V}

/-- The window `Vₕ^a → ⋯ → Vₕ^{a + m - 1}` of a subcomplex, a subcomplex of `H.window a m`. -/
def window (S : H.Subcomplex) (a : ℤ) (m : ℕ) : (H.window a m).Subcomplex where
  V i := S.V (a + i)
  le_domain _ _ := S.le_domain _ _
  mapsTo _ _ := S.mapsTo _ _

instance (S : H.Subcomplex) [∀ i, FiniteDimensional 𝕜 (S.V i)] (a : ℤ) (m : ℕ) (i : Fin m) :
    FiniteDimensional 𝕜 ((S.window a m).V i) :=
  inferInstanceAs (FiniteDimensional 𝕜 (S.V (a + i)))

end Feec.HilbertComplex.Subcomplex

/-! ## Rate of the semi-discrete Hodge wave equation on a subcomplex -/

namespace Feec.HilbertComplex.Subcomplex

open _root_.Feec.HodgeWave

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  {H : HilbertComplex 𝕜 c W}

/-- **Rate of the semi-discrete Hodge wave equation on a finite-dimensional subcomplex**
([QuennevilleBelair2015], Thm 4.14): if `ξ` is a weak solution in `C¹([t₀, t₁]; Γ(𝐝))`, `ξₕ` the
semi-discrete solution in `S` started at the elliptic projection `Pₕ ξ(t₀)`, and `ξ(s)`, `ξ'(s)`
are within `η` of `S` in the graph norm on `[t₀, t₁]`, then
`‖ξ(t) - ξₕ(t)‖ ≤ A (1 + (t - t₀))² η` with `A = 1 + √12 ‖a + m‖` independent of `S`
(`Feec.HodgeWave.norm_sub_ellipticProjection_le`, `Feec.HodgeWave.IsGraphSolution.norm_sub_le`). -/
theorem norm_sub_le_of_approx (S : H.Subcomplex) [∀ i, FiniteDimensional 𝕜 (S.V i)]
    {t₀ t₁ : ℝ} {ξ ξ' ξh ξh' : ℝ → H.totalD.GraphSpace}
    (hξ : IsGraphSolution (Set.Icc t₀ t₁) ξ ξ')
    (hξh : IsSemidiscreteSolution S.graphSub (Set.Icc t₀ t₁) ξh ξh')
    (h0 : ξh t₀ = ellipticProjection S.graphSub (ξ t₀)) {η : ℝ}
    (happ : ∀ s ∈ Set.Icc t₀ t₁, (∃ w ∈ S.graphSub, ‖ξ s - w‖ ≤ η) ∧
      (∃ w ∈ S.graphSub, ‖ξ' s - w‖ ≤ η))
    {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    ‖H.totalD.graphFst (ξ t - ξh t)‖ ≤
      (1 + ‖shiftedForm H.totalD‖ / ((1 / 2) / √3)) * (1 + (t - t₀)) ^ 2 * η := by
  set A : ℝ := 1 + ‖shiftedForm H.totalD‖ / ((1 / 2) / √3) with hAdef
  have hA : 0 ≤ A := by positivity
  have hP : ∀ ζ : H.totalD.GraphSpace, (∃ w ∈ S.graphSub, ‖ζ - w‖ ≤ η) →
      ‖H.totalD.graphFst (ellipticProjection S.graphSub ζ - ζ)‖ ≤ A * η := by
    rintro ζ ⟨w, hw, hζw⟩
    refine (norm_graphFst_le _).trans ?_
    rw [norm_sub_rev]
    exact (norm_sub_ellipticProjection_le H.totalD_mapsTo H.totalD_comp_totalD
      S.graphSub (fun _ hv => S.graphD_mem_graphSub hv) ζ hw).trans
      (mul_le_mul_of_nonneg_left hζw hA)
  have hb := hξ.norm_sub_le hξh t ht
  have hz : ‖H.totalD.graphFst (ellipticProjection S.graphSub (ξ t₀) - ξh t₀)‖ = 0 := by
    rw [h0, sub_self (ellipticProjection S.graphSub (ξ t₀) : H.totalD.GraphSpace)]
    exact norm_eq_zero.2 (H.totalD.graphFst.map_zero)
  rw [hz, zero_add] at hb
  have ht₀ : t₀ ∈ Set.Icc t₀ t₁ := ⟨le_rfl, ht.1.trans ht.2⟩
  have e1 := hP _ (happ t ht).1
  have e0 := hP _ (happ t₀ ht₀).1
  have hτ : 0 ≤ t - t₀ := sub_nonneg.2 ht.1
  have hint : ∫ s in t₀..t, ‖H.totalD.graphFst (ellipticProjection S.graphSub (ξ' s) - ξ' s)‖ ≤
      (t - t₀) * (A * η) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := t₀) (b := t)
      (C := A * η)
      (f := fun s => ‖H.totalD.graphFst (ellipticProjection S.graphSub (ξ' s) - ξ' s)‖)
      fun s hs => by
        rw [Set.uIoc_of_le ht.1] at hs
        rw [norm_norm]
        exact hP _ (happ s ⟨hs.1.le, hs.2.trans ht.2⟩).2
    rw [abs_of_nonneg hτ, mul_comm] at h
    exact (le_abs_self _).trans h
  have i1 : (t - t₀) * ‖H.totalD.graphFst (ellipticProjection S.graphSub (ξ t₀) - ξ t₀)‖ ≤
      (t - t₀) * (A * η) := mul_le_mul_of_nonneg_left e0 hτ
  have i2 : (1 + (t - t₀)) *
      ∫ s in t₀..t, ‖H.totalD.graphFst (ellipticProjection S.graphSub (ξ' s) - ξ' s)‖ ≤
      (1 + (t - t₀)) * ((t - t₀) * (A * η)) := mul_le_mul_of_nonneg_left hint (by linarith)
  calc _ ≤ _ := hb
    _ ≤ A * η + (t - t₀) * (A * η) + (1 + (t - t₀)) * ((t - t₀) * (A * η)) := by linarith
    _ = A * (1 + (t - t₀)) ^ 2 * η := by ring

end Feec.HilbertComplex.Subcomplex

/-! ## Freudenthal meshes of the cube `(0, ½)ⁿ` -/

namespace Feec.Models.Cube.FEM

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex

variable (n : ℕ)

/-- The cube `Q = (0, ½)ⁿ`. -/
def cubeDomain : Set (Fin n → ℝ) := Set.univ.pi fun _ => Set.Ioo 0 (1 / 2)

theorem isOpen_cubeDomain : IsOpen (cubeDomain n) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

theorem convex_cubeDomain : Convex ℝ (cubeDomain n) :=
  convex_pi fun _ _ => convex_Ioo _ _

/-- The maximal de Rham complex `HΛ(Q)` of the cube. -/
abbrev complex : HilbertComplex ℝ (ComplexShape.up ℤ) fun k => L2F ℝ (cubeDomain n) (formIdx n k) :=
  (deRham ℝ n).maximalComplex (isOpen_cubeDomain n)

/-- The centre `(¼, …, ¼)` of the cube. -/
def center : Fin n → ℝ := fun _ => 1 / 4

/-- **The cube is star-shaped with respect to the ball `B(centre, ¼)`** (in the sup norm of
`ℝⁿ` this ball is the cube itself; the cube is convex). -/
theorem starBall : ∀ y ∈ cubeDomain n, ∀ z ∈ Metric.ball (center n) (1 / 4),
    segment ℝ z y ⊆ cubeDomain n := by
  intro y hy z hz
  have hzQ : z ∈ cubeDomain n := by
    rw [Metric.mem_ball, dist_pi_lt_iff (by norm_num)] at hz
    intro i _
    have := hz i
    rw [Real.dist_eq, center, abs_lt] at this
    constructor <;> linarith
  exact (convex_cubeDomain n).segment_subset hzQ hy

/-- The level-`(N + 1)` Freudenthal mesh of the cube, mesh size `h = 1 / (2 (N + 1))`. -/
def mesh (N : ℕ) : SimplicialMesh n := freudenthalMesh 0 (1 / 2) (by norm_num) (N + 1)

/-- The mesh size `h_N = 1 / (2 (N + 1))` (the edge of the cubes of the Freudenthal mesh). -/
def meshSize (N : ℕ) : ℝ := 1 / 2 / (N + 1)

theorem meshSize_pos (N : ℕ) : 0 < meshSize N := by unfold meshSize; positivity

theorem tendsto_meshSize : Tendsto meshSize atTop (𝓝 0) := by
  unfold meshSize
  exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

theorem mesh_domain (N : ℕ) : (mesh n N).domain = cubeDomain n := by
  rw [mesh, freudenthalMesh_domain]
  simp [cubeDomain]

theorem isOpen_mesh_domain (N : ℕ) : IsOpen (mesh n N).domain :=
  isOpen_freudenthalMesh_domain _ _ _ _

theorem starBall_mesh (N : ℕ) : ∀ y ∈ (mesh n N).domain, ∀ z ∈ Metric.ball (center n) (1 / 4),
    segment ℝ z y ⊆ (mesh n N).domain := by
  rw [mesh_domain]; exact starBall n

variable [NeZero n]

/-- **The Whitney complex of the level-`(N + 1)` Freudenthal mesh** (Lagrange `P₁`, and in `ℝ³`
Nédélec edge and Raviart–Thomas face elements, piecewise constants) as a subcomplex of `HΛ(Q)`. -/
def whitney (N : ℕ) : (complex n).Subcomplex :=
  (deRham ℝ n).maximalSubcomplexOfEq (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n) (whitneySubcomplex (mesh n N) (isOpen_mesh_domain n N))

instance (N : ℕ) (k : ℤ) : FiniteDimensional ℝ ((whitney n N).V k) :=
  (deRham ℝ n).finiteDimensional_maximalSubcomplexOfEq _ _ _ _ k

/-- **The smoothed canonical interpolant** `Q_N = Π_h R` on the Freudenthal Whitney complex of
the cube, for maximal-family smoothing parameters centred at the centre of the cube. -/
def smoothed (N : ℕ) (p : SmoothingParam (Fin n → ℝ)) (hp : p.IsMaximal (center n) (1 / 4)) :
    (whitney n N).CommutingMap :=
  (deRham ℝ n).commutingMapOfEq (mesh_domain n N) (isOpen_mesh_domain n N) (isOpen_cubeDomain n)
    ((whitneyElement n).smoothedCommutingMap (mesh n N) p (isOpen_mesh_domain n N)
      (starBall_mesh n N) hp)

/-! ## The finite element method on the cube under the smoothed-projection estimates -/

variable (p : ℕ → SmoothingParam (Fin n → ℝ)) (C : ℝ)

/-- **The estimates of the smoothed canonical interpolants** ([AFW2010], §5.4;
[ChristiansenWinther2008]): for maximal-family smoothing parameters `p N` (any
`IsMaximal` parameters; the structure imposes no scaling), the smoothed interpolants
`Q_N = Π_h R` of the Whitney complexes are bounded in `L²` uniformly in `N`, and close to the
identity on `Vₕ`: `‖v - Q_N v‖ ≤ ½ ‖v‖`. In the references these are obtained with the scaling
factor `1 - δ h_N`, bump radius `≈ δ h_N` and `δ` small, from elementwise inverse estimates for
polynomials and the interpolation error of `Π_h` on smoothed fields; they are not
formalized here and are the hypotheses of this section. The maps `Q_N` themselves are the
concrete smoothed interpolants `smoothed n N (p N)`, and their commutation with `d` is proved
(`Feec.FiniteElement.LocalElement.smoothedCommutingMap`). The constant is normalized by
`½ ≤ C` (any bound can be enlarged). -/
structure SmoothingEstimates : Prop where
  isMaximal : ∀ N, (p N).IsMaximal (center n) (1 / 4)
  half_le : 1 / 2 ≤ C
  bound : ∀ N i x, ‖(smoothed n N (p N) (isMaximal N)).Q i x‖ ≤ C * ‖x‖
  close : ∀ N i, ∀ v ∈ (whitney n N).V i,
    ‖v - (smoothed n N (p N) (isMaximal N)).Q i v‖ ≤ 1 / 2 * ‖v‖

namespace SmoothingEstimates

variable {n p C}

/-- **The smoothed projection** `π_N = J_N⁻¹ Q_N` onto the Whitney complex of the cube. -/
def proj (hE : SmoothingEstimates n p C) (N : ℕ) : (whitney n N).CochainProjection :=
  (smoothed n N (p N) (hE.isMaximal N)).toCochainProjection (θ := 1 / 2) (by norm_num)
    (hE.close N)

theorem two_mul_nonneg (hE : SmoothingEstimates n p C) : 0 ≤ 2 * C := by linarith [hE.half_le]

theorem one_le_two_mul (hE : SmoothingEstimates n p C) : 1 ≤ 2 * C := by linarith [hE.half_le]

variable (hE : SmoothingEstimates n p C)
include hE

/-- **Uniform `L²` bound**: `‖π_N x‖ ≤ 2 C ‖x‖` for every `N`. -/
theorem norm_proj_le (N : ℕ) (i : ℤ) (x : L2F ℝ (cubeDomain n) (formIdx n i)) :
    ‖(hE.proj N).π i x‖ ≤ 2 * C * ‖x‖ := by
  have h := (smoothed n N (p N) (hE.isMaximal N)).norm_toCochainProjection_le (θ := 1 / 2)
    (by norm_num) (hE.close N) (hE.bound N i) x
  have e : (1 - 1 / 2 : ℝ)⁻¹ * C = 2 * C := by norm_num
  rwa [e] at h

/-- **Uniform graph-norm bound**: `π_N` is bounded by `2 C` in the graph norm of every `d`. -/
theorem isGraphBounded_proj (N : ℕ) (i j : ℤ) : (hE.proj N).IsGraphBounded i j (2 * C) := by
  have h := (smoothed n N (p N) (hE.isMaximal N)).isGraphBounded_toCochainProjection_of_norm_le
    (θ := 1 / 2) (by norm_num) (hE.close N) (hE.bound N i) (hE.bound N j)
  have e : (1 - 1 / 2 : ℝ)⁻¹ * C = 2 * C := by norm_num
  rwa [e] at h

/-- **Uniform discrete Poincaré inequality** on the cube meshes: if `‖z‖ ≤ c_P ‖d z‖` on
`(𝔷ⁱ)ᗮ` in `HΛ(Q)`, then `‖x‖ ≤ 2 C c_P ‖d x‖` for `x ∈ Vₕⁱ ⊥ 𝔷ₕⁱ`, for every mesh. -/
theorem norm_le_of_forall_inner_eq_zero {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j) {cP : ℝ}
    (hP : ∀ z : ((complex n).d i j).domain, (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈
      ((complex n).cycles i)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤
        cP * ‖(complex n).d i j z‖)
    (N : ℕ) {x : L2F ℝ (cubeDomain n) (formIdx n i)} (hx : x ∈ (whitney n N).V i)
    (hxo : ∀ y ∈ (whitney n N).cyclesW i, inner ℝ y x = 0) :
    ‖x‖ ≤ 2 * C * cP * ‖(complex n).d i j ⟨x, (whitney n N).le_domain i j hx⟩‖ :=
  (hE.proj N).norm_le_of_forall_inner_eq_zero hij hP hE.two_mul_nonneg (hE.norm_proj_le N i) hx
    hxo

/-- **Uniform well-posedness of the discrete mixed Hodge Laplacian** on the cube meshes
([AFW2010], Thm 3.8): for every `N` and `f ∈ Vₕʲ` the discrete mixed problem has a unique
solution, with `‖xₕ‖ ≤ 16 (2 C c_P)² ‖f‖` (`norm_le_of_mixed`). -/
theorem existsUnique_mixed {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {cP : ℝ} (hcP : 1 ≤ cP)
    (hPi : ∀ z : ((complex n).d i j).domain, (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈
      ((complex n).cycles i)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤
        cP * ‖(complex n).d i j z‖)
    (hPj : ∀ z : ((complex n).d j k).domain, (z : L2F ℝ (cubeDomain n) (formIdx n j)) ∈
      ((complex n).cycles j)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
        cP * ‖(complex n).d j k z‖)
    (N : ℕ) (f : (whitney n N).V j) :
    ∃! x, (whitney n N).toHilbertComplex.mixedForm i j k x =
      (whitney n N).toHilbertComplex.mixedRHS i j f :=
  (hE.proj N).existsUnique_mixed hij hjk hcP hE.one_le_two_mul hPi hPj (hE.norm_proj_le N i)
    (hE.norm_proj_le N j) f

/-- **Uniform stability of the discrete mixed Hodge Laplacian** on the cube meshes:
`‖xₕ‖ ≤ 16 (2 C c_P)² ‖fₕ‖`, independently of `N`. -/
theorem norm_le_of_mixed {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {cP : ℝ} (hcP : 1 ≤ cP)
    (hPi : ∀ z : ((complex n).d i j).domain, (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈
      ((complex n).cycles i)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤
        cP * ‖(complex n).d i j z‖)
    (hPj : ∀ z : ((complex n).d j k).domain, (z : L2F ℝ (cubeDomain n) (formIdx n j)) ∈
      ((complex n).cycles j)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
        cP * ‖(complex n).d j k z‖)
    (N : ℕ) {f : (whitney n N).V j} {x : (whitney n N).toHilbertComplex.MixedSpace i j}
    (hx : (whitney n N).toHilbertComplex.mixedForm i j k x =
      (whitney n N).toHilbertComplex.mixedRHS i j f) :
    ‖x‖ ≤ 16 * (2 * C * cP) ^ 2 * ‖f‖ :=
  (hE.proj N).norm_le_of_mixed hij hjk hcP hE.one_le_two_mul hPi hPj (hE.norm_proj_le N i)
    (hE.norm_proj_le N j) hx

/-- **Quasi-optimality of the mixed method on the cube meshes** ([AFW2010], Thm 3.9): the discrete
solution `(σₕ, uₕ, pₕ)` satisfies, with the constant
`C' = (1 + 144 (2C √(1 + c_P²))²)(1 + 2C)` independent of `N`,
`‖σ - σₕ‖_V + ‖u - uₕ‖_V + ‖p - pₕ‖ ≤ C' (E_V(σ) + E_V(u) + E(p) + μ_N E_V(P_𝔅 u))`. -/
theorem norm_sub_le_infDist {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {cP : ℝ}
    (hPi : ∀ z : ((complex n).d i j).domain, (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈
      ((complex n).cycles i)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤
        cP * ‖(complex n).d i j z‖)
    (hPj : ∀ z : ((complex n).d j k).domain, (z : L2F ℝ (cubeDomain n) (formIdx n j)) ∈
      ((complex n).cycles j)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
        cP * ‖(complex n).d j k z‖)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complex n).domainSpace i}
    {u : (complex n).domainSpace j} {q : (complex n).harmonic j}
    (hs : (complex n).IsMixedSolution i j k f σ u q) (N : ℕ) :
    ‖σ - (whitney n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).fst‖ +
        ‖u - (whitney n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitney n N) hij hjk f).snd.snd :
            (whitney n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + cP ^ 2)) ^ 2) * (1 + 2 * C) *
        (Metric.infDist σ ((whitney n N).domainSub i) + Metric.infDist u ((whitney n N).domainSub j) +
          Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j)) ((whitney n N).harmonicW j) +
          (hE.proj N).harmonicGap j *
            Metric.infDist ((complex n).boundaryPart j ((complex n).domainIncl j u))
              ((whitney n N).domainSub j)) :=
  (hE.proj N).norm_sub_le_infDist_harmonicGap hij hjk hE.one_le_two_mul hPi hPj
    (hE.isGraphBounded_proj N i j) (hE.isGraphBounded_proj N j k) hs

/-- **`O(h)` convergence for solutions approximable at rate `h`**: if the graph-norm distances of
`σ`, `u`, `P_𝔅 u` to the Whitney spaces and the distance of `p` to `ℌₕ` are `≤ K h_N` (for smooth
solutions, the interpolation error of the Whitney interpolant, [Arnold2018], Ch. 7), then the
discrete solutions converge at rate `h`:
`error_N ≤ (1 + 144 (2C √(1 + c_P²))²)(1 + 2C)(4 + 2C) K h_N`. The harmonic gap is bounded by
`1 + 2C` (`norm_sub_π_harmonic_le`). -/
theorem norm_sub_le_meshSize {i j k : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    (hjk : (ComplexShape.up ℤ).Rel j k) {cP : ℝ}
    (hPi : ∀ z : ((complex n).d i j).domain, (z : L2F ℝ (cubeDomain n) (formIdx n i)) ∈
      ((complex n).cycles i)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n i))‖ ≤
        cP * ‖(complex n).d i j z‖)
    (hPj : ∀ z : ((complex n).d j k).domain, (z : L2F ℝ (cubeDomain n) (formIdx n j)) ∈
      ((complex n).cycles j)ᗮ → ‖(z : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
        cP * ‖(complex n).d j k z‖)
    {f : L2F ℝ (cubeDomain n) (formIdx n j)} {σ : (complex n).domainSpace i}
    {u : (complex n).domainSpace j} {q : (complex n).harmonic j}
    (hs : (complex n).IsMixedSolution i j k f σ u q) {K : ℝ} (N : ℕ)
    (hσ : Metric.infDist σ ((whitney n N).domainSub i) ≤ K * meshSize N)
    (hu : Metric.infDist u ((whitney n N).domainSub j) ≤ K * meshSize N)
    (hq : Metric.infDist (q : L2F ℝ (cubeDomain n) (formIdx n j)) ((whitney n N).harmonicW j) ≤
      K * meshSize N)
    (hB : Metric.infDist ((complex n).boundaryPart j ((complex n).domainIncl j u))
      ((whitney n N).domainSub j) ≤ K * meshSize N) :
    ‖σ - (whitney n N).embD i (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).fst‖ +
        ‖u - (whitney n N).embD j (Subcomplex.CochainProjection.discreteMixedSolution
          (whitney n N) hij hjk f).snd.fst‖ +
        ‖(q : L2F ℝ (cubeDomain n) (formIdx n j)) -
          (((Subcomplex.CochainProjection.discreteMixedSolution (whitney n N) hij hjk f).snd.snd :
            (whitney n N).V j) : L2F ℝ (cubeDomain n) (formIdx n j))‖ ≤
      (1 + 144 * (2 * C * √(1 + cP ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) * K * meshSize N := by
  have hμ0 : 0 ≤ 1 + 2 * C := by linarith [hE.two_mul_nonneg]
  have h := (hE.proj N).norm_sub_le_infDist hij hjk hE.one_le_two_mul hμ0 hPi hPj
    (hE.isGraphBounded_proj N i j) (hE.isGraphBounded_proj N j k)
    (fun _ hq' => (hE.proj N).norm_sub_π_harmonic_le hjk hE.two_mul_nonneg
      (hE.isGraphBounded_proj N j k) hq') hs
  refine h.trans ?_
  have hK0 : 0 ≤ (1 + 144 * (2 * C * √(1 + cP ^ 2)) ^ 2) * (1 + 2 * C) := by
    have := hE.two_mul_nonneg; positivity
  have e : (1 + 144 * (2 * C * √(1 + cP ^ 2)) ^ 2) * (1 + 2 * C) * (4 + 2 * C) * K *
      meshSize N = (1 + 144 * (2 * C * √(1 + cP ^ 2)) ^ 2) * (1 + 2 * C) *
        ((4 + 2 * C) * (K * meshSize N)) := by ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ hK0
  have hB' := mul_le_mul_of_nonneg_left hB hμ0
  have e' : (4 + 2 * C) * (K * meshSize N) =
      3 * (K * meshSize N) + (1 + 2 * C) * (K * meshSize N) := by ring
  rw [e']
  linarith

/-- **The harmonic gap tends to zero** on the cube meshes, provided the harmonic forms of `HΛʲ(Q)`
are finite-dimensional and approximated by the Whitney spaces (`dist(q, Vₕ) → 0`). -/
theorem tendsto_harmonicGap {j : ℤ} [FiniteDimensional ℝ ((complex n).harmonic j)]
    (happrox : ∀ q ∈ (complex n).harmonic j,
      Tendsto (fun N => Metric.infDist q ((whitney n N).V j :
        Set (L2F ℝ (cubeDomain n) (formIdx n j)))) atTop (𝓝 0)) :
    Tendsto (fun N => (hE.proj N).harmonicGap j) atTop (𝓝 0) :=
  Subcomplex.CochainProjection.tendsto_harmonicGap hE.proj hE.two_mul_nonneg
    (fun N x => hE.norm_proj_le N j x) happrox

end SmoothingEstimates

/-! ## The Hodge wave equation and Maxwell's equations on the cube meshes -/

instance (N : ℕ) (a : ℤ) (m : ℕ) (i : Fin m) :
    FiniteDimensional ℝ (((whitney n N).window a m).V i) :=
  inferInstanceAs (FiniteDimensional ℝ ((whitney n N).V (a + i)))

instance (N : ℕ) (a : ℤ) (m : ℕ) : FiniteDimensional ℝ ((whitney n N).window a m).graphSub :=
  inferInstance

/-- **The Whitney windows are approximating** (for the semi-discrete Hodge wave equation of the
window `HΛᵃ(Q) → ⋯ → HΛ^{a+m-1}(Q)`) as soon as they approximate every point of the graph space
of the total differential; the uniform bound of the elliptic projections holds for every
subcomplex (`Feec.HilbertComplex.Subcomplex.norm_ellipticProjection_le`). -/
theorem isApproximating_window (a : ℤ) (m : ℕ)
    (hd : ∀ ζ : ((complex n).window a m).totalD.GraphSpace, ∀ δ > 0, ∀ᶠ N in atTop,
      ∃ w ∈ ((whitney n N).window a m).graphSub, ‖ζ - w‖ < δ) :
    HodgeWave.IsApproximating atTop fun N => ((whitney n N).window a m).graphSub :=
  Subcomplex.isApproximating hd

/-- **Convergence of the semi-discrete Hodge wave equation on the cube meshes** for `D(L)` data
(`L` the Hodge wave operator of the window): the semi-discrete Whitney solutions with
`ξₕ(t₀) = Pₕ x` converge to `e^{(t - t₀) L} x` uniformly on `[t₀, t₁]`. See
[QuennevilleBelair2015], Thm 4.14; the error bound for each `N` is
`Feec.HodgeWave.norm_sub_le_of_semidiscrete`. -/
theorem exists_tendstoUniformlyOn_window (a : ℤ) (m : ℕ)
    (hd : ∀ ζ : ((complex n).window a m).totalD.GraphSpace, ∀ δ > 0, ∀ᶠ N in atTop,
      ∃ w ∈ ((whitney n N).window a m).graphSub, ‖ζ - w‖ < δ)
    (t₀ t₁ : ℝ) (x : ((complex n).window a m).wave.domain) :
    ∃ ξh ξh' : ℕ → ℝ → ((complex n).window a m).totalD.GraphSpace,
      (∀ N, HodgeWave.IsSemidiscreteSolution (((whitney n N).window a m).graphSub)
        (Set.Icc t₀ t₁) (ξh N) (ξh' N)) ∧
      (∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((whitney n N).window a m).graphSub)
        (((complex n).window a m).totalD.toGraphSpace
          ⟨x, (((complex n).window a m).mem_wave_domain.1 x.2).1⟩)) ∧
      TendstoUniformlyOn (fun N t => ((complex n).window a m).totalD.graphFst (ξh N t))
        (fun t => ((complex n).window a m).waveGroup.S (t - t₀) x) atTop (Set.Icc t₀ t₁) :=
  HilbertComplex.HodgeWave.exists_tendstoUniformlyOn_ellipticProjection _
    (isApproximating_window n a m hd) t₀ t₁ x

/-- **`O(h)` error of the semi-discrete Hodge wave equation on the cube meshes**
([QuennevilleBelair2015], Thm 4.14; rate as in [Arnold2018], Ch. 7): for a weak solution `ξ` in
`C¹([t₀, t₁]; Γ(𝐝))` of the Hodge wave equation of the window and the semi-discrete Whitney
solutions `ξₕ` started at `Pₕ ξ(t₀)`, if `ξ(s)` and `ξ'(s)` are approximated in the graph norm by
the Whitney window to order `K h_N` on `[t₀, t₁]` (for smooth solutions, the interpolation error
of the Whitney interpolant), then `‖ξ(t) - ξₕ(t)‖ ≤ A (1 + (t - t₀))² K h_N` with `A` independent
of `N` (`Feec.HilbertComplex.Subcomplex.norm_sub_le_of_approx`). -/
theorem norm_sub_le_meshSize_window (a : ℤ) (m : ℕ) {t₀ t₁ : ℝ}
    {ξ ξ' : ℝ → ((complex n).window a m).totalD.GraphSpace}
    (hξ : HodgeWave.IsGraphSolution (Set.Icc t₀ t₁) ξ ξ')
    {ξh ξh' : ℕ → ℝ → ((complex n).window a m).totalD.GraphSpace}
    (hξh : ∀ N, HodgeWave.IsSemidiscreteSolution (((whitney n N).window a m).graphSub)
      (Set.Icc t₀ t₁) (ξh N) (ξh' N))
    (h0 : ∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((whitney n N).window a m).graphSub) (ξ t₀))
    {K : ℝ}
    (happ : ∀ N, ∀ s ∈ Set.Icc t₀ t₁,
      (∃ w ∈ ((whitney n N).window a m).graphSub, ‖ξ s - w‖ ≤ K * meshSize N) ∧
      (∃ w ∈ ((whitney n N).window a m).graphSub, ‖ξ' s - w‖ ≤ K * meshSize N))
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    ‖((complex n).window a m).totalD.graphFst (ξ t - ξh N t)‖ ≤
      (1 + ‖HodgeWave.shiftedForm ((complex n).window a m).totalD‖ / ((1 / 2) / √3)) *
        (1 + (t - t₀)) ^ 2 * (K * meshSize N) :=
  ((whitney n N).window a m).norm_sub_le_of_approx hξ (hξh N) (h0 N) (happ N) ht

/-- **Maxwell's equations on cube meshes** (perfect magnetic conductor): for `n = 3` the window
`HΛ⁰(Q) → HΛ¹(Q) → L²Λ²(Q)` is the PMC Maxwell complex `H¹ → H(curl) → L²` in form coordinates
(`Feec.Maxwell.maximalComplex_d_eq_pmcForms_d₀`, `_d₁`), discretized by Lagrange `P₁` and
Nédélec edge elements and Raviart–Thomas face elements (as `2`-forms) on the Freudenthal meshes;
the semi-discrete solutions converge for `D(L)` data. -/
theorem maxwell_exists_tendstoUniformlyOn
    (hd : ∀ ζ : ((complex 3).window 0 3).totalD.GraphSpace, ∀ δ > 0, ∀ᶠ N in atTop,
      ∃ w ∈ ((whitney 3 N).window 0 3).graphSub, ‖ζ - w‖ < δ)
    (t₀ t₁ : ℝ) (x : ((complex 3).window 0 3).wave.domain) :
    ∃ ξh ξh' : ℕ → ℝ → ((complex 3).window 0 3).totalD.GraphSpace,
      (∀ N, HodgeWave.IsSemidiscreteSolution (((whitney 3 N).window 0 3).graphSub)
        (Set.Icc t₀ t₁) (ξh N) (ξh' N)) ∧
      (∀ N, ξh N t₀ = HodgeWave.ellipticProjection (((whitney 3 N).window 0 3).graphSub)
        (((complex 3).window 0 3).totalD.toGraphSpace
          ⟨x, (((complex 3).window 0 3).mem_wave_domain.1 x.2).1⟩)) ∧
      TendstoUniformlyOn (fun N t => ((complex 3).window 0 3).totalD.graphFst (ξh N t))
        (fun t => ((complex 3).window 0 3).waveGroup.S (t - t₀) x) atTop (Set.Icc t₀ t₁) :=
  exists_tendstoUniformlyOn_window 3 0 3 hd t₀ t₁ x

end Feec.Models.Cube.FEM
