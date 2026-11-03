module

public import Feec.FiniteElement.SmoothedProjection
public import Feec.FiniteElement.WhitneyComplex
public import Feec.Domain.StarShapedSmoothing
public import Feec.HilbertComplex.Approximation.Convergence
public import Feec.HilbertComplex.Approximation.ConformingFamily

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
**estimates of [AFW2010], §5.5 and [ChristiansenWinther2008]** for these maps (uniform `L²`
bound `C` and `‖v - Q_N v‖ ≤ ½ ‖v‖` on `Vₕ`; the structure `FEM.SmoothingEstimates`, taken as a
hypothesis here and proved for explicit parameters in `Feec.Models.Cube.SmoothingEstimates`):

* uniformly bounded cochain projections `π_N` with `‖π_N‖ ≤ 2C` in `L²`
  (`SmoothingEstimates.proj`, `SmoothingEstimates.norm_proj_le`), hence in every graph norm
  (`Subcomplex.CochainProjection.isGraphBounded_of_norm_le`); with the density of the Whitney
  spaces they make the Whitney complexes a conforming family (`SmoothingEstimates.family` in
  `Feec.Models.Cube.FiniteElementConvergence`), to which the static FEEC theorem
  (`Feec.HilbertComplex.ConformingFamily.staticFEEC`: discrete Poincaré inequality,
  well-posedness, quasi-optimality, harmonic gap, cohomology, convergence) applies;
* for the Hodge wave equation of any window, the Whitney windows are approximating as soon as they
  are dense (`FEM.isApproximating_window`), hence convergence of the semi-discrete solutions
  (`FEM.exists_tendstoUniformlyOn_window`), and the rate `‖ξ(t) - ξₕ(t)‖ ≤ A (1 + t - t₀)² K h_N`
  when the solution and its time derivative are approximable at rate `h`
  (`FEM.norm_sub_le_meshSize_window`, from `Feec.HodgeWave.norm_sub_le_of_semidiscrete`, which needs
  no smoothed projection); **Maxwell's equations** (perfect
  magnetic conductor, `n = 3`, window `HΛ⁰ → HΛ¹ → L²Λ²`) are the instance `a = 0`, `m = 3`.

**Remaining hypotheses.** None for the cube: the three hypotheses of this module are theorems
elsewhere, and `Feec.Models.Cube.FiniteElementConvergence` states the results without them.
(1) `FEM.SmoothingEstimates` and `FEM.SmoothingEstimatesMin` hold for explicit parameters
(`FEM.smoothingEstimates_pMax`, `FEM.smoothingEstimatesMin_pMin` in
`Feec.Models.Cube.SmoothingEstimates`, from the inverse estimates of
`Feec.FiniteElement.InverseEstimate`); (2) the Poincaré inequalities of `HΛ(Q)` and `H̊Λ(Q)` hold
with `c_P = (2π)⁻¹` (`FEM.norm_le_of_mem_orthogonal_cycles`, `_min` in
`Feec.Models.Cube.DeRhamIdentFEM`, from the identification of `HΛ(Q)`, `H̊Λ(Q)` with the parity
classes of the torus complex, `Feec.Models.Cube.DeRhamIdent`); (3) the Whitney spaces approximate
at rate `h` for `C²` forms and are dense (`Feec.Models.Cube.WhitneyApprox`,
`Feec.Models.Cube.WhitneyRate`, from `Feec.FiniteElement.WhitneyInterpolation`). The statements of
this module keep (1) as a hypothesis so that they apply to any parameters and constants. For the
Einstein–Bianchi (BGG) system, `Feec.BGG.Discrete` needs subcomplexes of
both rows with cochain projections satisfying `Π S = S_h Π'`; vector-valued Whitney forms and such
a pair of projections are not constructed, so that structure remains an explicit hypothesis of
`Feec.HilbertComplex.BGG.Discrete`.

**The vanishing-trace family.** For minimal-family parameters (`c > 1`, dilation towards the
centre) the smoothed form is a test form on `Ω` (`smoothForm_eq_zero_of_minimal`), so its
canonical interpolant has vanishing boundary DOFs (`LocalElement.globalInterp_mem_globalSpace₀`),
and `d` of it is the smoothed form of `d_min u` everywhere (`extDeriv_smoothForm_of_minimal`):
`LocalElement.smoothedCommutingMapMin` is a commuting map into `V̊ₕ ⊆ H̊Λ(Ω)`. On the cube this
gives `FEM.whitneyMin`, `FEM.smoothedMin` and, under the analogous explicit estimates
`FEM.SmoothingEstimatesMin`, uniformly bounded cochain projections onto `V̊ₕ`
(`SmoothingEstimatesMin.proj`, `SmoothingEstimatesMin.norm_proj_le`; the conforming family
`SmoothingEstimatesMin.family`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §5.5 (smoothed projections), Thm 3.6, Thm 3.8, Thm 3.9
* [S. H. Christiansen, R. Winther, *Smoothed projections in finite element exterior calculus*][ChristiansenWinther2008]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §5 (canonical interpolants, Whitney forms)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (bounded commuting
  projections, approximation)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 4.14 (convergence of the semi-discrete Hodge wave equation)

Bibliography: [references.bib](../../../docs/references.bib)
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

/-- **`d` of the smoothed form is the smoothed form of `d_min u`** everywhere on `ℝⁿ` (any
parameters): the zero extension of `u ∈ D(d_min)` has distributional `d` equal to the zero
extension of `d_min u` (`Feec.Domain.apply_smoothExt_of_minimal`). -/
theorem extDeriv_smoothForm_of_minimal (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω) (k : ℕ)
    (u : ((extDerivOp ℝ n k).minimal Ω).domain) (x : Fin n → ℝ) :
    extDeriv (smoothForm p hΩ k u : FormField n) x =
      (smoothForm p hΩ ((k : ℤ) + 1) ((extDerivOp ℝ n k).minimal Ω u) : FormField n) x := by
  funext t
  by_cases ht : (#t : ℤ) = (k : ℤ) + 1
  · have h1 := extDerivOp_apply_formComp (isDeg_smoothForm p hΩ k (u : L2F ℝ Ω (formIdx n k)))
      ⟨t, ht⟩ x
    rw [formComp_smoothForm] at h1
    rw [← h1, apply_smoothExt_of_minimal (p := p) hΩo (extDerivOp_isRowHomogeneous k) u _ _ x,
      smoothForm_apply, formExt_of_card _ ht]
    change _ = p.factor ^ ((k : ℤ) + 1) * _
    rw [pow_one, zpow_add_one₀ p.factor_pos.ne']
  · have h0 := IsDeg.extDeriv (isDeg_smoothForm p hΩ k (u : L2F ℝ Ω (formIdx n k))) x t
      (fun h => ht (by exact_mod_cast h))
    rw [h0, smoothForm_apply]
    simp [formExt, ht]

/-- **Minimal family: the smoothed form vanishes outside `Ω`** (it is a test form on `Ω`,
`Feec.Domain.isTest_smoothExt`). -/
theorem smoothForm_eq_zero_of_minimal (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : Fin n → ℝ} {s₀ : ℝ} (hstar : ∀ y ∈ Ω, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ Ω)
    (hp : p.IsMinimal x₀ s₀) (k : ℤ) (u : L2F ℝ Ω (formIdx n k)) {x : Fin n → ℝ} (hx : x ∉ Ω) :
    (smoothForm p hΩ.measurableSet k u : FormField n) x = 0 := by
  funext t
  rw [smoothForm_apply]
  unfold formExt
  split_ifs with h
  · change p.factor ^ k * smoothExt Ω p ((u ⟨t, h⟩ : L2 ℝ Ω) : (Fin n → ℝ) → ℝ) x = 0
    rw [image_eq_zero_of_notMem_tsupport fun hx' => hx ((isTest_smoothExt hb hstar hp
      ((memLp_indicator hΩ.measurableSet _).locallyIntegrable (by norm_num))).tsupport_subset hx'),
      mul_zero]
  · rfl

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
interpolant of the smoothed form ([AFW2010], §5.5); zero in negative degrees. -/
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

/-! ### The vanishing-trace family -/

/-- A point of the boundary `∂(cl Ω)` is not in the open set `Ω`. -/
theorem _root_.Feec.Mesh.SimplicialMesh.notMem_domain_of_mem_frontier (hΩo : IsOpen M.domain)
    {x : Fin n → ℝ} (hx : x ∈ frontier (closure M.domain)) : x ∉ M.domain := fun hxΩ =>
  hx.2 (interior_maximal subset_closure hΩo hxΩ)

/-- **`Π_h` of a form vanishing on `∂(cl Ω)` has vanishing boundary DOFs**: the DOFs of a face
in a boundary facet see only the traces there (`dof_congr`). -/
theorem globalInterp_mem_globalSpace₀ (k : ℕ) {w : contForms n}
    (h : ∀ x ∈ frontier (closure M.domain), (w : FormField n) x = 0) :
    (E.globalInterp M k w : E.Piecewise M k) ∈ E.globalSpace₀ M k := by
  refine ⟨(E.globalInterp M k w).2, fun T F hF hFT g hg i => ?_⟩
  rw [localDof_globalInterp _ _ _ _ _ _ (hg.trans hFT)]
  have h0 : E.dof g k i w = E.dof g k i 0 := E.dof_congr i fun x hx V _ => by
    rw [h x (hF.2.2 (convexHull_mono (Finset.coe_subset.2 hg) hx))]
    rfl
  rw [h0, map_zero]

/-- **Minimal family: `Q = Π_h R` has vanishing boundary DOFs**, `Q u ∈ V̊ₕ`. -/
theorem smoothedInterp_mem_V₀ (hΩo : IsOpen M.domain) (hb : Bornology.IsBounded M.domain)
    {x₀ : Fin n → ℝ} {s₀ : ℝ}
    (hstar : ∀ y ∈ M.domain, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ M.domain)
    (hp : p.IsMinimal x₀ s₀) (k : ℤ) (u : L2F ℝ M.domain (formIdx n k)) :
    E.smoothedInterp M p hΩo.measurableSet k u ∈ E.V₀ M k := by
  rcases k with k | k
  · exact ⟨⟨_, E.globalInterp_mem_globalSpace₀ M k fun x hx =>
      smoothForm_eq_zero_of_minimal p hΩo hb hstar hp k u (M.notMem_domain_of_mem_frontier hΩo hx)⟩,
      rfl⟩
  · exact Submodule.zero_mem _

/-- **`d_min Q u = Q d_min u`** (minimal family): as `maximal_smoothedInterp`, with the smoother
commuting with `d_min` everywhere (`extDeriv_smoothForm_of_minimal`) and `Q u ∈ V̊ₕ ⊆ D(d_min)`. -/
theorem minimal_smoothedInterp [NeZero n] (hΩo : IsOpen M.domain)
    (hb : Bornology.IsBounded M.domain) {x₀ : Fin n → ℝ} {s₀ : ℝ}
    (hstar : ∀ y ∈ M.domain, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ M.domain)
    (hp : p.IsMinimal x₀ s₀) (y₀ : Fin n → ℝ)
    (hstar' : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → y₀ + t • (x - y₀) ∈ M.domain)
    (k : ℕ) (u : ((extDerivOp ℝ n k).minimal M.domain).domain) :
    ∃ h : E.smoothedInterp M p hΩo.measurableSet k u ∈
        ((extDerivOp ℝ n k).minimal M.domain).domain,
      (extDerivOp ℝ n k).minimal M.domain ⟨_, h⟩ =
        E.smoothedInterp M p hΩo.measurableSet ((k : ℤ) + 1)
          ((extDerivOp ℝ n k).minimal M.domain u) := by
  set w := smoothForm p hΩo.measurableSet k (u : L2F ℝ M.domain (formIdx n k))
  have hw : (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w) : E.Piecewise M k) ∈
      E.globalSpace₀ M k := E.globalInterp_mem_globalSpace₀ M k fun x hx =>
    smoothForm_eq_zero_of_minimal p hΩo hb hstar hp k _ (M.notMem_domain_of_mem_frontier hΩo hx)
  obtain ⟨h, hval⟩ := E.glue_mem_minimal M hΩo y₀ hstar' k ⟨_, hw⟩
  refine ⟨h, hval.trans ?_⟩
  have h1 : E.dPiecewise M k
      (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w) : E.Piecewise M k) =
      (E.dGlobal M k (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w)) :
        E.Piecewise M (k + 1)) := rfl
  change E.glue M ((k : ℤ) + 1) (E.dPiecewise M k
    (E.globalInterp M k (Submodule.inclusion c1Forms_le_contForms w) : E.Piecewise M k)) = _
  rw [h1, ← globalInterp_extDeriv]
  have h2 : E.globalInterp M (k + 1) (extDerivC1 w) = E.globalInterp M (k + 1)
      (Submodule.inclusion c1Forms_le_contForms
        (smoothForm p hΩo.measurableSet ((k + 1 : ℕ) : ℤ)
          ((extDerivOp ℝ n k).minimal M.domain u))) :=
    E.globalInterp_congr M (k + 1) fun x _ =>
      extDeriv_smoothForm_of_minimal p hΩo.measurableSet hΩo k u x
  rw [h2]
  rfl

/-- **The smoothed canonical interpolant as a commuting map** into the finite element subcomplex
with vanishing boundary DOFs `V̊ₕ ⊆ H̊Λ(Ω)` (minimal family, `Ω` bounded, star-shaped with respect
to `B(x₀, s₀)` and strictly star-shaped with respect to `y₀`): `d Q = Q d` in every degree. -/
def smoothedCommutingMapMin [NeZero n] (hΩo : IsOpen M.domain)
    (hb : Bornology.IsBounded M.domain) {x₀ : Fin n → ℝ} {s₀ : ℝ}
    (hstar : ∀ y ∈ M.domain, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ M.domain)
    (hp : p.IsMinimal x₀ s₀) (y₀ : Fin n → ℝ)
    (hstar' : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → y₀ + t • (x - y₀) ∈ M.domain) :
    (E.subcomplexMin M hΩo y₀ hstar').CommutingMap where
  Q := E.smoothedInterp M p hΩo.measurableSet
  mem i x := E.smoothedInterp_mem_V₀ M p hΩo hb hstar hp i x
  comm i j x := by
    by_cases hij : i + 1 = j
    · subst hij
      have hd := deRham_minimalComplex_d (𝕜 := ℝ) (n := n) hΩo i
      rcases i with k | k
      · rw [LinearPMap.apply_eq_of_eq' hd, LinearPMap.apply_eq_of_eq' hd x]
        obtain ⟨h, hv⟩ := E.minimal_smoothedInterp M p hΩo hb hstar hp y₀ hstar' k
          ⟨x.1, hd ▸ x.2⟩
        exact hv
      · have h0 : ∀ y : (((deRham ℝ n).minimalComplex hΩo).d (Int.negSucc k)
            (Int.negSucc k + 1)).domain, ((deRham ℝ n).minimalComplex hΩo).d _ _ y = 0 := by
          intro y
          have : y = 0 := Subtype.ext ((subsingleton_L2F_negSucc M.domain k).elim _ _)
          rw [this, LinearPMap.map_zero]
        rw [h0, h0]
        exact (E.smoothedInterp M p hΩo.measurableSet _).map_zero.symm
    · rw [HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hij),
        HilbertComplex.apply_eq_zero_of_not_rel _ (by simpa using hij)]
      exact (E.smoothedInterp M p hΩo.measurableSet j).map_zero.symm

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

/-- A subcomplex of the minimal complex on `Ω`, as a subcomplex of the minimal complex on
`Ω' = Ω`. -/
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

end Feec.Domain.ConstCoeffComplex

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

/-- **The estimates of the smoothed canonical interpolants** ([AFW2010], §5.5;
[ChristiansenWinther2008]): for maximal-family smoothing parameters `p N` (any
`IsMaximal` parameters; the structure imposes no scaling), the smoothed interpolants
`Q_N = Π_h R` of the Whitney complexes are bounded in `L²` uniformly in `N`, and close to the
identity on `Vₕ`: `‖v - Q_N v‖ ≤ ½ ‖v‖`. In the references these are obtained with the scaling
factor `1 - δ h_N`, bump radius `≈ δ h_N` and `δ` small, from elementwise inverse estimates for
polynomials and the interpolation error of `Π_h` on smoothed fields. They are the hypotheses of
this section, so that its results apply to any parameters; for the parameters `FEM.pMax γ` they
are proved in `Feec.Models.Cube.SmoothingEstimates` (`FEM.smoothingEstimates_pMax`,
`FEM.smoothingEstimates_exists`). The maps `Q_N` themselves are the
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

variable (hE : SmoothingEstimates n p C)
include hE

/-- **Uniform `L²` bound**: `‖π_N x‖ ≤ 2 C ‖x‖` for every `N`. -/
theorem norm_proj_le (N : ℕ) (i : ℤ) (x : L2F ℝ (cubeDomain n) (formIdx n i)) :
    ‖(hE.proj N).π i x‖ ≤ 2 * C * ‖x‖ :=
  (smoothed n N (p N) (hE.isMaximal N)).norm_toCochainProjection_le_two_mul (hE.close N)
    (hE.bound N i) x

end SmoothingEstimates

/-! ## The vanishing-trace family `H̊Λ(Q)` -/

/-- The minimal `L²` de Rham complex `H̊Λ(Q)` of the cube (vanishing tangential traces). -/
abbrev complexMin : HilbertComplex ℝ (ComplexShape.up ℤ) fun k => L2F ℝ (cubeDomain n) (formIdx n k) :=
  (deRham ℝ n).minimalComplex (isOpen_cubeDomain n)

omit [NeZero n] in
theorem isBounded_cubeDomain : Bornology.IsBounded (cubeDomain n) :=
  Bornology.IsBounded.pi fun _ => Metric.isBounded_Ioo _ _

omit [NeZero n] in
theorem center_mem_cubeDomain : center n ∈ cubeDomain n := fun i _ => by
  simp only [center, Set.mem_Ioo]; norm_num

omit [NeZero n] in
theorem strictStar_mesh (N : ℕ) : ∀ x ∈ closure (mesh n N).domain, ∀ t : ℝ, 0 ≤ t → t < 1 →
    center n + t • (x - center n) ∈ (mesh n N).domain := by
  rw [mesh_domain]
  exact add_smul_sub_mem_of_convex (isOpen_cubeDomain n) (convex_cubeDomain n)
    (center_mem_cubeDomain n)

/-- **The Whitney complex with vanishing boundary DOFs** of the level-`(N + 1)` Freudenthal mesh,
as a subcomplex of `H̊Λ(Q)`. -/
def whitneyMin (N : ℕ) : (complexMin n).Subcomplex :=
  (deRham ℝ n).minimalSubcomplexOfEq (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n)
    (whitneySubcomplexMin (mesh n N) (isOpen_mesh_domain n N) (center n) (strictStar_mesh n N))

instance (N : ℕ) (k : ℤ) : FiniteDimensional ℝ ((whitneyMin n N).V k) :=
  (deRham ℝ n).finiteDimensional_minimalSubcomplexOfEq _ _ _ _ k

/-- **The smoothed canonical interpolant with vanishing boundary DOFs** `Q̊_N = Π_h R` on the
Freudenthal Whitney complex of `H̊Λ(Q)`, for minimal-family smoothing parameters (dilation
towards the centre, `c > 1`): `R u` is a test form on `Q`, so `Q̊_N u ∈ V̊ₕ`, and `d Q̊_N = Q̊_N d`. -/
def smoothedMin (N : ℕ) (p : SmoothingParam (Fin n → ℝ)) (hp : p.IsMinimal (center n) (1 / 4)) :
    (whitneyMin n N).CommutingMap :=
  (deRham ℝ n).commutingMapOfEqMin (mesh_domain n N) (isOpen_mesh_domain n N)
    (isOpen_cubeDomain n)
    ((whitneyElement n).smoothedCommutingMapMin (mesh n N) p (isOpen_mesh_domain n N)
      (mesh_domain n N ▸ isBounded_cubeDomain n) (starBall_mesh n N) hp (center n)
      (strictStar_mesh n N))

/-- **The estimates of the smoothed interpolants with vanishing boundary DOFs** ([AFW2010],
§5.5, [ChristiansenWinther2008]; a hypothesis of the results below, as `SmoothingEstimates`,
proved for the parameters `FEM.pMin γ` in `Feec.Models.Cube.SmoothingEstimates`,
`FEM.smoothingEstimatesMin_pMin`): for minimal-family parameters `p N`, uniform `L²` bounds of
`Q̊_N` and `‖v - Q̊_N v‖ ≤ ½ ‖v‖` on `V̊ₕ`; normalized by `½ ≤ C`. -/
structure SmoothingEstimatesMin (p : ℕ → SmoothingParam (Fin n → ℝ)) (C : ℝ) : Prop where
  isMinimal : ∀ N, (p N).IsMinimal (center n) (1 / 4)
  half_le : 1 / 2 ≤ C
  bound : ∀ N i x, ‖(smoothedMin n N (p N) (isMinimal N)).Q i x‖ ≤ C * ‖x‖
  close : ∀ N i, ∀ v ∈ (whitneyMin n N).V i,
    ‖v - (smoothedMin n N (p N) (isMinimal N)).Q i v‖ ≤ 1 / 2 * ‖v‖

namespace SmoothingEstimatesMin

variable {n} {p : ℕ → SmoothingParam (Fin n → ℝ)} {C : ℝ}

/-- **The smoothed projection** `π̊_N = J_N⁻¹ Q̊_N` onto the Whitney complex of `H̊Λ(Q)`. -/
def proj (hE : SmoothingEstimatesMin n p C) (N : ℕ) : (whitneyMin n N).CochainProjection :=
  (smoothedMin n N (p N) (hE.isMinimal N)).toCochainProjection (θ := 1 / 2) (by norm_num)
    (hE.close N)

theorem two_mul_nonneg (hE : SmoothingEstimatesMin n p C) : 0 ≤ 2 * C := by
  linarith [hE.half_le]

variable (hE : SmoothingEstimatesMin n p C)
include hE

/-- **Uniform `L²` bound** `‖π̊_N x‖ ≤ 2 C ‖x‖`. -/
theorem norm_proj_le (N : ℕ) (i : ℤ) (x : L2F ℝ (cubeDomain n) (formIdx n i)) :
    ‖(hE.proj N).π i x‖ ≤ 2 * C * ‖x‖ :=
  (smoothedMin n N (p N) (hE.isMinimal N)).norm_toCochainProjection_le_two_mul (hE.close N)
    (hE.bound N i) x

end SmoothingEstimatesMin

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

end Feec.Models.Cube.FEM
