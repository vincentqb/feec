module

public import Feec.HilbertComplex.Approximation.ConstrainedFEEC
public import Feec.HilbertComplex.Approximation.ApproxConforming
public import Feec.Physics.Maxwell.CubeFEM
public import Feec.Physics.Maxwell.Constraints
public import Feec.Models.Torus.DeRhamGalerkin
public import Feec.Models.StarShaped.FiniteElement

/-!
# Maxwell's equations as instances of the constrained FEEC theorem

Maxwell's equations are the Hodge wave equation of a window `V a → V (a+1) → V (a+2)` of a
Hilbert complex, with the **Gauss laws** `σ = 0`, `d†E = 0`, `dB = 0` as constraint
(`Feec.Physics.Maxwell.Constraints`). This module makes them instances of the constrained FEEC
theorem `Feec.HilbertComplex.constrainedFEEC`.

* **The Gauss laws of a short complex.** For a Hilbert complex `H` on `ComplexShape.fin3` and a
  closed `Y ⊇ R(d₁)`, `gauss H Y = {0} × N(d₀†) × Y` (`mem_gauss`) is a reducing subcomplex
  (`reducingSubcomplex_gaussFam`), so it reduces the wave operator (`isReducing_gauss`). For a
  window of a complex on `ComplexShape.up α` (`α = ℕ, ℤ`), `windowGauss H a` takes for `Y` the
  magnetic Gauss law `N(d : V (a+2) → V (a+3))` (`magnetic`, `isReducing_windowGauss`).
* **Maxwell discretizations.** `feec H a l S P hP hS` is the constrained FEEC discretization of
  the window `H.window a 3` with constraint `windowGauss H a`, built from a family of
  finite-dimensional subcomplexes `S h` of `H` (windowed by `subWindow`), cochain projections
  `P h` (windowed by `projWindow`) bounded uniformly in `L²`, and degreewise `L²` density of the
  `S h` (`dense_of_forall` gives the approximation property of the total space).
  `regRate` is the rate class of data whose orbit and derivative have degreewise regularity
  `Reg` on `[0, T]`, under a degreewise approximation estimate `‖x - v‖, ‖d (x - v)‖ ≤ B Λ r_h`
  (`exists_mem_subWindow_le`).
* **The four headline statements for every Maxwell discretization**, each a one-line application
  of the constrained FEEC theorem: `wellPosed`, `gauss_propagates` (and
  `gauss_propagates_strong`; with no discretization, `windowGauss_propagates`,
  `windowGauss_propagates_strong`), `converges`, `rate`, `residual`, `residual_rate`; for any other
  closed constraint (`withConstraint`, same discrete solutions `discrete_withConstraint`),
  `residual_not_isReducing` (`K` or `Kᗮ`, forward in time), `residual_not_isReducing_symm` (data
  in `D(L) ∩ K`, `t ∈ [-T, T]`) and `residual_not_isReducing_of_grading` (data in `D(L) ∩ K`,
  forward in time, with the discrete residuals).
* **A non-reducing Maxwell constraint.** The vanishing-field constraint `potential 𝕜 W`
  (`E = 0`, `B = 0`; `mem_potential`) of a complex on `ComplexShape.fin3` does not reduce `L` as
  soon as `d₀ ≠ 0` (`not_isReducing_potential`, since `L (σ, 0, 0) = (0, dσ, 0)`), and `D(L) ∩ K`
  is dense in it (`dense_potential`). `potential_residual` is the non-reducing branch of item 4
  for it, for every constrained FEEC discretization: data in `D(L) ∩ K` leave `K` forward in time,
  and the discrete residuals tend to a positive limit.

**Through the approximating FEEC theorem.** Every Maxwell discretization is an instance of
`Feec.HilbertComplex.approxFEEC` (the special case `ιₕ` = inclusion, `πₕ = Pₕ`,
`ConstrainedFEEC.toApprox`, core `D(L²)`): `feec_approxFEEC`, and per instance
`torus_approxFEEC`, `torus_potential_approxFEEC` (with the non-reducing vanishing-field
constraint; `torus_potential_residual_of_approxFEEC` reads the graded item 4c off it),
`cubePMC_approxFEEC`, `cubePEC_approxFEEC`,
`paraPMC_approxFEEC`, `paraPEC_approxFEEC`, `starPMC_approxFEEC`, `starPEC_approxFEEC`. The rate
of the approximating theorem gives the conforming factor `(1 + C_P)(1 + 2t)` in place of the
`(1 + t)²` of `constrainedFEEC_rate` (`approx_rate`, `approx_residual_rate`,
`approx_rate_regRate`, `approx_residual_rate_regRate`, and `cubePMC_approx_rate`, …,
`starPEC_approx_residual_rate`).

The evolution statements above (`gauss_propagates`, `converges`, `rate`, `residual`,
`residual_rate`, `residual_not_isReducing*`, and the per-instance `*_converges`, `*_residual`,
`*_gauss_propagates`, `*_tendstoUniformlyOn`, `torus_potential_residual`) are projections of
`ConstrainedFEEC.constrainedFEEC_of_approxFEEC`, the statement of `constrainedFEEC` derived from
`approxFEEC`; so they depend on the approximating theorem, not on the original proof of
`constrainedFEEC`. Well-posedness is item 1 of both theorems (`constrainedFEEC_wellPosed`); the
propagation along strong solutions (`gauss_propagates_strong`) and the discrete Poincaré
inequalities (`*_discretePoincare`) are not items of either theorem and keep their direct
proofs.

## Instances

* **The torus `𝕋ᵈ`** (any `d`, any degree `a`; `d = 3`, `a = 0` is the classical system), with
  the spectral Galerkin spaces of band-limited forms `|n|_∞ ≤ N` and the Fourier truncations
  (`torus`; `torus_gauss_propagates`, `torus_converges`, `torus_residual`). The gradient of `𝕋ᵈ`
  is not zero (`torus_exists_d_ne_zero`), so the vanishing-field constraint is not reducing
  (`torus_not_isReducing_potential`) and is violated, also by the spectral Galerkin solutions
  (`torus_potential_residual`).
* **The cube `Q = (0, ½)ⁿ`** with the lowest-order Whitney forms of the Freudenthal meshes and
  the smoothed projections, for the **perfect magnetic conductor** (`cubePMC`, the maximal complex
  `HΛ(Q)`) and the **perfect electric conductor** (`cubePEC`, the minimal complex `H̊Λ(Q)`,
  vanishing boundary DOFs); for `n = 3`, `a = 0` these are the Maxwell systems of
  `Feec.Maxwell.CubeFEM`. The `O(h)` rate classes of `C²` solutions (`cubePMCRate`,
  `cubePECRate`; non-vacuity `zero_mem_cubePMCRate`, `zero_mem_cubePECRate`) give `cubePMC_rate`,
  `cubePMC_residual_rate`, `cubePEC_rate`, `cubePEC_residual_rate`. The convergence theorems
  `Feec.Maxwell.CubeFEM.pmc_tendstoUniformlyOn`, `pec_tendstoUniformlyOn` (at `t₀ = 0`) are
  recovered from the constrained FEEC theorem (`cubePMC_tendstoUniformlyOn`,
  `cubePEC_tendstoUniformlyOn`).
* **Parallelepipeds `Ω = A · Q + b`** (every box), with the image Freudenthal meshes, both boundary
  conditions (`paraPMC`, `paraPEC`, `paraPMCRate`, `paraPECRate`).
* **Domains star-shaped with respect to a ball**, with any uniformly shape-regular and
  quasi-uniform mesh family, both boundary conditions (`starPMC`, `starPEC`, `starPMCRate`,
  `starPECRate`). The Poincaré inequality (`StarShaped.HasPoincare`) is needed only for the uniform
  discrete Poincaré inequality (`starPMC_discretePoincare`, `starPEC_discretePoincare`).
* **Unconditional discrete Poincaré inequalities**, from the proved Poincaré inequalities of the
  cube and the parallelepipeds: `cubePMC_discretePoincare`, `cubePEC_discretePoincare`,
  `paraPMC_discretePoincare`, `paraPEC_discretePoincare`, and the star-shaped instances at the
  concrete witnesses `CubeWitness` and `ParallelepipedWitness`
  (`starPMC_cubeWitness_discretePoincare`, …, `starPEC_paraWitness_discretePoincare`).

No Poincaré inequality, closed range, compactness or exactness hypothesis enters the
well-posedness, propagation, convergence and residual statements. The rate classes are
hypotheses on the data (regularity of the orbit on `[0, T]`), as in `Feec.Maxwell.CubeFEM`.
The Gauss constraint is reducing, so the second branch of item 4 of the constrained FEEC theorem
(non-reducing constraints) concerns other constraints: the vanishing-field constraint
(`potential_residual`, `torus_potential_residual`) and any closed constraint
(`residual_not_isReducing`, `residual_not_isReducing_symm`, `residual_not_isReducing_of_grading`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.4 (Thms 4.6, 4.7), §4.6 (Thm 4.14), §4.9 (Prop. 4.16), §4.10 (Prop. 4.17)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3 (approximation property, bounded cochain projections, Thm 3.6), §5.4 (smoothed projections)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (rates for smooth
  solutions), Ch. 8 (evolution problems)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap Metric

@[expose] public noncomputable section

namespace Feec.Instances.Maxwell

open Feec.HilbertComplex _root_.Feec.HodgeWave

/-! ### The Gauss laws of a short complex -/

section Gauss

variable {𝕜 : Type*} [RCLike 𝕜] {W : Fin 3 → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  (H : HilbertComplex 𝕜 ComplexShape.fin3 W) (Y : Submodule 𝕜 (W 2))

/-- The Gauss-law family `{0} × N(d₀†) × Y` of a complex on `ComplexShape.fin3`
([QuennevilleBelair2015], Prop. 4.16). -/
def gaussFam : ∀ i : Fin 3, Submodule 𝕜 (W i)
  | 0 => ⊥
  | 1 => ((H.d 0 1)†).ker
  | 2 => Y

instance instHasOrthogonalProjectionGaussFam [Y.HasOrthogonalProjection] :
    ∀ i, (gaussFam H Y i).HasOrthogonalProjection
  | 0 => inferInstanceAs (⊥ : Submodule 𝕜 (W 0)).HasOrthogonalProjection
  | 1 => (hasOrthogonalProjection_ker (H.d 0 1)† (adjoint_isClosed (H.dense 0 1)) :
      ((H.d 0 1)†).ker.HasOrthogonalProjection)
  | 2 => inferInstanceAs Y.HasOrthogonalProjection

/-- **The Gauss laws form a reducing subcomplex** for every closed `Y ⊇ R(d₁)`: `(⊥, N(d₀†))`
reduces `d₀` because `R(d₀) ⊥ N(d₀†)`, and `(N(d₀†), Y)` reduces `d₁` because
`N(d₀†)ᗮ ⊆ N(d₁)` and `R(d₁) ⊆ Y`. [QuennevilleBelair2015], Prop. 4.16 -/
theorem reducingSubcomplex_gaussFam [Y.HasOrthogonalProjection]
    (hY : ∀ x : (H.d 1 2).domain, H.d 1 2 x ∈ Y) : H.ReducingSubcomplex (gaussFam H Y) := by
  have := hasOrthogonalProjection_ker (H.d 0 1)† (adjoint_isClosed (H.dense 0 1))
  refine ReducingSubcomplex.of_rel fun i j hij => ?_
  fin_cases i <;> fin_cases j <;> simp at hij
  · change (H.d 0 1).IsReducingPair (⊥ : Submodule 𝕜 (W 0)) ((H.d 0 1)†).ker
    refine isReducingPair_of_le_ker bot_le fun x => ?_
    rw [Submodule.mem_orthogonal]
    intro y hy
    obtain ⟨z, hz, hz0⟩ := mem_ker_iff.1 hy
    have h := adjoint_isFormalAdjoint (H.dense 0 1) z x
    rw [hz0, inner_zero_left] at h
    rw [hz]; exact h.symm
  · change (H.d 1 2).IsReducingPair ((H.d 0 1)†).ker Y
    exact isReducingPair_of_orthogonal_le_ker (H.orthogonal_ker_adjoint_le_ker 0 1 2) hY

/-- The **Gauss-law constraint** `{0} × N(d₀†) × Y` in the total space. -/
abbrev gauss : Submodule 𝕜 (PiLp 2 W) := totalSub (gaussFam H Y)

theorem mem_gauss {x : PiLp 2 W} :
    x ∈ gauss H Y ↔ x 0 = 0 ∧ x 1 ∈ ((H.d 0 1)†).ker ∧ x 2 ∈ Y := by
  constructor
  · intro h
    exact ⟨(Submodule.mem_bot 𝕜).1 (h 0), h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    exacts [(Submodule.mem_bot 𝕜).2 h0, h1, h2]

theorem isClosed_gauss [Y.HasOrthogonalProjection] : IsClosed (gauss H Y : Set (PiLp 2 W)) :=
  isClosed_totalSub (S := gaussFam H Y)

/-- **The Gauss laws reduce the Maxwell operator** `L = 𝐝 - 𝐝†`. [QuennevilleBelair2015],
Prop. 4.16 -/
theorem isReducing_gauss [Y.HasOrthogonalProjection]
    (hY : ∀ x : (H.d 1 2).domain, H.d 1 2 x ∈ Y) : H.wave.IsReducing (gauss H Y) :=
  (reducingSubcomplex_gaussFam H Y hY).isReducing_wave

end Gauss

/-! ### A non-reducing constraint: vanishing fields -/

section Potential

variable {𝕜 : Type*} [RCLike 𝕜] (W : Fin 3 → Type*)
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)]

/-- The family `W⁰ × {0} × {0}`. -/
def potentialFam : ∀ i : Fin 3, Submodule 𝕜 (W i)
  | 0 => ⊤
  | 1 => ⊥
  | 2 => ⊥

instance instHasOrthogonalProjectionPotentialFam [∀ i, CompleteSpace (W i)] :
    ∀ i, (potentialFam (𝕜 := 𝕜) W i).HasOrthogonalProjection
  | 0 => inferInstanceAs (⊤ : Submodule 𝕜 (W 0)).HasOrthogonalProjection
  | 1 => inferInstanceAs (⊥ : Submodule 𝕜 (W 1)).HasOrthogonalProjection
  | 2 => inferInstanceAs (⊥ : Submodule 𝕜 (W 2)).HasOrthogonalProjection

variable (𝕜) in
/-- The **vanishing-field constraint** `E = 0`, `B = 0` (only the scalar `σ` is free), the
constraint `W⁰ × {0} × {0}`. Its orthogonal complement is the constraint `σ = 0`. It does not
reduce the Maxwell operator as soon as `d₀ ≠ 0` (`not_isReducing_potential`): `E' = dσ`. -/
abbrev potential : Submodule 𝕜 (PiLp 2 W) := totalSub (potentialFam (𝕜 := 𝕜) W)

variable {W}

theorem mem_potential {x : PiLp 2 W} : x ∈ potential 𝕜 W ↔ x 1 = 0 ∧ x 2 = 0 := by
  constructor
  · intro h
    exact ⟨(Submodule.mem_bot 𝕜).1 (h 1), (Submodule.mem_bot 𝕜).1 (h 2)⟩
  · rintro ⟨h1, h2⟩ i
    fin_cases i
    exacts [Submodule.mem_top, (Submodule.mem_bot 𝕜).2 h1, (Submodule.mem_bot 𝕜).2 h2]

theorem single_zero_mem_potential (σ : W 0) : PiLp.single 2 (0 : Fin 3) σ ∈ potential 𝕜 W :=
  mem_potential.2 ⟨PiLp.single_eq_of_ne (p := 2) (by decide) _,
    PiLp.single_eq_of_ne (p := 2) (by decide) _⟩

variable [∀ i, CompleteSpace (W i)]

theorem isClosed_potential : IsClosed (potential 𝕜 W : Set (PiLp 2 W)) := isClosed_totalSub

variable (H : HilbertComplex 𝕜 ComplexShape.fin3 W)

/-- `(σ, 0, 0) ∈ D(L)` for `σ ∈ D(d₀)`. -/
theorem single_zero_mem_wave_domain {σ : W 0} (hσ : σ ∈ (H.d 0 1).domain) :
    PiLp.single 2 (0 : Fin 3) σ ∈ H.wave.domain := by
  refine ⟨H.single_mem_totalDomain 0 ?_, H.dual.single_mem_totalDomain 0 ?_⟩
  · rw [ComplexShape.next_eq' _ (show ComplexShape.fin3.Rel 0 1 by
      simp [ComplexShape.window_rel])]
    exact hσ
  · rw [H.dual.domain_eq_top_of_not_rel]
    · exact Submodule.mem_top
    · intro h
      change ComplexShape.fin3.Rel _ 0 at h
      simp [ComplexShape.window_rel] at h

/-- `L (σ, 0, 0) = (0, dσ, 0)`: the electric component is `dσ`. -/
theorem wave_single_zero_one {σ : W 0} (hσ : σ ∈ (H.d 0 1).domain) :
    (H.wave ⟨_, single_zero_mem_wave_domain H hσ⟩) 1 = H.d 0 1 ⟨σ, hσ⟩ := by
  rw [wave_apply, Fin.sum_univ_three, Fin.sum_univ_three]
  have z : ∀ {j k : Fin 3} (T : W j →ₗ.[𝕜] W k) (h : (0 : W j) ∈ T.domain), T ⟨0, h⟩ = 0 :=
    fun T h => LinearPMap.apply_mk_eq_zero T h rfl
  have e0 : (PiLp.single 2 (0 : Fin 3) σ : PiLp 2 W) 0 = σ := PiLp.single_eq_same (p := 2) _ _
  have e1 : (PiLp.single 2 (0 : Fin 3) σ : PiLp 2 W) 1 = 0 :=
    PiLp.single_eq_of_ne (p := 2) (by decide) _
  have e2 : (PiLp.single 2 (0 : Fin 3) σ : PiLp 2 W) 2 = 0 :=
    PiLp.single_eq_of_ne (p := 2) (by decide) _
  have h3 : ∀ hx, (H.d 1 0)† ⟨σ, hx⟩ = 0 := fun hx =>
    H.dual.apply_eq_zero_of_not_rel (i := 0) (j := 1) (by simp [ComplexShape.window_rel]) ⟨_, hx⟩
  simp only [e0, e1, e2, z, h3, add_zero, sub_zero]

/-- **The vanishing-field constraint does not reduce the Maxwell operator** when `d₀ ≠ 0`:
for `dσ ≠ 0`, `(σ, 0, 0) ∈ D(L) ∩ K` but `L (σ, 0, 0) = (0, dσ, 0) ∉ K`. -/
theorem not_isReducing_potential (hd : ∃ σ : (H.d 0 1).domain, H.d 0 1 σ ≠ 0) :
    ¬ H.wave.IsReducing (potential 𝕜 W) := by
  intro h
  obtain ⟨⟨σ, hσ⟩, hne⟩ := hd
  have hm := ((H.isSkewAdjoint_wave.isReducing_iff).1 h).2 ⟨_, single_zero_mem_wave_domain H hσ⟩
    (single_zero_mem_potential σ)
  exact hne ((wave_single_zero_one H hσ).symm.trans (mem_potential.1 hm).1)

/-- `D(L) ∩ K` is dense in the vanishing-field constraint `K` (`D(d₀)` is dense). -/
theorem dense_potential : ∀ k ∈ potential 𝕜 W,
    k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ potential 𝕜 W) := by
  intro k hk
  have hk' : k = PiLp.single 2 (0 : Fin 3) (k 0) := by
    ext i
    fin_cases i
    · exact (PiLp.single_eq_same (p := 2) _ _).symm
    · exact (mem_potential.1 hk).1.trans (PiLp.single_eq_of_ne (p := 2) (by decide) _).symm
    · exact (mem_potential.1 hk).2.trans (PiLp.single_eq_of_ne (p := 2) (by decide) _).symm
  have hc : Continuous fun σ : W 0 => (PiLp.single 2 (0 : Fin 3) σ : PiLp 2 W) := by
    refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun a b => ?_)
    rw [dist_eq_norm, dist_eq_norm, ← PiLp.single_sub, PiLp.norm_single]; simp
  rw [hk']
  exact map_mem_closure hc (s := ((H.d 0 1).domain : Set (W 0)))
    ((H.dense 0 1).closure_eq ▸ mem_univ _) fun σ hσ =>
      ⟨single_zero_mem_wave_domain H hσ, single_zero_mem_potential σ⟩

end Potential

/-! ### Windows -/

section Window

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [AddCommMonoidWithOne α] [IsCancelAdd α]
  [CharZero α] {V : α → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)]
  [∀ i, CompleteSpace (V i)] (H : HilbertComplex 𝕜 (ComplexShape.up α) V) (a : α)

/-- The **magnetic Gauss law** `dB = 0` of the Maxwell window `V a → V (a+1) → V (a+2)`: the
kernel of `d : V (a+2) → V (a+3)`. -/
abbrev magnetic : Submodule 𝕜 (V (a + ((2 : Fin 3) : α))) :=
  (H.d (a + ((2 : Fin 3) : α)) (a + ((2 : Fin 3) : α) + 1)).ker

instance : (magnetic H a).HasOrthogonalProjection :=
  hasOrthogonalProjection_ker _ (H.closed _ _)

/-- `R(d) ⊆ N(d)`: the curl of an electric field satisfies the magnetic Gauss law. -/
theorem d_mem_magnetic (x : ((H.window a 3).d 1 2).domain) :
    (H.window a 3).d 1 2 x ∈ magnetic H a :=
  LinearPMap.mem_ker_iff.2 ⟨⟨_, H.mapsTo _ _ (a + ((2 : Fin 3) : α) + 1) x⟩, rfl,
    H.d_comp_d _ _ _ x⟩

/-- The **Gauss laws** `σ = 0`, `d†E = 0`, `dB = 0` of the Maxwell window of `H` in degree
`a`. -/
abbrev windowGauss : Submodule 𝕜 (PiLp 2 fun i : Fin 3 => V (a + i)) :=
  gauss (H.window a 3) (magnetic H a)

/-- **The Gauss laws reduce the Maxwell operator** of every window of every Hilbert complex.
[QuennevilleBelair2015], Prop. 4.16 -/
theorem isReducing_windowGauss : (H.window a 3).wave.IsReducing (windowGauss H a) :=
  isReducing_gauss _ _ (d_mem_magnetic H a)

variable {H}

/-- The window `S^a → S^{a+1} → S^{a+2}` of a subcomplex, a subcomplex of `H.window a 3`. -/
def subWindow (S : H.Subcomplex) (a : α) : (H.window a 3).Subcomplex where
  V i := S.V (a + i)
  le_domain _ _ := S.le_domain _ _
  mapsTo _ _ := S.mapsTo _ _

instance (S : H.Subcomplex) [∀ k, FiniteDimensional 𝕜 (S.V k)] (i : Fin 3) :
    FiniteDimensional 𝕜 ((subWindow S a).V i) :=
  inferInstanceAs (FiniteDimensional 𝕜 (S.V (a + i)))

/-- The window of a cochain projection, a cochain projection onto `subWindow S a`. -/
def projWindow {S : H.Subcomplex} (P : S.CochainProjection) (a : α) :
    (subWindow S a).CochainProjection where
  π i := P.π (a + i)
  mem _ x := P.mem _ x
  proj _ x hx := P.proj _ x hx
  comm _ _ x := P.comm _ _ x

/-- **Graph-norm approximation in the Maxwell window from degreewise estimates**: if every
component of `ζ ∈ Γ(𝐝)` is within `ε` of `Sᵏ`, with `‖d (x - v)‖ ≤ ε`, some point of the window
of `S` is within `12 ε` of `ζ`. -/
theorem exists_mem_subWindow_le (S : H.Subcomplex) (ζ : (H.window a 3).totalD.GraphSpace)
    {ε : ℝ}
    (hdeg : ∀ i : Fin 3, ∃ v, ∃ hv : v ∈ S.V (a + i),
      ‖(H.window a 3).totalD.graphFst ζ i - v‖ ≤ ε ∧
      ∀ j (hx : (H.window a 3).totalD.graphFst ζ i ∈ (H.d (a + i) j).domain),
        ‖H.d (a + i) j ⟨(H.window a 3).totalD.graphFst ζ i - v,
          Submodule.sub_mem _ hx (S.le_domain _ j hv)⟩‖ ≤ ε) :
    ∃ w ∈ (subWindow S a).graphSub, ‖ζ - w‖ ≤ 12 * ε := by
  obtain ⟨x, rfl, -, -⟩ := (H.window a 3).totalD.exists_toGraphSpace_eq ζ
  simp only [LinearPMap.graphFst_toGraphSpace] at hdeg
  obtain ⟨w, hw, hle⟩ := Subcomplex.exists_mem_graphSub_le (subWindow S a) x (ε := ε)
    fun i => by
      obtain ⟨v, hv, h1, h2⟩ := hdeg i
      exact ⟨v, hv, h1, fun j hx => h2 (a + j) hx⟩
  refine ⟨w, hw, hle.trans_eq ?_⟩
  rw [Fintype.card_fin]; norm_num

end Window

/-! ### The approximation property from degreewise density -/

section Density

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex 𝕜 c W}

/-- **Degreewise `L²` density gives the approximation property of the total space.** -/
theorem dense_of_forall {κ : Type*} {l : Filter κ} (S : κ → H.Subcomplex)
    (hS : ∀ i (y : W i) (ε : ℝ), 0 < ε → ∀ᶠ h in l, ∃ v ∈ (S h).V i, ‖y - v‖ < ε) :
    ∀ x : PiLp 2 W, ∀ δ > 0, ∀ᶠ h in l, ∃ w ∈ totalSub (S h).V, ‖x - w‖ < δ := by
  intro x δ hδ
  set m : ℝ := (Fintype.card ι : ℝ)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  set ε := δ / (m + 1)
  have hε : 0 < ε := div_pos hδ (by positivity)
  filter_upwards [Filter.eventually_all.2 fun i => hS i (x i) ε hε] with h hh
  choose v hv hlt using hh
  refine ⟨WithLp.toLp 2 fun i => v i, fun i => hv i, ?_⟩
  refine (PiLp.norm_le_sum_norm _).trans_lt ?_
  have e : m * ε < δ := by
    have : m * ε = m / (m + 1) * δ := by simp only [ε]; field_simp
    rw [this]
    have h1 : m / (m + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith
  calc ∑ i, ‖(x - WithLp.toLp 2 fun i => v i) i‖ ≤ ∑ _i : ι, ε :=
        Finset.sum_le_sum fun i _ => by simpa using (hlt i).le
    _ = m * ε := by simp [m]
    _ < δ := e

end Density

/-! ### Maxwell discretizations -/

section Discretization

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [AddCommMonoidWithOne α] [IsCancelAdd α]
  [CharZero α] {V : α → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)]
  [∀ i, CompleteSpace (V i)] (H : HilbertComplex 𝕜 (ComplexShape.up α) V) (a : α)
  {κ : Type*} (l : Filter κ) (S : κ → H.Subcomplex) [∀ h k, FiniteDimensional 𝕜 ((S h).V k)]
  (P : ∀ h, (S h).CochainProjection)

/-- **The constrained FEEC discretization of Maxwell's equations** in the window
`V a → V (a+1) → V (a+2)` of `H`, with the Gauss laws as constraint, from finite-dimensional
subcomplexes `S h` of `H`, cochain projections `P h` bounded uniformly in `L²` and degreewise
`L²` density of the `S h` along `l`. -/
def feec (hP : ∃ C, ∀ h k x, ‖(P h).π k x‖ ≤ C * ‖x‖)
    (hS : ∀ k (y : V k) (ε : ℝ), 0 < ε → ∀ᶠ h in l, ∃ v ∈ (S h).V k, ‖y - v‖ < ε) :
    ConstrainedFEEC (H.window a 3) κ where
  K := windowGauss H a
  isClosed_K := isClosed_gauss _ _
  l := l
  V h := subWindow (S h) a
  finiteDimensional h i := inferInstanceAs (FiniteDimensional 𝕜 ((S h).V (a + i)))
  π h := projWindow (P h) a
  bound_π := by
    obtain ⟨C, hC⟩ := hP
    exact ⟨C, fun h i x => hC h _ x⟩
  dense := dense_of_forall (fun h => subWindow (S h) a) fun i y ε hε => hS (a + i) y ε hε

variable {H a l S P}
variable (hP : ∃ C, ∀ h k x, ‖(P h).π k x‖ ≤ C * ‖x‖)
  (hS : ∀ k (y : V k) (ε : ℝ), 0 < ε → ∀ᶠ h in l, ∃ v ∈ (S h).V k, ‖y - v‖ < ε)

@[simp] theorem feec_K : (feec H a l S P hP hS).K = windowGauss H a := rfl

theorem isReducing_feec_K : (H.window a 3).wave.IsReducing (feec H a l S P hP hS).K :=
  isReducing_windowGauss H a

variable [∀ i, NormedSpace ℝ (V i)] [∀ i, IsScalarTower ℝ 𝕜 (V i)]

omit [∀ h k, FiniteDimensional 𝕜 ((S h).V k)] in
variable (H a) in
/-- **The Gauss laws propagate** in every Maxwell window, for all data and all times `t ∈ ℝ`, with
no discretization: item (2) of the constrained FEEC theorem (`constrainedFEEC_propagates_iff`) at
the reducing constraint `windowGauss H a`. [QuennevilleBelair2015], Prop. 4.16, Prop. 4.17 -/
theorem windowGauss_propagates : ∀ t, ∀ x ∈ windowGauss H a,
    (H.window a 3).waveGroup.S t x ∈ windowGauss H a :=
  ((H.window a 3).isReducing_iff_waveGroup_invariant _ |>.trans C0Group.map_le_iff_forall).1
    (isReducing_windowGauss H a)

omit [∀ h k, FiniteDimensional 𝕜 ((S h).V k)] in
variable (H a) in
/-- **The Gauss laws propagate along strong solutions** on `[0, T]` in every Maxwell window, with
no discretization. [QuennevilleBelair2015], Prop. 4.16 -/
theorem windowGauss_propagates_strong {T : ℝ} {U : ℝ → PiLp 2 fun i : Fin 3 => V (a + i)}
    (h0 : U 0 ∈ windowGauss H a)
    (hU : Evolution.IsStrongSolution (H.window a 3).wave (Icc 0 T) 0 U) :
    ∀ t ∈ Icc 0 T, U t ∈ windowGauss H a :=
  hU.mem_of_isReducing (H.window a 3).isSkewAdjoint_wave.isDissipative
    (isReducing_windowGauss H a) h0 fun _ _ => (windowGauss H a).zero_mem

/-- The **rate class of regular data** on `[0, T]`: data `x ∈ D(L²)` whose orbit `e^{tL} x` and
derivative `e^{tL} L x` have components satisfying the degreewise regularity `Reg` for
`t ∈ [0, T]`, when every `Reg`-regular form of degree `k` is within `B k Λ r_h` of `Sₕᵏ` in the
graph norm. The constant is `12 Σᵢ B (a + i)`, the order `1` in `r_h`, the class norm `Λ`. -/
def regRate (T : ℝ) (Reg : ∀ k, V k → Prop) (B : α → ℝ) (r : κ → ℝ) (Λ : ℝ)
    (happ : ∀ h k (x : V k), Reg k x → ∃ v, ∃ hv : v ∈ (S h).V k,
      ‖x - v‖ ≤ B k * Λ * r h ∧ ∀ j (hxj : x ∈ (H.d k j).domain),
        ‖H.d k j ⟨x - v, Submodule.sub_mem _ hxj ((S h).le_domain k j hv)⟩‖ ≤ B k * Λ * r h)
    (hB : ∀ k, 0 ≤ B k) (hΛ : 0 ≤ Λ) (hr : ∀ h, 0 ≤ r h) :
    (feec H a l S P hP hS).RateClass T where
  Data := {x | ∃ hx : x ∈ (H.window a 3).wave.domain,
    (H.window a 3).wave ⟨x, hx⟩ ∈ (H.window a 3).wave.domain ∧ ∀ s ∈ Icc 0 T,
      (∀ i : Fin 3, Reg (a + i) ((H.window a 3).waveGroup.S s x i)) ∧
      ∀ i : Fin 3, Reg (a + i) ((H.window a 3).waveGroup.S s ((H.window a 3).wave ⟨x, hx⟩) i)}
  classNorm _ := Λ
  meshSize := r
  α := 1
  C := 12 * ∑ i : Fin 3, B (a + i)
  mem_domain _ hx := hx.1
  mem_domain_sq _ _ hx := by
    obtain ⟨_, h, -⟩ := hx
    exact h
  approx x hx h t ht v hv := by
    obtain ⟨_, _, hreg⟩ := hx
    obtain ⟨w, hw, hle⟩ := exists_mem_subWindow_le a (S h) v
      (ε := (∑ i : Fin 3, B (a + i)) * Λ * r h) fun i => by
        rw [hv]
        obtain ⟨u, hu, h1, h2⟩ := happ h _ _ ((hreg t ht).1 i)
        have hle : B (a + i) * Λ * r h ≤ (∑ i : Fin 3, B (a + i)) * Λ * r h :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (Finset.single_le_sum (f := fun i : Fin 3 => B (a + i)) (fun _ _ => hB _)
              (Finset.mem_univ i)) hΛ) (hr h)
        exact ⟨u, hu, h1.trans hle, fun j hxj => (h2 j hxj).trans hle⟩
    refine ⟨w, hw, hle.trans_eq ?_⟩
    rw [Real.rpow_one]; ring
  approx_deriv x hx' hx h t ht v hv := by
    obtain ⟨_, _, hreg⟩ := hx
    obtain ⟨w, hw, hle⟩ := exists_mem_subWindow_le a (S h) v
      (ε := (∑ i : Fin 3, B (a + i)) * Λ * r h) fun i => by
        rw [hv]
        obtain ⟨u, hu, h1, h2⟩ := happ h _ _ ((hreg t ht).2 i)
        have hle : B (a + i) * Λ * r h ≤ (∑ i : Fin 3, B (a + i)) * Λ * r h :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (Finset.single_le_sum (f := fun i : Fin 3 => B (a + i)) (fun _ _ => hB _)
              (Finset.mem_univ i)) hΛ) (hr h)
        exact ⟨u, hu, h1.trans hle, fun j hxj => (h2 j hxj).trans hle⟩
    refine ⟨w, hw, hle.trans_eq ?_⟩
    rw [Real.rpow_one]; ring

/-! ### The headline statements for every Maxwell discretization -/

/-- **Well-posedness of Maxwell's equations** (Stone): for `ξ₀ ∈ D(L)`, `t ↦ e^{tL} ξ₀` is a
classical solution on `[0, T]`, the only strong and the only weak solution, and it conserves
energy. [QuennevilleBelair2015], Thm 4.6, Thm 4.7 -/
theorem wellPosed {x : PiLp 2 fun i : Fin 3 => V (a + i)} (hx : x ∈ (H.window a 3).wave.domain)
    (T : ℝ) :
    Evolution.IsClassicalSolution (H.window a 3).wave (Icc 0 T) 0
        (fun t => (H.window a 3).waveGroup.S t x) ∧
      (∀ U, U 0 = x → Evolution.IsStrongSolution (H.window a 3).wave (Icc 0 T) 0 U →
        EqOn U (fun t => (H.window a 3).waveGroup.S t x) (Icc 0 T)) ∧
      (∀ U, U 0 = x → HilbertComplex.HodgeWave.IsWeakSolution (H.window a 3) (Icc 0 T) 0 U →
        EqOn U (fun t => (H.window a 3).waveGroup.S t x) (Icc 0 T)) ∧
      ∀ t, ‖(H.window a 3).waveGroup.S t x‖ = ‖x‖ :=
  constrainedFEEC_wellPosed hx T

/-- **The Gauss laws propagate** for all data and all times `t ∈ ℝ`: the Gauss constraint of
the discretization is reducing. [QuennevilleBelair2015], Prop. 4.16, Prop. 4.17 -/
theorem gauss_propagates : ∀ t, ∀ x ∈ (feec H a l S P hP hS).K,
    (H.window a 3).waveGroup.S t x ∈ (feec H a l S P hP hS).K :=
  (feec H a l S P hP hS).constrainedFEEC_of_approxFEEC.2.1.1 (isReducing_windowGauss H a)

/-- **The Gauss laws propagate along strong solutions** on `[0, T]`. [QuennevilleBelair2015],
Prop. 4.16 -/
theorem gauss_propagates_strong {T : ℝ} {U : ℝ → PiLp 2 fun i : Fin 3 => V (a + i)}
    (h0 : U 0 ∈ (feec H a l S P hP hS).K)
    (hU : Evolution.IsStrongSolution (H.window a 3).wave (Icc 0 T) 0 U) :
    ∀ t ∈ Icc 0 T, U t ∈ (feec H a l S P hP hS).K :=
  constrainedFEEC_propagates (feec H a l S P hP hS) (isReducing_windowGauss H a) h0 hU

/-- **Convergence of the semi-discrete Maxwell solutions**, uniformly on `[0, T]`, for data in
`D(L)` (`ξₕ(0) = Pₕ ξ₀`), and for data in `W` along every family with `ξₕ(0) → ξ₀` (such
families exist). [QuennevilleBelair2015], Thm 4.14 -/
theorem converges (T : ℝ) :
    (∀ x : (H.window a 3).wave.domain, TendstoUniformlyOn
      (fun h t => (H.window a 3).totalD.graphFst
        ((feec H a l S P hP hS).discrete h (waveLift _ x) t))
      (fun t => (H.window a 3).waveGroup.S t x) l (Icc 0 T)) ∧
    ∀ x : PiLp 2 fun i : Fin 3 => V (a + i),
      (∀ ξh ξh' : κ → ℝ → (H.window a 3).totalD.GraphSpace,
        (∀ h, IsSemidiscreteSolution ((feec H a l S P hP hS).Kh h) (Icc 0 T) (ξh h) (ξh' h)) →
        Tendsto (fun h => (H.window a 3).totalD.graphFst (ξh h 0)) l (𝓝 x) →
        TendstoUniformlyOn (fun h t => (H.window a 3).totalD.graphFst (ξh h t))
          (fun t => (H.window a 3).waveGroup.S t x) l (Icc 0 T)) ∧
      ∃ ξh ξh' : κ → ℝ → (H.window a 3).totalD.GraphSpace,
        (∀ h, IsSemidiscreteSolution ((feec H a l S P hP hS).Kh h) (Icc 0 T) (ξh h) (ξh' h)) ∧
        Tendsto (fun h => (H.window a 3).totalD.graphFst (ξh h 0)) l (𝓝 x) :=
  (feec H a l S P hP hS).constrainedFEEC_of_approxFEEC.2.2.1 T

/-- **The rate of the semi-discrete Maxwell solutions** for data in a rate class on `[0, T]`:
`‖ξ(t) - ξₕ(t)‖ ≤ (1 + C_P) (1 + t)² C hᵅ ‖ξ₀‖_class`. [QuennevilleBelair2015], Thm 4.14 -/
theorem rate {T : ℝ} (R : (feec H a l S P hP hS).RateClass T)
    {x : PiLp 2 fun i : Fin 3 => V (a + i)} (hxR : x ∈ R.Data) (h : κ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖(H.window a 3).waveGroup.S t x - (H.window a 3).totalD.graphFst
        ((feec H a l S P hP hS).discrete h (waveLift _ ⟨x, R.mem_domain x hxR⟩) t)‖ ≤
      (1 + ellipticConst (H.window a 3)) * (1 + t) ^ 2 *
        (R.C * R.meshSize h ^ R.α * R.classNorm x) :=
  (feec H a l S P hP hS).constrainedFEEC_of_approxFEEC.2.2.2.1 _ R _ hxR h _ ht

/-- **The Gauss-law residual of the discrete solutions**: for data in `D(L)` satisfying the Gauss
laws, `dist(ξₕ(t), K) ≤ ‖ξ(t) - ξₕ(t)‖`, and the residual tends to `0` uniformly on `[0, T]`. -/
theorem residual (x : (H.window a 3).wave.domain) (hxK : (x : PiLp 2 _) ∈ windowGauss H a)
    (T : ℝ) :
    (∀ h t, infDist ((H.window a 3).totalD.graphFst
        ((feec H a l S P hP hS).discrete h (waveLift _ x) t)) (windowGauss H a : Set _) ≤
      ‖(H.window a 3).waveGroup.S t x - (H.window a 3).totalD.graphFst
        ((feec H a l S P hP hS).discrete h (waveLift _ x) t)‖) ∧
    TendstoUniformlyOn
      (fun h t => infDist ((H.window a 3).totalD.graphFst
        ((feec H a l S P hP hS).discrete h (waveLift _ x) t)) (windowGauss H a : Set _))
      (fun _ => 0) l (Icc 0 T) :=
  (feec H a l S P hP hS).constrainedFEEC_of_approxFEEC.2.2.2.2.1 (isReducing_windowGauss H a)
    x hxK T

/-- **Rate of the Gauss-law residual** for data in a rate class satisfying the Gauss laws. -/
theorem residual_rate {T : ℝ} (R : (feec H a l S P hP hS).RateClass T)
    {x : PiLp 2 fun i : Fin 3 => V (a + i)} (hxR : x ∈ R.Data) (hxK : x ∈ windowGauss H a)
    (h : κ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    infDist ((H.window a 3).totalD.graphFst
        ((feec H a l S P hP hS).discrete h (waveLift _ ⟨x, R.mem_domain x hxR⟩) t))
        (windowGauss H a : Set _) ≤
      (1 + ellipticConst (H.window a 3)) * (1 + t) ^ 2 *
        (R.C * R.meshSize h ^ R.α * R.classNorm x) :=
  ((feec H a l S P hP hS).infDist_le_norm_sub
    ((feec H a l S P hP hS).constrainedFEEC_of_approxFEEC.2.1.1 (isReducing_windowGauss H a) t x
      hxK)).trans (rate hP hS R hxR h ht)

/-- **Non-vacuity of `regRate`**: the zero datum lies in the rate class whenever the zero form is
regular in every degree. -/
theorem zero_mem_regRate {T : ℝ} {Reg : ∀ k, V k → Prop} {B : α → ℝ} {r : κ → ℝ} {Λ : ℝ}
    {happ : ∀ h k (x : V k), Reg k x → ∃ v, ∃ hv : v ∈ (S h).V k,
      ‖x - v‖ ≤ B k * Λ * r h ∧ ∀ j (hxj : x ∈ (H.d k j).domain),
        ‖H.d k j ⟨x - v, Submodule.sub_mem _ hxj ((S h).le_domain k j hv)⟩‖ ≤ B k * Λ * r h}
    {hB : ∀ k, 0 ≤ B k} {hΛ : 0 ≤ Λ} {hr : ∀ h, 0 ≤ r h} (h0 : ∀ k, Reg k 0) :
    (0 : PiLp 2 fun i : Fin 3 => V (a + i)) ∈ (regRate hP hS T Reg B r Λ happ hB hΛ hr).Data := by
  have e : (H.window a 3).wave ⟨0, (H.window a 3).wave.domain.zero_mem⟩ = 0 :=
    (H.window a 3).wave.toFun.map_zero
  refine ⟨(H.window a 3).wave.domain.zero_mem, ?_, fun s _ => ⟨fun i => ?_, fun i => ?_⟩⟩
  · rw [e]; exact (H.window a 3).wave.domain.zero_mem
  · rw [_root_.map_zero]; exact h0 _
  · rw [e, _root_.map_zero]; exact h0 _

/-- **The `O(r_h)` rate for regular data** (`regRate`): for `x` whose orbit and derivative are
`Reg`-regular on `[0, T]`, `‖ξ(t) - ξₕ(t)‖ ≤ (1 + C_P) (1 + t)² · 12 (Σᵢ B (a + i)) r_h Λ`.
[QuennevilleBelair2015], Thm 4.14 -/
theorem rate_regRate {T : ℝ} {Reg : ∀ k, V k → Prop} {B : α → ℝ} {r : κ → ℝ} {Λ : ℝ}
    {happ : ∀ h k (x : V k), Reg k x → ∃ v, ∃ hv : v ∈ (S h).V k,
      ‖x - v‖ ≤ B k * Λ * r h ∧ ∀ j (hxj : x ∈ (H.d k j).domain),
        ‖H.d k j ⟨x - v, Submodule.sub_mem _ hxj ((S h).le_domain k j hv)⟩‖ ≤ B k * Λ * r h}
    {hB : ∀ k, 0 ≤ B k} {hΛ : 0 ≤ Λ} {hr : ∀ h, 0 ≤ r h} {x : PiLp 2 fun i : Fin 3 => V (a + i)}
    (hx : x ∈ (regRate hP hS T Reg B r Λ happ hB hΛ hr).Data) (h : κ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖(H.window a 3).waveGroup.S t x - (H.window a 3).totalD.graphFst
        ((feec H a l S P hP hS).discrete h (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst (H.window a 3)) * (1 + t) ^ 2 *
        (12 * (∑ i : Fin 3, B (a + i)) * r h * Λ) := by
  simpa only [regRate, Real.rpow_one] using
    rate hP hS (regRate hP hS T Reg B r Λ happ hB hΛ hr) hx h ht

/-- **The `O(r_h)` rate of the Gauss-law residual** for regular data satisfying the Gauss laws. -/
theorem residual_rate_regRate {T : ℝ} {Reg : ∀ k, V k → Prop} {B : α → ℝ} {r : κ → ℝ} {Λ : ℝ}
    {happ : ∀ h k (x : V k), Reg k x → ∃ v, ∃ hv : v ∈ (S h).V k,
      ‖x - v‖ ≤ B k * Λ * r h ∧ ∀ j (hxj : x ∈ (H.d k j).domain),
        ‖H.d k j ⟨x - v, Submodule.sub_mem _ hxj ((S h).le_domain k j hv)⟩‖ ≤ B k * Λ * r h}
    {hB : ∀ k, 0 ≤ B k} {hΛ : 0 ≤ Λ} {hr : ∀ h, 0 ≤ r h} {x : PiLp 2 fun i : Fin 3 => V (a + i)}
    (hx : x ∈ (regRate hP hS T Reg B r Λ happ hB hΛ hr).Data) (hxK : x ∈ windowGauss H a)
    (h : κ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    infDist ((H.window a 3).totalD.graphFst
        ((feec H a l S P hP hS).discrete h (waveLift _ ⟨x, hx.1⟩) t)) (windowGauss H a : Set _) ≤
      (1 + ellipticConst (H.window a 3)) * (1 + t) ^ 2 *
        (12 * (∑ i : Fin 3, B (a + i)) * r h * Λ) := by
  have := residual_rate hP hS (regRate hP hS T Reg B r Λ happ hB hΛ hr) hx hxK h ht
  simp only [regRate, Real.rpow_one] at this
  exact this

end Discretization

/-! ### Other constraints -/

section OtherConstraint

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  {H : HilbertComplex 𝕜 c W} {κ : Type*}

/-- The same discretization with another closed constraint `K`. -/
def withConstraint (F : ConstrainedFEEC H κ) (K : Submodule 𝕜 (PiLp 2 W))
    (hK : IsClosed (K : Set (PiLp 2 W))) : ConstrainedFEEC H κ :=
  { F with K := K, isClosed_K := hK }

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- **A non-reducing constraint is violated**: for a closed constraint `K` that does not reduce
the Maxwell operator, for every `T > 0` the constraint `Q = K` or `Q = Kᗮ` has a datum leaving
`Q` at some `t ∈ [0, T]`, and the residuals of every convergent family of semi-discrete
solutions tend to a positive limit. -/
theorem residual_not_isReducing (F : ConstrainedFEEC H κ) {K : Submodule 𝕜 (PiLp 2 W)}
    (hK : IsClosed (K : Set (PiLp 2 W))) (hnot : ¬ H.wave.IsReducing K) {T : ℝ} (hT : 0 < T) :
    ∃ Q : Submodule 𝕜 (PiLp 2 W), (Q = K ∨ Q = Kᗮ) ∧ ∃ x ∈ Q, ∃ t ∈ Icc 0 T,
      H.waveGroup.S t x ∉ Q ∧ 0 < infDist (H.waveGroup.S t x) (Q : Set (PiLp 2 W)) ∧
      ∀ ξh ξh' : κ → ℝ → H.totalD.GraphSpace,
        (∀ h, IsSemidiscreteSolution ((withConstraint F K hK).Kh h) (Icc 0 T) (ξh h) (ξh' h)) →
        Tendsto (fun h => H.totalD.graphFst (ξh h 0)) F.l (𝓝 x) →
        Tendsto (fun h => infDist (H.totalD.graphFst (ξh h t)) (Q : Set (PiLp 2 W))) F.l
          (𝓝 (infDist (H.waveGroup.S t x) (Q : Set (PiLp 2 W)))) :=
  (withConstraint F K hK).constrainedFEEC_of_approxFEEC.2.2.2.2.2.1 hnot T hT

/-- Changing the constraint does not change the discrete solutions. -/
@[simp] theorem discrete_withConstraint (F : ConstrainedFEEC H κ) {K : Submodule 𝕜 (PiLp 2 W)}
    (hK : IsClosed (K : Set (PiLp 2 W))) : (withConstraint F K hK).discrete = F.discrete := rfl

/-- **A non-reducing constraint is violated by data in `D(L) ∩ K`, in one of the two time
directions** (`constrainedFEEC_residual_not_isReducing_symm`): if `K` does not reduce `L` and
`D(L) ∩ K` is dense in `K`, for every `T > 0` some `x ∈ D(L) ∩ K` has `e^{tL} x ∉ K` for some
`t ∈ [-T, T]`. -/
theorem residual_not_isReducing_symm (F : ConstrainedFEEC H κ) {K : Submodule 𝕜 (PiLp 2 W)}
    (hK : IsClosed (K : Set (PiLp 2 W))) (hnot : ¬ H.wave.IsReducing K)
    (hdense : ∀ k ∈ K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ K)) {T : ℝ} (hT : 0 < T) :
    ∃ x : H.wave.domain, (x : PiLp 2 W) ∈ K ∧ ∃ t ∈ Icc (-T) T,
      H.waveGroup.S t x ∉ K ∧ 0 < infDist (H.waveGroup.S t x) (K : Set (PiLp 2 W)) :=
  (withConstraint F K hK).constrainedFEEC_of_approxFEEC.2.2.2.2.2.2.1 hnot hdense T hT

/-- **On a graded complex a non-reducing constraint is violated forward in time by data in
`D(L) ∩ K`, and so are the discrete solutions** (`constrainedFEEC_residual_not_isReducing_of_grading`):
for a grading `p`, an `R`-invariant closed `K` not reducing `L` with `D(L) ∩ K` dense in `K`, and
`T > 0`, some `x ∈ D(L) ∩ K` leaves `K` at some `t ∈ [0, T]`, and the residuals
`dist(ξₕ(t), K)` of the discrete solutions tend to `dist(e^{tL} x, K) > 0` (eventually above half
of it). -/
theorem residual_not_isReducing_of_grading (F : ConstrainedFEEC H κ) {K : Submodule 𝕜 (PiLp 2 W)}
    (hK : IsClosed (K : Set (PiLp 2 W))) {p : ι → Bool} (hp : ∀ i j, c.Rel i j → p j ≠ p i)
    (hRK : ∀ x ∈ K, reversal 𝕜 p x ∈ K)
    (hdense : ∀ k ∈ K, k ∈ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ K))
    (hnot : ¬ H.wave.IsReducing K) {T : ℝ} (hT : 0 < T) :
    ∃ x : H.wave.domain, (x : PiLp 2 W) ∈ K ∧ ∃ t ∈ Icc 0 T,
      H.waveGroup.S t x ∉ K ∧ 0 < infDist (H.waveGroup.S t x) (K : Set (PiLp 2 W)) ∧
      Tendsto (fun h => infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t))
        (K : Set (PiLp 2 W))) F.l (𝓝 (infDist (H.waveGroup.S t x) (K : Set (PiLp 2 W)))) ∧
      ∀ᶠ h in F.l, infDist (H.waveGroup.S t x) (K : Set (PiLp 2 W)) / 2 <
        infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t)) (K : Set (PiLp 2 W)) :=
  (withConstraint F K hK).constrainedFEEC_of_approxFEEC.2.2.2.2.2.2.2 p hp hRK hdense hnot T hT

end OtherConstraint

/-! ### The vanishing-field constraint: item (4) for a non-reducing Maxwell constraint -/

section PotentialConstraint

variable {𝕜 : Type*} [RCLike 𝕜] {W : Fin 3 → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  {H : HilbertComplex 𝕜 ComplexShape.fin3 W} {κ : Type*}

/-- **The vanishing-field constraint is violated, also by the discrete solutions**: if `d₀ ≠ 0`,
for every `T > 0` some datum `x ∈ D(L)` with `E = 0`, `B = 0` has `e^{tL} x` leaving the
constraint at some `t ∈ [0, T]`, and the residuals `dist(ξₕ(t), K)` of the discrete
solutions of every constrained FEEC discretization `F` tend to `dist(e^{tL} x, K) > 0`. Item (4)
of the constrained FEEC theorem, non-reducing branch, through the parity grading of the window. -/
theorem potential_residual (F : ConstrainedFEEC H κ) (hd : ∃ σ : (H.d 0 1).domain, H.d 0 1 σ ≠ 0)
    {T : ℝ} (hT : 0 < T) :
    ∃ x : H.wave.domain, (x : PiLp 2 W) ∈ potential 𝕜 W ∧ ∃ t ∈ Icc 0 T,
      H.waveGroup.S t x ∉ potential 𝕜 W ∧
      0 < infDist (H.waveGroup.S t x) (potential 𝕜 W : Set (PiLp 2 W)) ∧
      Tendsto (fun h => infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t))
        (potential 𝕜 W : Set (PiLp 2 W))) F.l
        (𝓝 (infDist (H.waveGroup.S t x) (potential 𝕜 W : Set (PiLp 2 W)))) ∧
      ∀ᶠ h in F.l, infDist (H.waveGroup.S t x) (potential 𝕜 W : Set (PiLp 2 W)) / 2 <
        infDist (H.totalD.graphFst (F.discrete h (waveLift H x) t))
          (potential 𝕜 W : Set (PiLp 2 W)) :=
  residual_not_isReducing_of_grading F isClosed_potential (fun _ _ h => ComplexShape.window_parity h)
    (fun _ hx => reversal_mem_totalSub hx) (dense_potential H) (not_isReducing_potential H hd) hT

end PotentialConstraint

/-! ### The torus: spectral Galerkin -/

section Torus

open Models.Torus.DeRham

variable (d : Type*) [Fintype d] [LinearOrder d]

theorem torus_bound : ∃ C, ∀ (N k : ℕ) (x : L2Form d k), ‖(bandProj d N).π k x‖ ≤ C * ‖x‖ :=
  ⟨1, fun N k x => by
    rw [one_mul, bandProj_apply]; exact Submodule.norm_starProjection_apply_le _ x⟩

theorem torus_dense : ∀ (k : ℕ) (y : L2Form d k) (ε : ℝ), 0 < ε →
    ∀ᶠ N in atTop, ∃ v ∈ (bandSubcomplex d N).V k, ‖y - v‖ < ε := fun k y ε hε => by
  have h := Fourier.tendsto_starProjection_band
    (Fourier.Torus.symbolComplex (Fourier.Exterior.deRham d))
    (fun N => (Fourier.Torus.finite_bandN N).measurableSet) Fourier.Torus.bandN_mono
    Fourier.Torus.exists_mem_bandN k y
  filter_upwards [(tendsto_iff_norm_sub_tendsto_zero.1 h).eventually (gt_mem_nhds hε)] with N hN
  exact ⟨_, Submodule.starProjection_apply_mem _ _, by rwa [norm_sub_rev]⟩

/-- **Maxwell's equations on the torus `𝕋ᵈ`** (degree `a`; `d = 3`, `a = 0` is the classical
system) with the **spectral Galerkin** spaces of band-limited forms `|n|_∞ ≤ N` and the Fourier
truncations, as a constrained FEEC discretization with the Gauss laws. -/
def torus (a : ℕ) : ConstrainedFEEC ((complex d).window a 3) ℕ :=
  feec (complex d) a atTop (bandSubcomplex d) (bandProj d) (torus_bound d) (torus_dense d)

variable {d} {a : ℕ}

theorem torus_wellPosed {x : PiLp 2 fun i : Fin 3 => L2Form d (a + i)}
    (hx : x ∈ ((complex d).window a 3).wave.domain) (T : ℝ) :
    Evolution.IsClassicalSolution ((complex d).window a 3).wave (Icc 0 T) 0
        (fun t => ((complex d).window a 3).waveGroup.S t x) ∧
      ∀ t, ‖((complex d).window a 3).waveGroup.S t x‖ = ‖x‖ :=
  ⟨(constrainedFEEC_wellPosed hx T).1, (constrainedFEEC_wellPosed hx T).2.2.2⟩

/-- **The Gauss laws propagate on the torus** for all data and times. -/
theorem torus_gauss_propagates : ∀ t, ∀ x ∈ windowGauss (complex d) a,
    ((complex d).window a 3).waveGroup.S t x ∈ windowGauss (complex d) a :=
  (torus d a).constrainedFEEC_of_approxFEEC.2.1.1 (isReducing_windowGauss _ a)

/-- **Convergence of the spectral Galerkin Maxwell solutions on the torus.** -/
theorem torus_converges (T : ℝ) (x : ((complex d).window a 3).wave.domain) :
    TendstoUniformlyOn (fun N t => ((complex d).window a 3).totalD.graphFst
        ((torus d a).discrete N (waveLift _ x) t))
      (fun t => ((complex d).window a 3).waveGroup.S t x) atTop (Icc 0 T) :=
  ((torus d a).constrainedFEEC_of_approxFEEC.2.2.1 T).1 x

/-- **The Gauss-law residual of the spectral Galerkin solutions on the torus** is bounded by
the error and tends to `0`. -/
theorem torus_residual (x : ((complex d).window a 3).wave.domain)
    (hxK : (x : PiLp 2 _) ∈ windowGauss (complex d) a) (T : ℝ) :
    (∀ N t, infDist (((complex d).window a 3).totalD.graphFst
        ((torus d a).discrete N (waveLift _ x) t)) (windowGauss (complex d) a : Set _) ≤
      ‖((complex d).window a 3).waveGroup.S t x - ((complex d).window a 3).totalD.graphFst
        ((torus d a).discrete N (waveLift _ x) t)‖) ∧
    TendstoUniformlyOn (fun N t => infDist (((complex d).window a 3).totalD.graphFst
        ((torus d a).discrete N (waveLift _ x) t)) (windowGauss (complex d) a : Set _))
      (fun _ => 0) atTop (Icc 0 T) :=
  (torus d a).constrainedFEEC_of_approxFEEC.2.2.2.2.1 (isReducing_windowGauss _ a)
    x hxK T

/-- The de Rham symbol `d_ξ = i ξ ∧ ·` is injective on `0`-forms for `ξ ≠ 0`. -/
theorem deRham_m_zero_one_ne_zero {ξ : EuclideanSpace ℝ d} (hξ : ξ ≠ 0)
    {v : Fourier.Exterior.Form ℂ d 0} (hv : v ≠ 0) : (Fourier.Exterior.deRham d).m 0 1 ξ v ≠ 0 := by
  intro h
  refine hv (Fourier.Exterior.eq_zero_of_koszul_eq_zero_of_contr_eq_zero hξ ?_ ?_)
  · have e : (Fourier.Exterior.deRham d).m 0 1 ξ = Complex.I • Fourier.Exterior.koszulDeg 0 ξ :=
      Fourier.Exterior.deRham_m_succ 0 ξ
    rw [e, _root_.smul_apply, smul_eq_zero] at h
    exact h.resolve_left Complex.I_ne_zero
  · ext s
    exact Fourier.Exterior.contr_ext_eq_zero ξ 0 v (by omega)

/-- **The gradient on `𝕋ᵈ` is not zero** (`d ≠ ∅`): the Fourier mode `e^{2πi x_j}` has
`d e^{2πi x_j} ≠ 0`. -/
theorem torus_exists_d_ne_zero [Nonempty d] :
    ∃ σ : (((complex d).window 0 3).d 0 1).domain, ((complex d).window 0 3).d 0 1 σ ≠ 0 := by
  obtain ⟨j⟩ := ‹Nonempty d›
  set q : d → ℤ := Pi.single j 1
  have hq : q ≠ 0 := fun h => by simpa [q] using congrFun h j
  set v : Fourier.Exterior.Form ℂ d 0 := EuclideanSpace.single ⟨∅, Finset.card_empty⟩ 1
  have hv : v ≠ 0 := by simp [v]
  set u : L2Form d 0 :=
    lp.equivLpCount ℂ (d → ℤ) (Fourier.Exterior.Form ℂ d 0) 2 (lp.single 2 q v)
  have hu : ∀ p, (u : (d → ℤ) → Fourier.Exterior.Form ℂ d 0) p = if p = q then v else 0 :=
    fun p => by
      rw [lp.coeFn_equivLpCount, lp.single_apply]
      split_ifs with h
      · subst h; simp
      · simp [Pi.single, Function.update, h]
  have hband : u ∈ (bandSubcomplex d 1).V 0 := by
    refine (Fourier.mem_band_iff
      (S := Fourier.Torus.symbolComplex (Fourier.Exterior.deRham d))).2
      (MeasureTheory.ae_of_all _ fun p hp => ?_)
    rw [hu]
    split_ifs with hpq
    · subst hpq
      refine absurd (fun i => ?_) hp
      by_cases hi : i = j
      · subst hi; simp [q]
      · simp [q, hi]
    · rfl
  have hdom : u ∈ ((complex d).d 0 1).domain := (bandSubcomplex d 1).le_domain 0 1 hband
  refine ⟨⟨u, hdom⟩, fun h0 => ?_⟩
  have hae := (Fourier.Torus.symbolComplex (Fourier.Exterior.deRham d)).coeFn_d (i := 0) (j := 1)
    ⟨u, hdom⟩
  change (complex d).d 0 1 ⟨u, hdom⟩ = 0 at h0
  change ((complex d).d 0 1 ⟨u, hdom⟩ : (d → ℤ) → Fourier.Exterior.Form ℂ d 1) =ᵐ[_] _ at hae
  rw [h0] at hae
  have h1 := (MeasureTheory.Lp.coeFn_zero (Fourier.Exterior.Form ℂ d 1) 2
    (MeasureTheory.Measure.count : MeasureTheory.Measure (d → ℤ))).symm.trans hae
  have h2 := MeasureTheory.Measure.ae_count_iff.1 h1 q
  simp only [Pi.zero_apply, hu, ↓reduceIte, Fourier.Torus.symbolComplex_m] at h2
  exact deRham_m_zero_one_ne_zero (fun h => hq (Fourier.Torus.freq_eq_zero_iff.1 h)) hv h2.symm

/-- **The vanishing-field constraint does not reduce Maxwell's operator on `𝕋ᵈ`** (`d ≠ ∅`,
degree `0`). -/
theorem torus_not_isReducing_potential [Nonempty d] :
    ¬ ((complex d).window 0 3).wave.IsReducing (potential ℂ fun i : Fin 3 => L2Form d (0 + i)) :=
  not_isReducing_potential _ torus_exists_d_ne_zero

/-- **Item (4), non-reducing branch, on `𝕋ᵈ`**: for the vanishing-field constraint `E = 0`,
`B = 0`, for every `T > 0` some datum in `D(L) ∩ K` leaves `K` at some `t ∈ [0, T]`, and the
residuals of the spectral Galerkin solutions tend to a positive limit. -/
theorem torus_potential_residual [Nonempty d] {T : ℝ} (hT : 0 < T) :
    ∃ x : ((complex d).window 0 3).wave.domain,
      (x : PiLp 2 _) ∈ potential ℂ (fun i : Fin 3 => L2Form d (0 + i)) ∧ ∃ t ∈ Icc 0 T,
      ((complex d).window 0 3).waveGroup.S t x ∉ potential ℂ (fun i : Fin 3 => L2Form d (0 + i)) ∧
      0 < infDist (((complex d).window 0 3).waveGroup.S t x)
        (potential ℂ (fun i : Fin 3 => L2Form d (0 + i)) : Set _) ∧
      Tendsto (fun N => infDist (((complex d).window 0 3).totalD.graphFst
          ((torus d 0).discrete N (waveLift _ x) t))
          (potential ℂ (fun i : Fin 3 => L2Form d (0 + i)) : Set _)) atTop
        (𝓝 (infDist (((complex d).window 0 3).waveGroup.S t x)
          (potential ℂ (fun i : Fin 3 => L2Form d (0 + i)) : Set _))) ∧
      ∀ᶠ N in atTop, infDist (((complex d).window 0 3).waveGroup.S t x)
          (potential ℂ (fun i : Fin 3 => L2Form d (0 + i)) : Set _) / 2 <
        infDist (((complex d).window 0 3).totalD.graphFst
          ((torus d 0).discrete N (waveLift _ x) t))
          (potential ℂ (fun i : Fin 3 => L2Form d (0 + i)) : Set _) :=
  potential_residual (torus d 0) torus_exists_d_ne_zero hT

end Torus

/-! ### The cube: Whitney forms, perfect magnetic and electric conductors -/

section Cube

open Models.Cube Feec.Domain Feec.ExteriorFibre

variable (n : ℕ) [NeZero n]

/-- The smoothed cochain projections onto the Whitney complexes of the cube meshes. -/
def cubeProj (N : ℕ) : (FEM.whitney n N).CochainProjection :=
  (FEM.smoothingEstimates_exists (n := n)).choose_spec.choose_spec.proj N

theorem cubeProj_bound : ∃ C, ∀ (N : ℕ) (k : ℤ) (x : L2F ℝ (FEM.cubeDomain n) (formIdx n k)),
    ‖(cubeProj n N).π k x‖ ≤ C * ‖x‖ :=
  ⟨_, fun N k x => (FEM.smoothingEstimates_exists (n := n)).choose_spec.choose_spec.norm_proj_le
    N k x⟩

theorem cube_dense : ∀ (k : ℤ) (y : L2F ℝ (FEM.cubeDomain n) (formIdx n k)) (ε : ℝ), 0 < ε →
    ∀ᶠ N in atTop, ∃ v ∈ (FEM.whitney n N).V k, ‖y - v‖ < ε := fun k y _ hε =>
  (FEM.eventually_exists_whitney_near k y hε).mono fun _ ⟨v, hv, h1, _⟩ => ⟨v, hv, h1⟩

/-- **Maxwell's equations with a perfect magnetic conductor on the cube** `Q = (0, ½)ⁿ`
(degree `a`; `n = 3`, `a = 0` is the system `HΛ⁰(Q) → HΛ¹(Q) → L²Λ²(Q)` of
`Feec.Maxwell.CubeFEM`), discretized by the lowest-order Whitney forms of the Freudenthal meshes
with the smoothed projections, as a constrained FEEC discretization with the Gauss laws. -/
def cubePMC (a : ℤ) : ConstrainedFEEC ((FEM.complex n).window a 3) ℕ :=
  feec (FEM.complex n) a atTop (FEM.whitney n) (cubeProj n) (cubeProj_bound n) (cube_dense n)

/-- The `O(h)` rate class of `C²` solutions with bound `Λ` on `[0, T]` (`FEM.IsC2Form`). -/
abbrev cubePMCRate (a : ℤ) (T Λ : ℝ) (hΛ : 0 ≤ Λ) : (cubePMC n a).RateClass T :=
  regRate (cubeProj_bound n) (cube_dense n) T (fun k x => FEM.IsC2Form k Λ x) (FEM.interpBound n)
    FEM.meshSize Λ (fun N _ _ hx => hx.exists_mem_whitney_le hΛ N) (FEM.interpBound_nonneg n) hΛ
    fun N => (FEM.meshSize_pos N).le

/-- The smoothed cochain projections onto the Whitney complexes with vanishing boundary DOFs. -/
def cubeProjMin (N : ℕ) : (FEM.whitneyMin n N).CochainProjection :=
  (FEM.smoothingEstimatesMin_exists (n := n)).choose_spec.choose_spec.proj N

theorem cubeProjMin_bound : ∃ C, ∀ (N : ℕ) (k : ℤ) (x : L2F ℝ (FEM.cubeDomain n) (formIdx n k)),
    ‖(cubeProjMin n N).π k x‖ ≤ C * ‖x‖ :=
  ⟨_, fun N k x =>
    (FEM.smoothingEstimatesMin_exists (n := n)).choose_spec.choose_spec.norm_proj_le N k x⟩

theorem cube_denseMin : ∀ (k : ℤ) (y : L2F ℝ (FEM.cubeDomain n) (formIdx n k)) (ε : ℝ), 0 < ε →
    ∀ᶠ N in atTop, ∃ v ∈ (FEM.whitneyMin n N).V k, ‖y - v‖ < ε := fun k y _ hε =>
  (FEM.eventually_exists_whitneyMin_near k y hε).mono fun _ ⟨v, hv, h1, _⟩ => ⟨v, hv, h1⟩

/-- **Maxwell's equations with a perfect electric conductor on the cube** (vanishing tangential
traces: `H̊Λ⁰(Q) → H̊Λ¹(Q) → L²Λ²(Q)` for `n = 3`, `a = 0`), discretized by the Whitney forms with
vanishing boundary DOFs, as a constrained FEEC discretization with the Gauss laws. -/
def cubePEC (a : ℤ) : ConstrainedFEEC ((FEM.complexMin n).window a 3) ℕ :=
  feec (FEM.complexMin n) a atTop (FEM.whitneyMin n) (cubeProjMin n) (cubeProjMin_bound n)
    (cube_denseMin n)

/-- The `O(h)` rate class of `C²` solutions vanishing outside `Q` (`FEM.IsC2FormMin`). -/
abbrev cubePECRate (a : ℤ) (T Λ : ℝ) (hΛ : 0 ≤ Λ) : (cubePEC n a).RateClass T :=
  regRate (cubeProjMin_bound n) (cube_denseMin n) T (fun k x => FEM.IsC2FormMin k Λ x)
    (FEM.interpBound n) FEM.meshSize Λ (fun N _ _ hx => hx.exists_mem_whitneyMin_le hΛ N)
    (FEM.interpBound_nonneg n) hΛ fun N => (FEM.meshSize_pos N).le

variable {n} {a : ℤ}

omit [NeZero n] in
/-- **Well-posedness** (perfect magnetic conductor, cube): for `x ∈ D(L)`, `t ↦ e^{tL} x` is a
classical solution on `[0, T]` and conserves energy. [QuennevilleBelair2015], Thm 4.6 -/
theorem cubePMC_wellPosed {x} (hx : x ∈ ((FEM.complex n).window a 3).wave.domain) (T : ℝ) :
    Evolution.IsClassicalSolution ((FEM.complex n).window a 3).wave (Icc 0 T) 0
        (fun t => ((FEM.complex n).window a 3).waveGroup.S t x) ∧
      ∀ t, ‖((FEM.complex n).window a 3).waveGroup.S t x‖ = ‖x‖ :=
  ⟨(constrainedFEEC_wellPosed hx T).1, (constrainedFEEC_wellPosed hx T).2.2.2⟩

/-- **The Gauss laws propagate** (perfect magnetic conductor, cube) for all data and all times `t ∈
ℝ`. [QuennevilleBelair2015], Prop. 4.16 -/
theorem cubePMC_gauss_propagates :
    ∀ t, ∀ x ∈ windowGauss (FEM.complex n) a,
      ((FEM.complex n).window a 3).waveGroup.S t x ∈ windowGauss (FEM.complex n) a :=
  (cubePMC n a).constrainedFEEC_of_approxFEEC.2.1.1 (isReducing_windowGauss _ a)

/-- **Convergence of the semi-discrete solutions** (perfect magnetic conductor, cube), uniformly on
`[0, T]`, for `D(L)` data and `ξₕ(0) = Pₕ x`. [QuennevilleBelair2015], Thm 4.14 -/
theorem cubePMC_converges (T : ℝ) (x : ((FEM.complex n).window a 3).wave.domain) :
    TendstoUniformlyOn
      (fun N t => ((FEM.complex n).window a 3).totalD.graphFst
        ((cubePMC n a).discrete N (waveLift _ x) t))
      (fun t => ((FEM.complex n).window a 3).waveGroup.S t x) atTop (Icc 0 T) :=
  ((cubePMC n a).constrainedFEEC_of_approxFEEC.2.2.1 T).1 x

/-- **The Gauss-law residual** (perfect magnetic conductor, cube) of the discrete solution is
bounded by the error and tends to `0` uniformly on `[0, T]`. -/
theorem cubePMC_residual (x : ((FEM.complex n).window a 3).wave.domain)
    (hxK : (x : PiLp 2 _) ∈ windowGauss (FEM.complex n) a) (T : ℝ) :
    (∀ N t, infDist (((FEM.complex n).window a 3).totalD.graphFst
        ((cubePMC n a).discrete N (waveLift _ x) t))
        (windowGauss (FEM.complex n) a : Set _) ≤
      ‖((FEM.complex n).window a 3).waveGroup.S t x -
        ((FEM.complex n).window a 3).totalD.graphFst
          ((cubePMC n a).discrete N (waveLift _ x) t)‖) ∧
    TendstoUniformlyOn
      (fun N t => infDist (((FEM.complex n).window a 3).totalD.graphFst
        ((cubePMC n a).discrete N (waveLift _ x) t))
        (windowGauss (FEM.complex n) a : Set _))
      (fun _ => 0) atTop (Icc 0 T) :=
  (cubePMC n a).constrainedFEEC_of_approxFEEC.2.2.2.2.1 (isReducing_windowGauss _ a)
    x hxK T

/-- **The `O(h)` rate for `C²` solutions** (perfect magnetic conductor, cube): if the components of
`e^{tL} x` and `e^{tL} L x` are `C²` forms (`FEM.IsC2Form`) with bound `Λ` on `[0, T]`, then `‖ξ(t)
- ξₕ(t)‖ ≤ (1 + C_P) (1 + t)² · 12 (Σᵢ B_{a+i}) h_N Λ`. [QuennevilleBelair2015], Thm 4.14;
[Arnold2018], Ch. 7 -/
theorem cubePMC_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (cubePMCRate n a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖((FEM.complex n).window a 3).waveGroup.S t x -
        ((FEM.complex n).window a 3).totalD.graphFst
          ((cubePMC n a).discrete N (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst ((FEM.complex n).window a 3)) * (1 + t) ^ 2 *
        (12 * (∑ i : Fin 3, FEM.interpBound n (a + i)) * FEM.meshSize N * Λ) :=
  rate_regRate _ _ hx N ht

/-- **The `O(h)` rate of the Gauss-law residual for `C²` solutions** (perfect magnetic conductor,
cube). -/
theorem cubePMC_residual_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (cubePMCRate n a T Λ hΛ).Data) (hxK : x ∈ windowGauss (FEM.complex n) a)
    (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    infDist (((FEM.complex n).window a 3).totalD.graphFst
        ((cubePMC n a).discrete N (waveLift _ ⟨x, hx.1⟩) t))
        (windowGauss (FEM.complex n) a : Set _) ≤
      (1 + ellipticConst ((FEM.complex n).window a 3)) * (1 + t) ^ 2 *
        (12 * (∑ i : Fin 3, FEM.interpBound n (a + i)) * FEM.meshSize N * Λ) :=
  residual_rate_regRate _ _ hx hxK N ht

omit [NeZero n] in
/-- **Well-posedness** (perfect electric conductor, cube): for `x ∈ D(L)`, `t ↦ e^{tL} x` is a
classical solution on `[0, T]` and conserves energy. [QuennevilleBelair2015], Thm 4.6 -/
theorem cubePEC_wellPosed {x} (hx : x ∈ ((FEM.complexMin n).window a 3).wave.domain) (T : ℝ) :
    Evolution.IsClassicalSolution ((FEM.complexMin n).window a 3).wave (Icc 0 T) 0
        (fun t => ((FEM.complexMin n).window a 3).waveGroup.S t x) ∧
      ∀ t, ‖((FEM.complexMin n).window a 3).waveGroup.S t x‖ = ‖x‖ :=
  ⟨(constrainedFEEC_wellPosed hx T).1, (constrainedFEEC_wellPosed hx T).2.2.2⟩

/-- **The Gauss laws propagate** (perfect electric conductor, cube) for all data and all times `t ∈
ℝ`. [QuennevilleBelair2015], Prop. 4.16 -/
theorem cubePEC_gauss_propagates :
    ∀ t, ∀ x ∈ windowGauss (FEM.complexMin n) a,
      ((FEM.complexMin n).window a 3).waveGroup.S t x ∈ windowGauss (FEM.complexMin n) a :=
  (cubePEC n a).constrainedFEEC_of_approxFEEC.2.1.1 (isReducing_windowGauss _ a)

/-- **Convergence of the semi-discrete solutions** (perfect electric conductor, cube), uniformly on
`[0, T]`, for `D(L)` data and `ξₕ(0) = Pₕ x`. [QuennevilleBelair2015], Thm 4.14 -/
theorem cubePEC_converges (T : ℝ) (x : ((FEM.complexMin n).window a 3).wave.domain) :
    TendstoUniformlyOn
      (fun N t => ((FEM.complexMin n).window a 3).totalD.graphFst
        ((cubePEC n a).discrete N (waveLift _ x) t))
      (fun t => ((FEM.complexMin n).window a 3).waveGroup.S t x) atTop (Icc 0 T) :=
  ((cubePEC n a).constrainedFEEC_of_approxFEEC.2.2.1 T).1 x

/-- **The Gauss-law residual** (perfect electric conductor, cube) of the discrete solution is
bounded by the error and tends to `0` uniformly on `[0, T]`. -/
theorem cubePEC_residual (x : ((FEM.complexMin n).window a 3).wave.domain)
    (hxK : (x : PiLp 2 _) ∈ windowGauss (FEM.complexMin n) a) (T : ℝ) :
    (∀ N t, infDist (((FEM.complexMin n).window a 3).totalD.graphFst
        ((cubePEC n a).discrete N (waveLift _ x) t))
        (windowGauss (FEM.complexMin n) a : Set _) ≤
      ‖((FEM.complexMin n).window a 3).waveGroup.S t x -
        ((FEM.complexMin n).window a 3).totalD.graphFst
          ((cubePEC n a).discrete N (waveLift _ x) t)‖) ∧
    TendstoUniformlyOn
      (fun N t => infDist (((FEM.complexMin n).window a 3).totalD.graphFst
        ((cubePEC n a).discrete N (waveLift _ x) t))
        (windowGauss (FEM.complexMin n) a : Set _))
      (fun _ => 0) atTop (Icc 0 T) :=
  (cubePEC n a).constrainedFEEC_of_approxFEEC.2.2.2.2.1 (isReducing_windowGauss _ a)
    x hxK T

/-- **The `O(h)` rate for `C²` solutions** (perfect electric conductor, cube): if the components of
`e^{tL} x` and `e^{tL} L x` are `C²` forms vanishing outside `Q` (`FEM.IsC2FormMin`) with bound `Λ`
on `[0, T]`, then `‖ξ(t) - ξₕ(t)‖ ≤ (1 + C_P) (1 + t)² · 12 (Σᵢ B_{a+i}) h_N Λ`.
[QuennevilleBelair2015], Thm 4.14; [Arnold2018], Ch. 7 -/
theorem cubePEC_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (cubePECRate n a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖((FEM.complexMin n).window a 3).waveGroup.S t x -
        ((FEM.complexMin n).window a 3).totalD.graphFst
          ((cubePEC n a).discrete N (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst ((FEM.complexMin n).window a 3)) * (1 + t) ^ 2 *
        (12 * (∑ i : Fin 3, FEM.interpBound n (a + i)) * FEM.meshSize N * Λ) :=
  rate_regRate _ _ hx N ht

/-- **The `O(h)` rate of the Gauss-law residual for `C²` solutions** (perfect electric conductor,
cube). -/
theorem cubePEC_residual_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (cubePECRate n a T Λ hΛ).Data) (hxK : x ∈ windowGauss (FEM.complexMin n) a)
    (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    infDist (((FEM.complexMin n).window a 3).totalD.graphFst
        ((cubePEC n a).discrete N (waveLift _ ⟨x, hx.1⟩) t))
        (windowGauss (FEM.complexMin n) a : Set _) ≤
      (1 + ellipticConst ((FEM.complexMin n).window a 3)) * (1 + t) ^ 2 *
        (12 * (∑ i : Fin 3, FEM.interpBound n (a + i)) * FEM.meshSize N * Λ) :=
  residual_rate_regRate _ _ hx hxK N ht

omit [NeZero n] in
/-- The zero form is a `C²` form with every bound `Λ ≥ 0`. -/
theorem isC2Form_zero (k : ℤ) {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    FEM.IsC2Form k Λ (0 : L2F ℝ (FEM.cubeDomain n) (formIdx n k)) := by
  rcases lt_or_ge k 0 with hk | hk
  · exact Or.inl hk
  · have e : FiniteElement.extDeriv (0 : FiniteElement.FormField n) = 0 :=
      FiniteElement.extDeriv_const (0 : Finset (Fin n) → ℝ)
    refine Or.inr ⟨k.toNat, by omega, 0, contDiff_const, fun y t _ => rfl, fun y _ => ?_,
      fun y _ => ?_, (_root_.map_zero _).symm⟩
    · simp [hΛ]
    · rw [e]; simp [hΛ]

omit [NeZero n] in
/-- The zero form is a `C²` form vanishing outside `Q` with every bound `Λ ≥ 0`. -/
theorem isC2FormMin_zero (k : ℤ) {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    FEM.IsC2FormMin k Λ (0 : L2F ℝ (FEM.cubeDomain n) (formIdx n k)) := by
  rcases lt_or_ge k 0 with hk | hk
  · exact Or.inl hk
  · have e : FiniteElement.extDeriv (0 : FiniteElement.FormField n) = 0 :=
      FiniteElement.extDeriv_const (0 : Finset (Fin n) → ℝ)
    refine Or.inr ⟨k.toNat, by omega, 0, contDiff_const, fun y t _ => rfl, fun y _ => rfl,
      fun y _ => ?_, fun y _ => ?_, (_root_.map_zero _).symm⟩
    · simp [hΛ]
    · rw [e]; simp [hΛ]

/-- Non-vacuity of the cube rate classes (the zero datum). -/
theorem zero_mem_cubePMCRate {T Λ : ℝ} (hΛ : 0 ≤ Λ) :
    (0 : PiLp 2 _) ∈ (cubePMCRate n a T Λ hΛ).Data :=
  zero_mem_regRate _ _ fun k => isC2Form_zero k hΛ

theorem zero_mem_cubePECRate {T Λ : ℝ} (hΛ : 0 ≤ Λ) :
    (0 : PiLp 2 _) ∈ (cubePECRate n a T Λ hΛ).Data :=
  zero_mem_regRate _ _ fun k => isC2FormMin_zero k hΛ

/-- **`Feec.Maxwell.CubeFEM.pmc_tendstoUniformlyOn` at `t₀ = 0`, from the constrained FEEC
theorem**: the semi-discrete Lagrange–Nédélec–Raviart–Thomas solutions with `ξₕ(0) = Pₕ x`
converge to `e^{tL} x` uniformly on `[0, t₁]`. -/
theorem cubePMC_tendstoUniformlyOn (t₁ : ℝ) (x : ((FEM.complex 3).window 0 3).wave.domain) :
    ∃ ξh ξh' : ℕ → ℝ → ((FEM.complex 3).window 0 3).totalD.GraphSpace,
      (∀ N, IsSemidiscreteSolution (((FEM.whitney 3 N).window 0 3).graphSub) (Icc 0 t₁)
        (ξh N) (ξh' N)) ∧
      (∀ N, ξh N 0 = ellipticProjection (((FEM.whitney 3 N).window 0 3).graphSub)
        (waveLift _ x)) ∧
      TendstoUniformlyOn (fun N t => ((FEM.complex 3).window 0 3).totalD.graphFst (ξh N t))
        (fun t => ((FEM.complex 3).window 0 3).waveGroup.S t x) atTop (Icc 0 t₁) :=
  ⟨fun N => (cubePMC 3 0).discrete N _, fun N => (cubePMC 3 0).discreteDeriv N _,
    fun N => (cubePMC 3 0).isSemidiscreteSolution_discrete N _ _,
    fun N => (cubePMC 3 0).discrete_zero N _, ((cubePMC 3 0).constrainedFEEC_of_approxFEEC.2.2.1
      t₁).1 x⟩

/-- **`Feec.Maxwell.CubeFEM.pec_tendstoUniformlyOn` at `t₀ = 0`, from the constrained FEEC
theorem.** -/
theorem cubePEC_tendstoUniformlyOn (t₁ : ℝ) (x : ((FEM.complexMin 3).window 0 3).wave.domain) :
    ∃ ξh ξh' : ℕ → ℝ → ((FEM.complexMin 3).window 0 3).totalD.GraphSpace,
      (∀ N, IsSemidiscreteSolution (((FEM.whitneyMin 3 N).window 0 3).graphSub) (Icc 0 t₁)
        (ξh N) (ξh' N)) ∧
      (∀ N, ξh N 0 = ellipticProjection (((FEM.whitneyMin 3 N).window 0 3).graphSub)
        (waveLift _ x)) ∧
      TendstoUniformlyOn (fun N t => ((FEM.complexMin 3).window 0 3).totalD.graphFst (ξh N t))
        (fun t => ((FEM.complexMin 3).window 0 3).waveGroup.S t x) atTop (Icc 0 t₁) :=
  ⟨fun N => (cubePEC 3 0).discrete N _, fun N => (cubePEC 3 0).discreteDeriv N _,
    fun N => (cubePEC 3 0).isSemidiscreteSolution_discrete N _ _,
    fun N => (cubePEC 3 0).discrete_zero N _, ((cubePEC 3 0).constrainedFEEC_of_approxFEEC.2.2.1
      t₁).1 x⟩

end Cube

/-! ### Parallelepipeds -/

section Parallelepiped

open Models.Cube Feec.Domain Feec.ExteriorFibre
open Models.Parallelepiped (complex complexMin whitney whitneyMin domain IsC2Form IsC2FormMin
  rateBound rateBound_nonneg smoothedProjection_uniform smoothedProjection_uniform_min
  eventually_exists_whitney_near eventually_exists_whitneyMin_near)

variable {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ)

/-- The transported smoothed cochain projections onto the Whitney complexes of `T(M_N)`. -/
def paraProj (N : ℕ) : (whitney A hA b N).CochainProjection :=
  (smoothedProjection_uniform A hA b).choose_spec.choose N

theorem paraProj_bound : ∃ C, ∀ (N : ℕ) (k : ℤ) (x : L2F ℝ (domain A b) (formIdx n k)),
    ‖(paraProj A hA b N).π k x‖ ≤ C * ‖x‖ :=
  ⟨_, (smoothedProjection_uniform A hA b).choose_spec.choose_spec.2.1⟩

theorem para_dense : ∀ (k : ℤ) (y : L2F ℝ (domain A b) (formIdx n k)) (ε : ℝ), 0 < ε →
    ∀ᶠ N in atTop, ∃ v ∈ (whitney A hA b N).V k, ‖y - v‖ < ε := fun k y _ hε =>
  (eventually_exists_whitney_near A hA b k y hε).mono fun _ ⟨v, hv, h1, _⟩ => ⟨v, hv, h1⟩

/-- **Maxwell's equations with a perfect magnetic conductor on the parallelepiped**
`Ω = A · Q + b` (every box), with the Whitney forms of the image Freudenthal meshes, as a
constrained FEEC discretization with the Gauss laws. -/
def paraPMC (a : ℤ) : ConstrainedFEEC ((complex A b).window a 3) ℕ :=
  feec (complex A b) a atTop (whitney A hA b) (paraProj A hA b) (paraProj_bound A hA b)
    (para_dense A hA b)

/-- The `O(h)` rate class of `C²` solutions on `Ω` (`Parallelepiped.IsC2Form`). -/
abbrev paraPMCRate (a : ℤ) (T Λ : ℝ) (hΛ : 0 ≤ Λ) : (paraPMC A hA b a).RateClass T :=
  regRate (paraProj_bound A hA b) (para_dense A hA b) T (fun k x => IsC2Form A hA b k Λ x)
    (rateBound A) FEM.meshSize Λ (fun N _ _ hx => hx.exists_mem_whitney_le A hA b hΛ N)
    (rateBound_nonneg A) hΛ fun N => (FEM.meshSize_pos N).le

/-- The transported smoothed cochain projections with vanishing boundary DOFs. -/
def paraProjMin (N : ℕ) : (whitneyMin A hA b N).CochainProjection :=
  (smoothedProjection_uniform_min A hA b).choose_spec.choose N

theorem paraProjMin_bound : ∃ C, ∀ (N : ℕ) (k : ℤ) (x : L2F ℝ (domain A b) (formIdx n k)),
    ‖(paraProjMin A hA b N).π k x‖ ≤ C * ‖x‖ :=
  ⟨_, (smoothedProjection_uniform_min A hA b).choose_spec.choose_spec.2.1⟩

theorem para_denseMin : ∀ (k : ℤ) (y : L2F ℝ (domain A b) (formIdx n k)) (ε : ℝ), 0 < ε →
    ∀ᶠ N in atTop, ∃ v ∈ (whitneyMin A hA b N).V k, ‖y - v‖ < ε := fun k y _ hε =>
  (eventually_exists_whitneyMin_near A hA b k y hε).mono fun _ ⟨v, hv, h1, _⟩ => ⟨v, hv, h1⟩

/-- **Maxwell's equations with a perfect electric conductor on the parallelepiped** `Ω`, with the
Whitney forms with vanishing boundary DOFs. -/
def paraPEC (a : ℤ) : ConstrainedFEEC ((complexMin A b).window a 3) ℕ :=
  feec (complexMin A b) a atTop (whitneyMin A hA b) (paraProjMin A hA b)
    (paraProjMin_bound A hA b) (para_denseMin A hA b)

/-- The `O(h)` rate class of `C²` solutions vanishing outside `Ω`. -/
abbrev paraPECRate (a : ℤ) (T Λ : ℝ) (hΛ : 0 ≤ Λ) : (paraPEC A hA b a).RateClass T :=
  regRate (paraProjMin_bound A hA b) (para_denseMin A hA b) T
    (fun k x => IsC2FormMin A hA b k Λ x) (rateBound A) FEM.meshSize Λ
    (fun N _ _ hx => hx.exists_mem_whitneyMin_le A hA b hΛ N) (rateBound_nonneg A) hΛ
    fun N => (FEM.meshSize_pos N).le

variable {A hA b} {a : ℤ}

omit [NeZero n] in
/-- **Well-posedness** (perfect magnetic conductor, parallelepiped): for `x ∈ D(L)`, `t ↦ e^{tL} x`
is a classical solution on `[0, T]` and conserves energy. [QuennevilleBelair2015], Thm 4.6 -/
theorem paraPMC_wellPosed {x} (hx : x ∈ ((complex A b).window a 3).wave.domain) (T : ℝ) :
    Evolution.IsClassicalSolution ((complex A b).window a 3).wave (Icc 0 T) 0
        (fun t => ((complex A b).window a 3).waveGroup.S t x) ∧
      ∀ t, ‖((complex A b).window a 3).waveGroup.S t x‖ = ‖x‖ :=
  ⟨(constrainedFEEC_wellPosed hx T).1, (constrainedFEEC_wellPosed hx T).2.2.2⟩

omit [NeZero n] in
/-- **The Gauss laws propagate** (perfect magnetic conductor, parallelepiped) for all data and all
times `t ∈ ℝ`. [QuennevilleBelair2015], Prop. 4.16 -/
theorem paraPMC_gauss_propagates :
    ∀ t, ∀ x ∈ windowGauss (complex A b) a,
      ((complex A b).window a 3).waveGroup.S t x ∈ windowGauss (complex A b) a :=
  windowGauss_propagates (complex A b) a

/-- **Convergence of the semi-discrete solutions** (perfect magnetic conductor, parallelepiped),
uniformly on `[0, T]`, for `D(L)` data and `ξₕ(0) = Pₕ x`. [QuennevilleBelair2015], Thm 4.14 -/
theorem paraPMC_converges (T : ℝ) (x : ((complex A b).window a 3).wave.domain) :
    TendstoUniformlyOn
      (fun N t => ((complex A b).window a 3).totalD.graphFst
        ((paraPMC A hA b a).discrete N (waveLift _ x) t))
      (fun t => ((complex A b).window a 3).waveGroup.S t x) atTop (Icc 0 T) :=
  ((paraPMC A hA b a).constrainedFEEC_of_approxFEEC.2.2.1 T).1 x

/-- **The Gauss-law residual** (perfect magnetic conductor, parallelepiped) of the discrete solution
is bounded by the error and tends to `0` uniformly on `[0, T]`. -/
theorem paraPMC_residual (x : ((complex A b).window a 3).wave.domain)
    (hxK : (x : PiLp 2 _) ∈ windowGauss (complex A b) a) (T : ℝ) :
    (∀ N t, infDist (((complex A b).window a 3).totalD.graphFst
        ((paraPMC A hA b a).discrete N (waveLift _ x) t))
        (windowGauss (complex A b) a : Set _) ≤
      ‖((complex A b).window a 3).waveGroup.S t x -
        ((complex A b).window a 3).totalD.graphFst
          ((paraPMC A hA b a).discrete N (waveLift _ x) t)‖) ∧
    TendstoUniformlyOn
      (fun N t => infDist (((complex A b).window a 3).totalD.graphFst
        ((paraPMC A hA b a).discrete N (waveLift _ x) t))
        (windowGauss (complex A b) a : Set _))
      (fun _ => 0) atTop (Icc 0 T) :=
  (paraPMC A hA b a).constrainedFEEC_of_approxFEEC.2.2.2.2.1 (isReducing_windowGauss _ a)
    x hxK T

/-- **The `O(h)` rate for `C²` solutions** (perfect magnetic conductor, parallelepiped): if the
components of `e^{tL} x` and `e^{tL} L x` are `C²` forms on `cl Ω` (`Parallelepiped.IsC2Form`) with
bound `Λ` on `[0, T]`, then `‖ξ(t) - ξₕ(t)‖ ≤ (1 + C_P) (1 + t)² · 12 (Σᵢ B_{a+i}) h_N Λ`.
[QuennevilleBelair2015], Thm 4.14; [Arnold2018], Ch. 7 -/
theorem paraPMC_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (paraPMCRate A hA b a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖((complex A b).window a 3).waveGroup.S t x -
        ((complex A b).window a 3).totalD.graphFst
          ((paraPMC A hA b a).discrete N (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst ((complex A b).window a 3)) * (1 + t) ^ 2 *
        (12 * (∑ i : Fin 3, rateBound A (a + i)) * FEM.meshSize N * Λ) :=
  rate_regRate _ _ hx N ht

/-- **The `O(h)` rate of the Gauss-law residual for `C²` solutions** (perfect magnetic conductor,
parallelepiped). -/
theorem paraPMC_residual_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (paraPMCRate A hA b a T Λ hΛ).Data) (hxK : x ∈ windowGauss (complex A b) a)
    (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    infDist (((complex A b).window a 3).totalD.graphFst
        ((paraPMC A hA b a).discrete N (waveLift _ ⟨x, hx.1⟩) t))
        (windowGauss (complex A b) a : Set _) ≤
      (1 + ellipticConst ((complex A b).window a 3)) * (1 + t) ^ 2 *
        (12 * (∑ i : Fin 3, rateBound A (a + i)) * FEM.meshSize N * Λ) :=
  residual_rate_regRate _ _ hx hxK N ht

omit [NeZero n] in
/-- **Well-posedness** (perfect electric conductor, parallelepiped): for `x ∈ D(L)`, `t ↦ e^{tL} x`
is a classical solution on `[0, T]` and conserves energy. [QuennevilleBelair2015], Thm 4.6 -/
theorem paraPEC_wellPosed {x} (hx : x ∈ ((complexMin A b).window a 3).wave.domain) (T : ℝ) :
    Evolution.IsClassicalSolution ((complexMin A b).window a 3).wave (Icc 0 T) 0
        (fun t => ((complexMin A b).window a 3).waveGroup.S t x) ∧
      ∀ t, ‖((complexMin A b).window a 3).waveGroup.S t x‖ = ‖x‖ :=
  ⟨(constrainedFEEC_wellPosed hx T).1, (constrainedFEEC_wellPosed hx T).2.2.2⟩

omit [NeZero n] in
/-- **The Gauss laws propagate** (perfect electric conductor, parallelepiped) for all data and all
times `t ∈ ℝ`. [QuennevilleBelair2015], Prop. 4.16 -/
theorem paraPEC_gauss_propagates :
    ∀ t, ∀ x ∈ windowGauss (complexMin A b) a,
      ((complexMin A b).window a 3).waveGroup.S t x ∈ windowGauss (complexMin A b) a :=
  windowGauss_propagates (complexMin A b) a

/-- **Convergence of the semi-discrete solutions** (perfect electric conductor, parallelepiped),
uniformly on `[0, T]`, for `D(L)` data and `ξₕ(0) = Pₕ x`. [QuennevilleBelair2015], Thm 4.14 -/
theorem paraPEC_converges (T : ℝ) (x : ((complexMin A b).window a 3).wave.domain) :
    TendstoUniformlyOn
      (fun N t => ((complexMin A b).window a 3).totalD.graphFst
        ((paraPEC A hA b a).discrete N (waveLift _ x) t))
      (fun t => ((complexMin A b).window a 3).waveGroup.S t x) atTop (Icc 0 T) :=
  ((paraPEC A hA b a).constrainedFEEC_of_approxFEEC.2.2.1 T).1 x

/-- **The Gauss-law residual** (perfect electric conductor, parallelepiped) of the discrete solution
is bounded by the error and tends to `0` uniformly on `[0, T]`. -/
theorem paraPEC_residual (x : ((complexMin A b).window a 3).wave.domain)
    (hxK : (x : PiLp 2 _) ∈ windowGauss (complexMin A b) a) (T : ℝ) :
    (∀ N t, infDist (((complexMin A b).window a 3).totalD.graphFst
        ((paraPEC A hA b a).discrete N (waveLift _ x) t))
        (windowGauss (complexMin A b) a : Set _) ≤
      ‖((complexMin A b).window a 3).waveGroup.S t x -
        ((complexMin A b).window a 3).totalD.graphFst
          ((paraPEC A hA b a).discrete N (waveLift _ x) t)‖) ∧
    TendstoUniformlyOn
      (fun N t => infDist (((complexMin A b).window a 3).totalD.graphFst
        ((paraPEC A hA b a).discrete N (waveLift _ x) t))
        (windowGauss (complexMin A b) a : Set _))
      (fun _ => 0) atTop (Icc 0 T) :=
  (paraPEC A hA b a).constrainedFEEC_of_approxFEEC.2.2.2.2.1 (isReducing_windowGauss _ a)
    x hxK T

/-- **The `O(h)` rate for `C²` solutions** (perfect electric conductor, parallelepiped): if the
components of `e^{tL} x` and `e^{tL} L x` are `C²` forms vanishing outside `Ω`
(`Parallelepiped.IsC2FormMin`) with bound `Λ` on `[0, T]`, then `‖ξ(t) - ξₕ(t)‖ ≤ (1 + C_P) (1 + t)²
· 12 (Σᵢ B_{a+i}) h_N Λ`. [QuennevilleBelair2015], Thm 4.14; [Arnold2018], Ch. 7 -/
theorem paraPEC_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (paraPECRate A hA b a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖((complexMin A b).window a 3).waveGroup.S t x -
        ((complexMin A b).window a 3).totalD.graphFst
          ((paraPEC A hA b a).discrete N (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst ((complexMin A b).window a 3)) * (1 + t) ^ 2 *
        (12 * (∑ i : Fin 3, rateBound A (a + i)) * FEM.meshSize N * Λ) :=
  rate_regRate _ _ hx N ht

/-- **The `O(h)` rate of the Gauss-law residual for `C²` solutions** (perfect electric conductor,
parallelepiped). -/
theorem paraPEC_residual_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (paraPECRate A hA b a T Λ hΛ).Data) (hxK : x ∈ windowGauss (complexMin A b) a)
    (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    infDist (((complexMin A b).window a 3).totalD.graphFst
        ((paraPEC A hA b a).discrete N (waveLift _ ⟨x, hx.1⟩) t))
        (windowGauss (complexMin A b) a : Set _) ≤
      (1 + ellipticConst ((complexMin A b).window a 3)) * (1 + t) ^ 2 *
        (12 * (∑ i : Fin 3, rateBound A (a + i)) * FEM.meshSize N * Λ) :=
  residual_rate_regRate _ _ hx hxK N ht

end Parallelepiped

/-! ### Domains star-shaped with respect to a ball -/

section StarShaped

open Models.Cube Models.StarShaped Feec.Domain Feec.ExteriorFibre

/-- **The Poincaré inequality of a complex gives that of its Maxwell window**, in the form of
the discrete Poincaré theorem `constrainedFEEC_discretePoincare`. -/
theorem window_poincare {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
    [∀ i, InnerProductSpace ℝ (W i)] [∀ i, CompleteSpace (W i)]
    {H : HilbertComplex ℝ (ComplexShape.up ℤ) W} {cP : ℝ} (hP : HasPoincare H cP) (a : ℤ)
    {i j : Fin 3} (hij : (ComplexShape.window 3).Rel i j) (z : ((H.window a 3).d i j).domain)
    (hz : (z : W (a + i)) ∈ ((H.window a 3).cycles i)ᗮ) :
    ‖(z : W (a + i))‖ ≤ cP * ‖(H.window a 3).d i j z‖ := by
  have hrel : (ComplexShape.up ℤ).Rel (a + (i : ℕ)) (a + (j : ℕ)) := by
    simp only [ComplexShape.window_rel] at hij
    simp only [ComplexShape.up_Rel]; omega
  have e : (H.window a 3).cycles i = H.cycles (a + (i : ℕ)) := by
    unfold HilbertComplex.cycles
    rw [ComplexShape.next_eq' _ hij, ComplexShape.next_eq' _ hrel]; rfl
  exact hP _ _ hrel z (e ▸ hz)

variable {n : ℕ} [NeZero n] {D : StarDomain n} (M : MeshFamily D)

/-- The smoothed cochain projections onto the Whitney complexes of the mesh family. -/
def starProj (N : ℕ) : (M.whitney N).CochainProjection :=
  (M.exists_uniform_proj.choose_spec.2 N).choose

theorem starProj_bound : ∃ C, ∀ (N : ℕ) (k : ℤ) (x : L2F ℝ D.Ω (formIdx n k)),
    ‖(starProj M N).π k x‖ ≤ C * ‖x‖ :=
  ⟨_, fun N k x => (M.exists_uniform_proj.choose_spec.2 N).choose_spec.1 k x⟩

theorem star_dense : ∀ (k : ℤ) (y : L2F ℝ D.Ω (formIdx n k)) (ε : ℝ), 0 < ε →
    ∀ᶠ N in atTop, ∃ v ∈ (M.whitney N).V k, ‖y - v‖ < ε := fun k y _ hε =>
  (M.eventually_exists_whitney_near k y hε).mono fun _ ⟨v, hv, h1, _⟩ => ⟨v, hv, h1⟩

/-- **Maxwell's equations with a perfect magnetic conductor on a domain star-shaped with respect
to a ball**, with the Whitney forms of a uniformly shape-regular, quasi-uniform mesh family, as a
constrained FEEC discretization with the Gauss laws. No Poincaré inequality is needed. -/
def starPMC (a : ℤ) : ConstrainedFEEC (D.complex.window a 3) ℕ :=
  feec D.complex a atTop M.whitney (starProj M) (starProj_bound M) (star_dense M)

/-- The `O(h)` rate class of `C²` solutions on `Ω` (`StarDomain.IsC2Form`), in powers of the mesh
size `h_N` of the family. -/
abbrev starPMCRate (a : ℤ) (T Λ : ℝ) (hΛ : 0 ≤ Λ) : (starPMC M a).RateClass T :=
  regRate (starProj_bound M) (star_dense M) T (fun k x => D.IsC2Form k Λ x) M.interpBound
    (fun N => (M.mesh N).meshSize) Λ (fun N _ _ hx => M.exists_mem_whitney_le_of_isC2Form hx hΛ N)
    M.interpBound_nonneg hΛ fun N => (M.meshSize_pos N).le

/-- The smoothed cochain projections onto the Whitney complexes with vanishing boundary DOFs. -/
def starProjMin (N : ℕ) : (M.whitneyMin N).CochainProjection :=
  (M.exists_uniform_projMin.choose_spec.2 N).choose

theorem starProjMin_bound : ∃ C, ∀ (N : ℕ) (k : ℤ) (x : L2F ℝ D.Ω (formIdx n k)),
    ‖(starProjMin M N).π k x‖ ≤ C * ‖x‖ :=
  ⟨_, fun N k x => (M.exists_uniform_projMin.choose_spec.2 N).choose_spec.1 k x⟩

theorem star_denseMin : ∀ (k : ℤ) (y : L2F ℝ D.Ω (formIdx n k)) (ε : ℝ), 0 < ε →
    ∀ᶠ N in atTop, ∃ v ∈ (M.whitneyMin N).V k, ‖y - v‖ < ε := fun k y _ hε =>
  (M.eventually_exists_whitneyMin_near k y hε).mono fun _ ⟨v, hv, h1, _⟩ => ⟨v, hv, h1⟩

/-- **Maxwell's equations with a perfect electric conductor on a domain star-shaped with respect
to a ball**, with the Whitney forms with vanishing boundary DOFs. -/
def starPEC (a : ℤ) : ConstrainedFEEC (D.complexMin.window a 3) ℕ :=
  feec D.complexMin a atTop M.whitneyMin (starProjMin M) (starProjMin_bound M) (star_denseMin M)

/-- The `O(h)` rate class of `C²` solutions vanishing outside `Ω` (`StarDomain.IsC2FormMin`). -/
abbrev starPECRate (a : ℤ) (T Λ : ℝ) (hΛ : 0 ≤ Λ) : (starPEC M a).RateClass T :=
  regRate (starProjMin_bound M) (star_denseMin M) T (fun k x => D.IsC2FormMin k Λ x)
    M.interpBound (fun N => (M.mesh N).meshSize) Λ
    (fun N _ _ hx => M.exists_mem_whitneyMin_le_of_isC2FormMin hx hΛ N) M.interpBound_nonneg hΛ
    fun N => (M.meshSize_pos N).le

variable {M} {a : ℤ}

omit [NeZero n] in
/-- **Well-posedness** (perfect magnetic conductor, star-shaped domain): for `x ∈ D(L)`, `t ↦ e^{tL}
x` is a classical solution on `[0, T]` and conserves energy. [QuennevilleBelair2015], Thm 4.6 -/
theorem starPMC_wellPosed {x} (hx : x ∈ (D.complex.window a 3).wave.domain) (T : ℝ) :
    Evolution.IsClassicalSolution (D.complex.window a 3).wave (Icc 0 T) 0
        (fun t => (D.complex.window a 3).waveGroup.S t x) ∧
      ∀ t, ‖(D.complex.window a 3).waveGroup.S t x‖ = ‖x‖ :=
  ⟨(constrainedFEEC_wellPosed hx T).1, (constrainedFEEC_wellPosed hx T).2.2.2⟩

omit [NeZero n] in
/-- **The Gauss laws propagate** (perfect magnetic conductor, star-shaped domain) for all data and
all times `t ∈ ℝ`. [QuennevilleBelair2015], Prop. 4.16 -/
theorem starPMC_gauss_propagates :
    ∀ t, ∀ x ∈ windowGauss D.complex a,
      (D.complex.window a 3).waveGroup.S t x ∈ windowGauss D.complex a :=
  windowGauss_propagates D.complex a

/-- **Convergence of the semi-discrete solutions** (perfect magnetic conductor, star-shaped domain),
uniformly on `[0, T]`, for `D(L)` data and `ξₕ(0) = Pₕ x`. [QuennevilleBelair2015], Thm 4.14 -/
theorem starPMC_converges (T : ℝ) (x : (D.complex.window a 3).wave.domain) :
    TendstoUniformlyOn
      (fun N t => (D.complex.window a 3).totalD.graphFst
        ((starPMC M a).discrete N (waveLift _ x) t))
      (fun t => (D.complex.window a 3).waveGroup.S t x) atTop (Icc 0 T) :=
  ((starPMC M a).constrainedFEEC_of_approxFEEC.2.2.1 T).1 x

/-- **The Gauss-law residual** (perfect magnetic conductor, star-shaped domain) of the discrete
solution is bounded by the error and tends to `0` uniformly on `[0, T]`. -/
theorem starPMC_residual (x : (D.complex.window a 3).wave.domain)
    (hxK : (x : PiLp 2 _) ∈ windowGauss D.complex a) (T : ℝ) :
    (∀ N t, infDist ((D.complex.window a 3).totalD.graphFst
        ((starPMC M a).discrete N (waveLift _ x) t))
        (windowGauss D.complex a : Set _) ≤
      ‖(D.complex.window a 3).waveGroup.S t x -
        (D.complex.window a 3).totalD.graphFst
          ((starPMC M a).discrete N (waveLift _ x) t)‖) ∧
    TendstoUniformlyOn
      (fun N t => infDist ((D.complex.window a 3).totalD.graphFst
        ((starPMC M a).discrete N (waveLift _ x) t))
        (windowGauss D.complex a : Set _))
      (fun _ => 0) atTop (Icc 0 T) :=
  (starPMC M a).constrainedFEEC_of_approxFEEC.2.2.2.2.1 (isReducing_windowGauss _ a)
    x hxK T

/-- **The `O(h)` rate for `C²` solutions** (perfect magnetic conductor, star-shaped domain): if the
components of `e^{tL} x` and `e^{tL} L x` are `C²` forms on `cl Ω` (`StarDomain.IsC2Form`) with
bound `Λ` on `[0, T]`, then `‖ξ(t) - ξₕ(t)‖ ≤ (1 + C_P) (1 + t)² · 12 (Σᵢ B_{a+i}) h_N Λ`.
[QuennevilleBelair2015], Thm 4.14; [Arnold2018], Ch. 7 -/
theorem starPMC_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (starPMCRate M a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖(D.complex.window a 3).waveGroup.S t x -
        (D.complex.window a 3).totalD.graphFst
          ((starPMC M a).discrete N (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst (D.complex.window a 3)) * (1 + t) ^ 2 *
        (12 * (∑ i : Fin 3, M.interpBound (a + i)) * (M.mesh N).meshSize * Λ) :=
  rate_regRate _ _ hx N ht

/-- **The `O(h)` rate of the Gauss-law residual for `C²` solutions** (perfect magnetic conductor,
star-shaped domain). -/
theorem starPMC_residual_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (starPMCRate M a T Λ hΛ).Data) (hxK : x ∈ windowGauss D.complex a)
    (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    infDist ((D.complex.window a 3).totalD.graphFst
        ((starPMC M a).discrete N (waveLift _ ⟨x, hx.1⟩) t))
        (windowGauss D.complex a : Set _) ≤
      (1 + ellipticConst (D.complex.window a 3)) * (1 + t) ^ 2 *
        (12 * (∑ i : Fin 3, M.interpBound (a + i)) * (M.mesh N).meshSize * Λ) :=
  residual_rate_regRate _ _ hx hxK N ht

omit [NeZero n] in
/-- **Well-posedness** (perfect electric conductor, star-shaped domain): for `x ∈ D(L)`, `t ↦ e^{tL}
x` is a classical solution on `[0, T]` and conserves energy. [QuennevilleBelair2015], Thm 4.6 -/
theorem starPEC_wellPosed {x} (hx : x ∈ (D.complexMin.window a 3).wave.domain) (T : ℝ) :
    Evolution.IsClassicalSolution (D.complexMin.window a 3).wave (Icc 0 T) 0
        (fun t => (D.complexMin.window a 3).waveGroup.S t x) ∧
      ∀ t, ‖(D.complexMin.window a 3).waveGroup.S t x‖ = ‖x‖ :=
  ⟨(constrainedFEEC_wellPosed hx T).1, (constrainedFEEC_wellPosed hx T).2.2.2⟩

omit [NeZero n] in
/-- **The Gauss laws propagate** (perfect electric conductor, star-shaped domain) for all data and
all times `t ∈ ℝ`. [QuennevilleBelair2015], Prop. 4.16 -/
theorem starPEC_gauss_propagates :
    ∀ t, ∀ x ∈ windowGauss D.complexMin a,
      (D.complexMin.window a 3).waveGroup.S t x ∈ windowGauss D.complexMin a :=
  windowGauss_propagates D.complexMin a

/-- **Convergence of the semi-discrete solutions** (perfect electric conductor, star-shaped domain),
uniformly on `[0, T]`, for `D(L)` data and `ξₕ(0) = Pₕ x`. [QuennevilleBelair2015], Thm 4.14 -/
theorem starPEC_converges (T : ℝ) (x : (D.complexMin.window a 3).wave.domain) :
    TendstoUniformlyOn
      (fun N t => (D.complexMin.window a 3).totalD.graphFst
        ((starPEC M a).discrete N (waveLift _ x) t))
      (fun t => (D.complexMin.window a 3).waveGroup.S t x) atTop (Icc 0 T) :=
  ((starPEC M a).constrainedFEEC_of_approxFEEC.2.2.1 T).1 x

/-- **The Gauss-law residual** (perfect electric conductor, star-shaped domain) of the discrete
solution is bounded by the error and tends to `0` uniformly on `[0, T]`. -/
theorem starPEC_residual (x : (D.complexMin.window a 3).wave.domain)
    (hxK : (x : PiLp 2 _) ∈ windowGauss D.complexMin a) (T : ℝ) :
    (∀ N t, infDist ((D.complexMin.window a 3).totalD.graphFst
        ((starPEC M a).discrete N (waveLift _ x) t))
        (windowGauss D.complexMin a : Set _) ≤
      ‖(D.complexMin.window a 3).waveGroup.S t x -
        (D.complexMin.window a 3).totalD.graphFst
          ((starPEC M a).discrete N (waveLift _ x) t)‖) ∧
    TendstoUniformlyOn
      (fun N t => infDist ((D.complexMin.window a 3).totalD.graphFst
        ((starPEC M a).discrete N (waveLift _ x) t))
        (windowGauss D.complexMin a : Set _))
      (fun _ => 0) atTop (Icc 0 T) :=
  (starPEC M a).constrainedFEEC_of_approxFEEC.2.2.2.2.1 (isReducing_windowGauss _ a)
    x hxK T

/-- **The `O(h)` rate for `C²` solutions** (perfect electric conductor, star-shaped domain): if the
components of `e^{tL} x` and `e^{tL} L x` are `C²` forms vanishing outside `Ω`
(`StarDomain.IsC2FormMin`) with bound `Λ` on `[0, T]`, then `‖ξ(t) - ξₕ(t)‖ ≤ (1 + C_P) (1 + t)² ·
12 (Σᵢ B_{a+i}) h_N Λ`. [QuennevilleBelair2015], Thm 4.14; [Arnold2018], Ch. 7 -/
theorem starPEC_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (starPECRate M a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖(D.complexMin.window a 3).waveGroup.S t x -
        (D.complexMin.window a 3).totalD.graphFst
          ((starPEC M a).discrete N (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst (D.complexMin.window a 3)) * (1 + t) ^ 2 *
        (12 * (∑ i : Fin 3, M.interpBound (a + i)) * (M.mesh N).meshSize * Λ) :=
  rate_regRate _ _ hx N ht

/-- **The `O(h)` rate of the Gauss-law residual for `C²` solutions** (perfect electric conductor,
star-shaped domain). -/
theorem starPEC_residual_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (starPECRate M a T Λ hΛ).Data) (hxK : x ∈ windowGauss D.complexMin a)
    (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    infDist ((D.complexMin.window a 3).totalD.graphFst
        ((starPEC M a).discrete N (waveLift _ ⟨x, hx.1⟩) t))
        (windowGauss D.complexMin a : Set _) ≤
      (1 + ellipticConst (D.complexMin.window a 3)) * (1 + t) ^ 2 *
        (12 * (∑ i : Fin 3, M.interpBound (a + i)) * (M.mesh N).meshSize * Λ) :=
  residual_rate_regRate _ _ hx hxK N ht

/-- **The uniform discrete Poincaré inequality** for the Maxwell window on a star-shaped domain
(perfect magnetic conductor), under the Poincaré inequality of `HΛ(Ω)` (the only place where it
is needed). [AFW2010], Thm 3.6 -/
theorem starPMC_discretePoincare {cP : ℝ} (hP : HasPoincare D.complex cP) {i j : Fin 3}
    (hij : (ComplexShape.window 3).Rel i j) :
    ∃ C, 0 ≤ C ∧ ∀ N, ∀ x (hx : x ∈ ((starPMC M a).V N).V i),
      (∀ y ∈ ((starPMC M a).V N).cyclesW i, ⟪y, x⟫_ℝ = 0) →
        ‖x‖ ≤ C * cP * ‖(D.complex.window a 3).d i j ⟨x, ((starPMC M a).V N).le_domain i j hx⟩‖ :=
  constrainedFEEC_discretePoincare (starPMC M a) hij (window_poincare hP a hij)

/-- **The uniform discrete Poincaré inequality** for the Maxwell window on a star-shaped domain
(perfect electric conductor), under the Poincaré inequality of `H̊Λ(Ω)`. [AFW2010], Thm 3.6 -/
theorem starPEC_discretePoincare {cP : ℝ} (hP : HasPoincare D.complexMin cP) {i j : Fin 3}
    (hij : (ComplexShape.window 3).Rel i j) :
    ∃ C, 0 ≤ C ∧ ∀ N, ∀ x (hx : x ∈ ((starPEC M a).V N).V i),
      (∀ y ∈ ((starPEC M a).V N).cyclesW i, ⟪y, x⟫_ℝ = 0) →
        ‖x‖ ≤ C * cP *
          ‖(D.complexMin.window a 3).d i j ⟨x, ((starPEC M a).V N).le_domain i j hx⟩‖ :=
  constrainedFEEC_discretePoincare (starPEC M a) hij (window_poincare hP a hij)

/-! #### Unconditional discrete Poincaré inequalities -/

/-- **The uniform discrete Poincaré inequality on the cube** (perfect magnetic conductor), with
`c_P = (2π)⁻¹` (`CubeWitness.hasPoincare`). [AFW2010], Thm 3.6 -/
theorem cubePMC_discretePoincare {i j : Fin 3} (hij : (ComplexShape.window 3).Rel i j) :
    ∃ C, 0 ≤ C ∧ ∀ N, ∀ x (hx : x ∈ ((cubePMC n a).V N).V i),
      (∀ y ∈ ((cubePMC n a).V N).cyclesW i, ⟪y, x⟫_ℝ = 0) →
        ‖x‖ ≤ C * (2 * Real.pi)⁻¹ *
          ‖((FEM.complex n).window a 3).d i j ⟨x, ((cubePMC n a).V N).le_domain i j hx⟩‖ :=
  constrainedFEEC_discretePoincare (cubePMC n a) hij
    (window_poincare (H := FEM.complex n) (CubeWitness.hasPoincare n) a hij)

/-- **The uniform discrete Poincaré inequality on the cube** (perfect electric conductor), with
`c_P = (2π)⁻¹` (`CubeWitness.hasPoincareMin`). [AFW2010], Thm 3.6 -/
theorem cubePEC_discretePoincare {i j : Fin 3} (hij : (ComplexShape.window 3).Rel i j) :
    ∃ C, 0 ≤ C ∧ ∀ N, ∀ x (hx : x ∈ ((cubePEC n a).V N).V i),
      (∀ y ∈ ((cubePEC n a).V N).cyclesW i, ⟪y, x⟫_ℝ = 0) →
        ‖x‖ ≤ C * (2 * Real.pi)⁻¹ *
          ‖((FEM.complexMin n).window a 3).d i j ⟨x, ((cubePEC n a).V N).le_domain i j hx⟩‖ :=
  constrainedFEEC_discretePoincare (cubePEC n a) hij
    (window_poincare (H := FEM.complexMin n) (CubeWitness.hasPoincareMin n) a hij)

/-- **The uniform discrete Poincaré inequality on the parallelepiped** `Ω = A · Q + b` (perfect
magnetic conductor), with `c_P(A) = Parallelepiped.poincareConst A`. [AFW2010], Thm 3.6 -/
theorem paraPMC_discretePoincare (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (b : Fin n → ℝ) {i j : Fin 3} (hij : (ComplexShape.window 3).Rel i j) :
    ∃ C, 0 ≤ C ∧ ∀ N, ∀ x (hx : x ∈ ((paraPMC A hA b a).V N).V i),
      (∀ y ∈ ((paraPMC A hA b a).V N).cyclesW i, ⟪y, x⟫_ℝ = 0) →
        ‖x‖ ≤ C * Feec.Models.Parallelepiped.poincareConst A *
          ‖((Feec.Models.Parallelepiped.complex A b).window a 3).d i j
            ⟨x, ((paraPMC A hA b a).V N).le_domain i j hx⟩‖ :=
  constrainedFEEC_discretePoincare (paraPMC A hA b a) hij
    (window_poincare (Feec.Models.Parallelepiped.poincare A hA b) a hij)

/-- **The uniform discrete Poincaré inequality on the parallelepiped** (perfect electric
conductor). [AFW2010], Thm 3.6 -/
theorem paraPEC_discretePoincare (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (b : Fin n → ℝ) {i j : Fin 3} (hij : (ComplexShape.window 3).Rel i j) :
    ∃ C, 0 ≤ C ∧ ∀ N, ∀ x (hx : x ∈ ((paraPEC A hA b a).V N).V i),
      (∀ y ∈ ((paraPEC A hA b a).V N).cyclesW i, ⟪y, x⟫_ℝ = 0) →
        ‖x‖ ≤ C * Feec.Models.Parallelepiped.poincareConst A *
          ‖((Feec.Models.Parallelepiped.complexMin A b).window a 3).d i j
            ⟨x, ((paraPEC A hA b a).V N).le_domain i j hx⟩‖ :=
  constrainedFEEC_discretePoincare (paraPEC A hA b a) hij
    (window_poincare (Feec.Models.Parallelepiped.poincare_min A hA b) a hij)

/-- **The star-shaped instance at a concrete domain**: for the cube as a star-shaped domain with
the Freudenthal mesh family (`CubeWitness`), `starPMC` has the uniform discrete Poincaré
inequality with no hypothesis. -/
theorem starPMC_cubeWitness_discretePoincare {i j : Fin 3}
    (hij : (ComplexShape.window 3).Rel i j) :
    ∃ C, 0 ≤ C ∧ ∀ N, ∀ x (hx : x ∈ ((starPMC (CubeWitness.meshFamily n) a).V N).V i),
      (∀ y ∈ ((starPMC (CubeWitness.meshFamily n) a).V N).cyclesW i, ⟪y, x⟫_ℝ = 0) →
        ‖x‖ ≤ C * (2 * Real.pi)⁻¹ * ‖((CubeWitness.starDomain n).complex.window a 3).d i j
          ⟨x, ((starPMC (CubeWitness.meshFamily n) a).V N).le_domain i j hx⟩‖ :=
  starPMC_discretePoincare (CubeWitness.hasPoincare n) hij

/-- `starPEC` at the cube witness, with no hypothesis. -/
theorem starPEC_cubeWitness_discretePoincare {i j : Fin 3}
    (hij : (ComplexShape.window 3).Rel i j) :
    ∃ C, 0 ≤ C ∧ ∀ N, ∀ x (hx : x ∈ ((starPEC (CubeWitness.meshFamily n) a).V N).V i),
      (∀ y ∈ ((starPEC (CubeWitness.meshFamily n) a).V N).cyclesW i, ⟪y, x⟫_ℝ = 0) →
        ‖x‖ ≤ C * (2 * Real.pi)⁻¹ * ‖((CubeWitness.starDomain n).complexMin.window a 3).d i j
          ⟨x, ((starPEC (CubeWitness.meshFamily n) a).V N).le_domain i j hx⟩‖ :=
  starPEC_discretePoincare (CubeWitness.hasPoincareMin n) hij

/-- **The star-shaped instance at every parallelepiped** (`ParallelepipedWitness`), with no
hypothesis. -/
theorem starPMC_paraWitness_discretePoincare (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (b : Fin n → ℝ) {i j : Fin 3} (hij : (ComplexShape.window 3).Rel i j) :
    ∃ C, 0 ≤ C ∧ ∀ N,
      ∀ x (hx : x ∈ ((starPMC (ParallelepipedWitness.meshFamily A hA b) a).V N).V i),
      (∀ y ∈ ((starPMC (ParallelepipedWitness.meshFamily A hA b) a).V N).cyclesW i,
        ⟪y, x⟫_ℝ = 0) →
        ‖x‖ ≤ C * Feec.Models.Parallelepiped.poincareConst A *
          ‖((ParallelepipedWitness.starDomain A hA b).complex.window a 3).d i j
            ⟨x, ((starPMC (ParallelepipedWitness.meshFamily A hA b) a).V N).le_domain i j hx⟩‖ :=
  starPMC_discretePoincare (M := ParallelepipedWitness.meshFamily A hA b)
    (fun i j hij z hz => Feec.Models.Parallelepiped.poincare A hA b i j hij z hz) hij

/-- `starPEC` at every parallelepiped, with no hypothesis. -/
theorem starPEC_paraWitness_discretePoincare (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (b : Fin n → ℝ) {i j : Fin 3} (hij : (ComplexShape.window 3).Rel i j) :
    ∃ C, 0 ≤ C ∧ ∀ N,
      ∀ x (hx : x ∈ ((starPEC (ParallelepipedWitness.meshFamily A hA b) a).V N).V i),
      (∀ y ∈ ((starPEC (ParallelepipedWitness.meshFamily A hA b) a).V N).cyclesW i,
        ⟪y, x⟫_ℝ = 0) →
        ‖x‖ ≤ C * Feec.Models.Parallelepiped.poincareConst A *
          ‖((ParallelepipedWitness.starDomain A hA b).complexMin.window a 3).d i j
            ⟨x, ((starPEC (ParallelepipedWitness.meshFamily A hA b) a).V N).le_domain i j hx⟩‖ :=
  starPEC_discretePoincare (M := ParallelepipedWitness.meshFamily A hA b)
    (fun i j hij z hz => Feec.Models.Parallelepiped.poincare_min A hA b i j hij z hz) hij

end StarShaped

/-! ### Through the approximating FEEC theorem -/

section Approx

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [AddCommMonoidWithOne α] [IsCancelAdd α]
  [CharZero α] {V : α → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)]
  [∀ i, CompleteSpace (V i)] {H : HilbertComplex 𝕜 (ComplexShape.up α) V} {a : α}
  {κ : Type*} {l : Filter κ} {S : κ → H.Subcomplex} [∀ h k, FiniteDimensional 𝕜 ((S h).V k)]
  {P : ∀ h, (S h).CochainProjection}
  (hP : ∃ C, ∀ h k x, ‖(P h).π k x‖ ≤ C * ‖x‖)
  (hS : ∀ k (y : V k) (ε : ℝ), 0 < ε → ∀ᶠ h in l, ∃ v ∈ (S h).V k, ‖y - v‖ < ε)
  [∀ i, NormedSpace ℝ (V i)] [∀ i, IsScalarTower ℝ 𝕜 (V i)]

/-- **Every Maxwell discretization is an instance of the approximating FEEC theorem**: the verdict
of `approxFEEC` for `(feec H a l S P hP hS).toApprox` (the special case `ιₕ` = inclusion,
`πₕ = Pₕ` windowed) with the core `D(L²)` (`ConstrainedFEEC.toCore`). The statement of
`constrainedFEEC` follows from it (`ConstrainedFEEC.constrainedFEEC_of_approxFEEC`). -/
theorem feec_approxFEEC :
    (feec H a l S P hP hS).toApprox.Verdict (feec H a l S P hP hS).toCore := approxFEEC _ _

/-- **The rate of the semi-discrete Maxwell solutions with the conforming factor
`(1 + C_P)(1 + 2t)`** (sharper than the `(1 + t)²` of `rate`), from `approxFEEC_rate`
(`ConstrainedFEEC.rate_le`). -/
theorem approx_rate {T : ℝ} (R : (feec H a l S P hP hS).RateClass T)
    {x : PiLp 2 fun i : Fin 3 => V (a + i)} (hxR : x ∈ R.Data) (h : κ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖(H.window a 3).waveGroup.S t x - (H.window a 3).totalD.graphFst
        ((feec H a l S P hP hS).discrete h (waveLift _ ⟨x, R.mem_domain x hxR⟩) t)‖ ≤
      (1 + ellipticConst (H.window a 3)) * (1 + 2 * t) *
        (R.C * R.meshSize h ^ R.α * R.classNorm x) :=
  (feec H a l S P hP hS).rate_le R hxR h ht

/-- **The rate of the Gauss-law residual with the conforming factor `(1 + C_P)(1 + 2t)`**, from
`approxFEEC_residual_le` (the residual through `ιₕ` is bounded by the error) and `approx_rate`. -/
theorem approx_residual_rate {T : ℝ} (R : (feec H a l S P hP hS).RateClass T)
    {x : PiLp 2 fun i : Fin 3 => V (a + i)} (hxR : x ∈ R.Data) (hxK : x ∈ windowGauss H a)
    (h : κ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    infDist ((H.window a 3).totalD.graphFst
        ((feec H a l S P hP hS).discrete h (waveLift _ ⟨x, R.mem_domain x hxR⟩) t))
        (windowGauss H a : Set _) ≤
      (1 + ellipticConst (H.window a 3)) * (1 + 2 * t) *
        (R.C * R.meshSize h ^ R.α * R.classNorm x) := by
  have hr := approxFEEC_residual_le (feec H a l S P hP hS).toApprox (isReducing_windowGauss H a)
    hxK h ((feec H a l S P hP hS).ellipticProj h (waveLift _ ⟨x, R.mem_domain x hxR⟩)) t
  rw [ConstrainedFEEC.toApprox_sol] at hr
  exact hr.trans (approx_rate hP hS R hxR h ht)

/-- **The `O(r_h)` rate for regular data with the factor `(1 + C_P)(1 + 2t)`** (`rate_regRate`
with `(1 + t)²` replaced by `1 + 2t`). -/
theorem approx_rate_regRate {T : ℝ} {Reg : ∀ k, V k → Prop} {B : α → ℝ} {r : κ → ℝ} {Λ : ℝ}
    {happ : ∀ h k (x : V k), Reg k x → ∃ v, ∃ hv : v ∈ (S h).V k,
      ‖x - v‖ ≤ B k * Λ * r h ∧ ∀ j (hxj : x ∈ (H.d k j).domain),
        ‖H.d k j ⟨x - v, Submodule.sub_mem _ hxj ((S h).le_domain k j hv)⟩‖ ≤ B k * Λ * r h}
    {hB : ∀ k, 0 ≤ B k} {hΛ : 0 ≤ Λ} {hr : ∀ h, 0 ≤ r h} {x : PiLp 2 fun i : Fin 3 => V (a + i)}
    (hx : x ∈ (regRate hP hS T Reg B r Λ happ hB hΛ hr).Data) (h : κ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖(H.window a 3).waveGroup.S t x - (H.window a 3).totalD.graphFst
        ((feec H a l S P hP hS).discrete h (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst (H.window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, B (a + i)) * r h * Λ) := by
  simpa only [regRate, Real.rpow_one] using
    approx_rate hP hS (regRate hP hS T Reg B r Λ happ hB hΛ hr) hx h ht

/-- **The `O(r_h)` rate of the Gauss-law residual with the factor `(1 + C_P)(1 + 2t)`**. -/
theorem approx_residual_rate_regRate {T : ℝ} {Reg : ∀ k, V k → Prop} {B : α → ℝ} {r : κ → ℝ}
    {Λ : ℝ}
    {happ : ∀ h k (x : V k), Reg k x → ∃ v, ∃ hv : v ∈ (S h).V k,
      ‖x - v‖ ≤ B k * Λ * r h ∧ ∀ j (hxj : x ∈ (H.d k j).domain),
        ‖H.d k j ⟨x - v, Submodule.sub_mem _ hxj ((S h).le_domain k j hv)⟩‖ ≤ B k * Λ * r h}
    {hB : ∀ k, 0 ≤ B k} {hΛ : 0 ≤ Λ} {hr : ∀ h, 0 ≤ r h} {x : PiLp 2 fun i : Fin 3 => V (a + i)}
    (hx : x ∈ (regRate hP hS T Reg B r Λ happ hB hΛ hr).Data) (hxK : x ∈ windowGauss H a)
    (h : κ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    infDist ((H.window a 3).totalD.graphFst
        ((feec H a l S P hP hS).discrete h (waveLift _ ⟨x, hx.1⟩) t)) (windowGauss H a : Set _) ≤
      (1 + ellipticConst (H.window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, B (a + i)) * r h * Λ) := by
  have := approx_residual_rate hP hS (regRate hP hS T Reg B r Λ happ hB hΛ hr) hx hxK h ht
  simp only [regRate, Real.rpow_one] at this
  exact this

end Approx

/-! ### The Maxwell instances through the approximating FEEC theorem -/

section TorusApprox

open Models.Torus.DeRham

variable {d : Type*} [Fintype d] [LinearOrder d] {a : ℕ}

/-- **`torus` through the approximating FEEC theorem** (the constrained FEEC special case
`ConstrainedFEEC.toApprox`, core `D(L²)`). -/
theorem torus_approxFEEC : (torus d a).toApprox.Verdict (torus d a).toCore := approxFEEC _ _

/-- **The vanishing-field constraint on `𝕋ᵈ` through the approximating FEEC theorem**: the
verdict for the spectral Galerkin discretization with the constraint `E = 0`, `B = 0`
(`withConstraint`), together with the fact that the constraint does not reduce `L`
(`torus_not_isReducing_potential`), so the non-reducing branches 4b–4c of the verdict are not
vacuous; `torus_potential_residual_of_approxFEEC` discharges the graded 4c clause. -/
theorem torus_potential_approxFEEC [Nonempty d] :
    (withConstraint (torus d 0) (potential ℂ fun i : Fin 3 => L2Form d (0 + i))
        isClosed_potential).toApprox.Verdict
      (withConstraint (torus d 0) (potential ℂ fun i : Fin 3 => L2Form d (0 + i))
        isClosed_potential).toCore ∧
    ¬ ((complex d).window 0 3).wave.IsReducing (potential ℂ fun i : Fin 3 => L2Form d (0 + i)) :=
  ⟨approxFEEC _ _, torus_not_isReducing_potential⟩

-- the instance arguments of `toApprox` at `L2Form d (0 + i)` need more than the default
set_option maxHeartbeats 400000 in
/-- **`torus_potential_residual`, read off the approximating FEEC theorem**: the statement of
`torus_potential_residual`, derived from the graded item 4c of `torus_potential_approxFEEC`,
with the parity grading of the window (`ComplexShape.window_parity`), the `R`-invariance of the
vanishing-field constraint (`reversal_mem_totalSub`), the density of `D(L) ∩ K`
(`dense_potential`), the density of the core (`mem_toCore_closure`), the convergence of the
elliptic projections (`tendsto_incl_ellipticProj`) and the identification of the discrete orbits
from `Rₕ ξ₀` with the semi-discrete solutions (`toApprox_sol`). -/
theorem torus_potential_residual_of_approxFEEC [Nonempty d] {T : ℝ} (hT : 0 < T) :
    ∃ x : ((complex d).window 0 3).wave.domain,
      (x : PiLp 2 _) ∈ potential ℂ (fun i : Fin 3 => L2Form d (0 + i)) ∧ ∃ t ∈ Icc 0 T,
      ((complex d).window 0 3).waveGroup.S t x ∉ potential ℂ (fun i : Fin 3 => L2Form d (0 + i)) ∧
      0 < infDist (((complex d).window 0 3).waveGroup.S t x)
        (potential ℂ (fun i : Fin 3 => L2Form d (0 + i)) : Set _) ∧
      Tendsto (fun N => infDist (((complex d).window 0 3).totalD.graphFst
          ((torus d 0).discrete N (waveLift _ x) t))
          (potential ℂ (fun i : Fin 3 => L2Form d (0 + i)) : Set _)) atTop
        (𝓝 (infDist (((complex d).window 0 3).waveGroup.S t x)
          (potential ℂ (fun i : Fin 3 => L2Form d (0 + i)) : Set _))) ∧
      ∀ᶠ N in atTop, infDist (((complex d).window 0 3).waveGroup.S t x)
          (potential ℂ (fun i : Fin 3 => L2Form d (0 + i)) : Set _) / 2 <
        infDist (((complex d).window 0 3).totalD.graphFst
          ((torus d 0).discrete N (waveLift _ x) t))
          (potential ℂ (fun i : Fin 3 => L2Form d (0 + i)) : Set _) := by
  obtain ⟨V, hnot⟩ := torus_potential_approxFEEC (d := d)
  obtain ⟨x, hxK, t, ht, hout, hpos, hres⟩ := V.2.2.2.2.2.2.2.2.2 _
    (fun _ _ h => ComplexShape.window_parity h) (fun _ hx => reversal_mem_totalSub hx)
    (dense_potential _) hnot T hT
  obtain ⟨hlim, hev⟩ := hres (ConstrainedFEEC.mem_toCore_closure _ _) _
    (ConstrainedFEEC.tendsto_incl_ellipticProj _ x)
  refine ⟨x, hxK, t, ht, hout, hpos, hlim.congr fun N => ?_, hev.mono fun N hN => ?_⟩
  · exact congrArg (infDist · _) (ConstrainedFEEC.toApprox_sol _ N _ t)
  · rwa [ConstrainedFEEC.toApprox_sol] at hN

end TorusApprox

section CubeApprox

open Models.Cube Feec.Domain Feec.ExteriorFibre

variable {n : ℕ} [NeZero n] {a : ℤ}

/-- **`cubePMC` through the approximating FEEC theorem** (the constrained FEEC special case
`ConstrainedFEEC.toApprox`, core `D(L²)`). -/
theorem cubePMC_approxFEEC : (cubePMC n a).toApprox.Verdict (cubePMC n a).toCore := approxFEEC _ _

/-- **`cubePEC` through the approximating FEEC theorem** (the constrained FEEC special case
`ConstrainedFEEC.toApprox`, core `D(L²)`). -/
theorem cubePEC_approxFEEC : (cubePEC n a).toApprox.Verdict (cubePEC n a).toCore := approxFEEC _ _

/-- **The `O(h)` rate with the conforming factor `(1 + C_P)(1 + 2t)`**
(`cubePMC_rate` with `(1 + t)²` replaced by `1 + 2t`), through the approximating FEEC
theorem. -/
theorem cubePMC_approx_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (cubePMCRate n a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖((FEM.complex n).window a 3).waveGroup.S t x -
        ((FEM.complex n).window a 3).totalD.graphFst
          ((cubePMC n a).discrete N (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst ((FEM.complex n).window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, FEM.interpBound n (a + i)) * FEM.meshSize N * Λ) :=
  approx_rate_regRate _ _ hx N ht

/-- **The `O(h)` Gauss-law residual rate with the conforming factor `(1 + C_P)(1 + 2t)`**
(`cubePMC_residual_rate` with `(1 + t)²` replaced by `1 + 2t`), through the approximating FEEC
theorem. -/
theorem cubePMC_approx_residual_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (cubePMCRate n a T Λ hΛ).Data) (hxK : x ∈ windowGauss (FEM.complex n) a)
    (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    infDist (((FEM.complex n).window a 3).totalD.graphFst
        ((cubePMC n a).discrete N (waveLift _ ⟨x, hx.1⟩) t))
        (windowGauss (FEM.complex n) a : Set _) ≤
      (1 + ellipticConst ((FEM.complex n).window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, FEM.interpBound n (a + i)) * FEM.meshSize N * Λ) :=
  approx_residual_rate_regRate _ _ hx hxK N ht

/-- **The `O(h)` rate with the conforming factor `(1 + C_P)(1 + 2t)`**
(`cubePEC_rate` with `(1 + t)²` replaced by `1 + 2t`), through the approximating FEEC
theorem. -/
theorem cubePEC_approx_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (cubePECRate n a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖((FEM.complexMin n).window a 3).waveGroup.S t x -
        ((FEM.complexMin n).window a 3).totalD.graphFst
          ((cubePEC n a).discrete N (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst ((FEM.complexMin n).window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, FEM.interpBound n (a + i)) * FEM.meshSize N * Λ) :=
  approx_rate_regRate _ _ hx N ht

/-- **The `O(h)` Gauss-law residual rate with the conforming factor `(1 + C_P)(1 + 2t)`**
(`cubePEC_residual_rate` with `(1 + t)²` replaced by `1 + 2t`), through the approximating FEEC
theorem. -/
theorem cubePEC_approx_residual_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (cubePECRate n a T Λ hΛ).Data) (hxK : x ∈ windowGauss (FEM.complexMin n) a)
    (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    infDist (((FEM.complexMin n).window a 3).totalD.graphFst
        ((cubePEC n a).discrete N (waveLift _ ⟨x, hx.1⟩) t))
        (windowGauss (FEM.complexMin n) a : Set _) ≤
      (1 + ellipticConst ((FEM.complexMin n).window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, FEM.interpBound n (a + i)) * FEM.meshSize N * Λ) :=
  approx_residual_rate_regRate _ _ hx hxK N ht

end CubeApprox

section ParallelepipedApprox

open Models.Cube Feec.Domain Feec.ExteriorFibre
open Models.Parallelepiped (complex complexMin rateBound)

variable {n : ℕ} [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ} {hA : IsUnit A.det} {b : Fin n → ℝ}
  {a : ℤ}

/-- **`paraPMC` through the approximating FEEC theorem** (the constrained FEEC special case
`ConstrainedFEEC.toApprox`, core `D(L²)`). -/
theorem paraPMC_approxFEEC : (paraPMC A hA b a).toApprox.Verdict (paraPMC A hA b a).toCore :=
  approxFEEC _ _

/-- **`paraPEC` through the approximating FEEC theorem** (the constrained FEEC special case
`ConstrainedFEEC.toApprox`, core `D(L²)`). -/
theorem paraPEC_approxFEEC : (paraPEC A hA b a).toApprox.Verdict (paraPEC A hA b a).toCore :=
  approxFEEC _ _

/-- **The `O(h)` rate with the conforming factor `(1 + C_P)(1 + 2t)`**
(`paraPMC_rate` with `(1 + t)²` replaced by `1 + 2t`), through the approximating FEEC
theorem. -/
theorem paraPMC_approx_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (paraPMCRate A hA b a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖((complex A b).window a 3).waveGroup.S t x -
        ((complex A b).window a 3).totalD.graphFst
          ((paraPMC A hA b a).discrete N (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst ((complex A b).window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, rateBound A (a + i)) * FEM.meshSize N * Λ) :=
  approx_rate_regRate _ _ hx N ht

/-- **The `O(h)` Gauss-law residual rate with the conforming factor `(1 + C_P)(1 + 2t)`**
(`paraPMC_residual_rate` with `(1 + t)²` replaced by `1 + 2t`), through the approximating FEEC
theorem. -/
theorem paraPMC_approx_residual_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (paraPMCRate A hA b a T Λ hΛ).Data) (hxK : x ∈ windowGauss (complex A b) a)
    (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    infDist (((complex A b).window a 3).totalD.graphFst
        ((paraPMC A hA b a).discrete N (waveLift _ ⟨x, hx.1⟩) t))
        (windowGauss (complex A b) a : Set _) ≤
      (1 + ellipticConst ((complex A b).window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, rateBound A (a + i)) * FEM.meshSize N * Λ) :=
  approx_residual_rate_regRate _ _ hx hxK N ht

/-- **The `O(h)` rate with the conforming factor `(1 + C_P)(1 + 2t)`**
(`paraPEC_rate` with `(1 + t)²` replaced by `1 + 2t`), through the approximating FEEC
theorem. -/
theorem paraPEC_approx_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (paraPECRate A hA b a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖((complexMin A b).window a 3).waveGroup.S t x -
        ((complexMin A b).window a 3).totalD.graphFst
          ((paraPEC A hA b a).discrete N (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst ((complexMin A b).window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, rateBound A (a + i)) * FEM.meshSize N * Λ) :=
  approx_rate_regRate _ _ hx N ht

/-- **The `O(h)` Gauss-law residual rate with the conforming factor `(1 + C_P)(1 + 2t)`**
(`paraPEC_residual_rate` with `(1 + t)²` replaced by `1 + 2t`), through the approximating FEEC
theorem. -/
theorem paraPEC_approx_residual_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (paraPECRate A hA b a T Λ hΛ).Data) (hxK : x ∈ windowGauss (complexMin A b) a)
    (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    infDist (((complexMin A b).window a 3).totalD.graphFst
        ((paraPEC A hA b a).discrete N (waveLift _ ⟨x, hx.1⟩) t))
        (windowGauss (complexMin A b) a : Set _) ≤
      (1 + ellipticConst ((complexMin A b).window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, rateBound A (a + i)) * FEM.meshSize N * Λ) :=
  approx_residual_rate_regRate _ _ hx hxK N ht

end ParallelepipedApprox

section StarShapedApprox

open Models.Cube Models.StarShaped Feec.Domain Feec.ExteriorFibre

variable {n : ℕ} [NeZero n] {D : StarDomain n} {M : MeshFamily D} {a : ℤ}

/-- **`starPMC` through the approximating FEEC theorem** (the constrained FEEC special case
`ConstrainedFEEC.toApprox`, core `D(L²)`). -/
theorem starPMC_approxFEEC : (starPMC M a).toApprox.Verdict (starPMC M a).toCore := approxFEEC _ _

/-- **`starPEC` through the approximating FEEC theorem** (the constrained FEEC special case
`ConstrainedFEEC.toApprox`, core `D(L²)`). -/
theorem starPEC_approxFEEC : (starPEC M a).toApprox.Verdict (starPEC M a).toCore := approxFEEC _ _

/-- **The `O(h)` rate with the conforming factor `(1 + C_P)(1 + 2t)`**
(`starPMC_rate` with `(1 + t)²` replaced by `1 + 2t`), through the approximating FEEC
theorem. -/
theorem starPMC_approx_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (starPMCRate M a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖(D.complex.window a 3).waveGroup.S t x -
        (D.complex.window a 3).totalD.graphFst
          ((starPMC M a).discrete N (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst (D.complex.window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, M.interpBound (a + i)) * (M.mesh N).meshSize * Λ) :=
  approx_rate_regRate _ _ hx N ht

/-- **The `O(h)` Gauss-law residual rate with the conforming factor `(1 + C_P)(1 + 2t)`**
(`starPMC_residual_rate` with `(1 + t)²` replaced by `1 + 2t`), through the approximating FEEC
theorem. -/
theorem starPMC_approx_residual_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (starPMCRate M a T Λ hΛ).Data) (hxK : x ∈ windowGauss D.complex a)
    (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    infDist ((D.complex.window a 3).totalD.graphFst
        ((starPMC M a).discrete N (waveLift _ ⟨x, hx.1⟩) t))
        (windowGauss D.complex a : Set _) ≤
      (1 + ellipticConst (D.complex.window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, M.interpBound (a + i)) * (M.mesh N).meshSize * Λ) :=
  approx_residual_rate_regRate _ _ hx hxK N ht

/-- **The `O(h)` rate with the conforming factor `(1 + C_P)(1 + 2t)`**
(`starPEC_rate` with `(1 + t)²` replaced by `1 + 2t`), through the approximating FEEC
theorem. -/
theorem starPEC_approx_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (starPECRate M a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖(D.complexMin.window a 3).waveGroup.S t x -
        (D.complexMin.window a 3).totalD.graphFst
          ((starPEC M a).discrete N (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst (D.complexMin.window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, M.interpBound (a + i)) * (M.mesh N).meshSize * Λ) :=
  approx_rate_regRate _ _ hx N ht

/-- **The `O(h)` Gauss-law residual rate with the conforming factor `(1 + C_P)(1 + 2t)`**
(`starPEC_residual_rate` with `(1 + t)²` replaced by `1 + 2t`), through the approximating FEEC
theorem. -/
theorem starPEC_approx_residual_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (starPECRate M a T Λ hΛ).Data) (hxK : x ∈ windowGauss D.complexMin a)
    (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    infDist ((D.complexMin.window a 3).totalD.graphFst
        ((starPEC M a).discrete N (waveLift _ ⟨x, hx.1⟩) t))
        (windowGauss D.complexMin a : Set _) ≤
      (1 + ellipticConst (D.complexMin.window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, M.interpBound (a + i)) * (M.mesh N).meshSize * Λ) :=
  approx_residual_rate_regRate _ _ hx hxK N ht

end StarShapedApprox

end Feec.Instances.Maxwell
