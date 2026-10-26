module

public import Feec.HilbertComplex.Approximation.ConstrainedFEEC
public import Feec.HilbertComplex.Approximation.ApproxConforming
public import Feec.HilbertComplex.Approximation.ApproxComplex
public import Feec.Physics.Maxwell.CubeFEM
public import Feec.Physics.Maxwell.Constraints
public import Feec.Models.Torus.DeRhamGalerkin
public import Feec.Models.StarShaped.FiniteElement
public import Feec.Models.ConformingFamilies

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
* **Maxwell discretizations.** `feec F a` is the constrained FEEC discretization of the window
  `H.window a 3` with constraint `windowGauss H a`, for every conforming family `F` of `H`
  (`Feec.HilbertComplex.ConformingFamily`: finite-dimensional subcomplexes, cochain projections
  bounded uniformly in `L²`, the approximation property): the windows of `F`
  (`ConformingFamily.window`) with the Gauss laws (`ConformingFamily.withConstraint`). `regRate` is
  the rate class of data whose orbit and derivative have degreewise regularity `Reg` on `[0, T]`,
  under a degreewise best-approximation estimate `‖x - v‖, ‖d (x - v)‖ ≤ B Λ r_h`
  (`ConstrainedFEEC.RateClass.ofDegreewise` on the window).
* **The headline statements for every Maxwell discretization**, each a field of the verdict
  `ConstrainedFEEC.Verdict` of `ConstrainedFEEC.constrainedFEEC_of_approxFEEC` (the constrained
  FEEC theorem derived from the approximating one): `wellPosed`, `gauss_propagates` (and
  `gauss_propagates_strong`; with no discretization, `windowGauss_propagates`,
  `windowGauss_propagates_strong`), `converges`, and `rate`, `rate_regRate` with the conforming
  factor `(1 + C_P)(1 + 2t)` of the approximating FEEC theorem (`ConstrainedFEEC.rate_le`; it
  implies the `(1 + t)²` of `constrainedFEEC_rate`).
* **A non-reducing Maxwell constraint.** The vanishing-field constraint `potential 𝕜 W`
  (`E = 0`, `B = 0`; `mem_potential`) of a complex on `ComplexShape.fin3` does not reduce `L` as
  soon as `d₀ ≠ 0` (`not_isReducing_potential`, since `L (σ, 0, 0) = (0, dσ, 0)`), and `D(L) ∩ K`
  is dense in it (`dense_potential`).

Every verdict of the approximating FEEC theorem `Feec.HilbertComplex.approxFEEC` holds for every
Maxwell discretization (`approxFEEC (feec F a).toApprox (feec F a).toCore`; the concrete instances
below are pinned in the regression tests `scripts/FeecCheck/MaxwellInstances.lean`); on the
torus it is used with the non-reducing vanishing-field constraint (`torus_potential_approxFEEC`,
whose graded departure clause `torus_potential_residual_of_approxFEEC` reads off).

**Through the discrete complex.** Every Maxwell discretization is also an instance of the
complex-level front end `Feec.HilbertComplex.ApproxFEEC.ofComplex`
(`Feec.HilbertComplex.ConstrainedFEEC.toComplex`: the subcomplexes as discrete Hilbert
complexes, zero inner-product defect, the same discrete solutions). There the **discrete Gauss
laws** `discreteGauss F Y h = {0} × N(𝐝ₕ₀*) × (Vₕ² ∩ Y)` (adjoint in `Vₕ`: the discrete
divergence) are a reducing subcomplex of `Vₕ`, preserved exactly by the discrete solutions, with
the magnetic component read in `W` in `Y` (`discreteGauss_propagates`); for the cube,
`cubePMC_ofComplex` (`Y` the magnetic Gauss law `dB = 0`).

## Instances

* **The torus `𝕋ᵈ`** (any `d`, any degree `a`; `d = 3`, `a = 0` is the classical system), with
  the spectral Galerkin family of band-limited forms `|n|_∞ ≤ N` and the Fourier truncations
  (`torusFamily`, `torus`). The gradient of `𝕋ᵈ` is not zero (`torus_exists_d_ne_zero`), so the
  vanishing-field constraint is not reducing (`torus_not_isReducing_potential`) and is violated,
  also by the spectral Galerkin solutions (`torus_potential_residual_of_approxFEEC`).
* **The cube `Q = (0, ½)ⁿ`**, for the **perfect magnetic conductor** (the maximal complex
  `HΛ(Q)`) and the **perfect electric conductor** (the minimal complex `H̊Λ(Q)`, vanishing boundary
  DOFs): with the lowest-order Whitney forms of the Freudenthal meshes (`cubePMC`, `cubePEC`; for
  `n = 3`, `a = 0` these are the Maxwell systems of `Feec.Maxwell.CubeFEM`), with the `O(h)` rate
  classes of `C²` solutions (`cubePMCRate`, `cubePECRate`; non-vacuity `zero_mem_cubePMCRate`,
  `zero_mem_cubePECRate`; `cubePMC_rate`, `cubePEC_rate`), and **at every polynomial order**, with
  the finite element complexes of every admissible sequence `S` of the periodic table
  (`cubePolyPMC`, `cubePolyPEC`), with the `O(h^{s+1})` rate classes of `C^{s+2}` solutions for a
  sequence of order `s` (`cubePolyPMCRate`, `cubePolyPECRate`; `cubePolyPMC_rate`,
  `cubePolyPEC_rate`).
* **Parallelepipeds `Ω = A · Q + b`** (every box), with the image Freudenthal meshes, both boundary
  conditions, Whitney forms and every admissible sequence (`paraPMC`, `paraPEC`, `paraPolyPMC`,
  `paraPolyPEC` and their rate classes and rates).
* **Domains star-shaped with respect to a ball**, with any uniformly shape-regular and
  quasi-uniform mesh family, both boundary conditions, Whitney forms and every admissible sequence
  (`starPMC`, `starPEC`, `starPolyPMC`, `starPolyPEC` and their rate classes and rates). The
  Poincaré inequality (`StarShaped.HasPoincare`) is needed only for the uniform discrete Poincaré
  inequality (`starPMC_discretePoincare`, `starPEC_discretePoincare`).
* **Unconditional discrete Poincaré inequalities**, from the proved Poincaré inequalities of the
  cube and the parallelepipeds: `cubePMC_discretePoincare`, `cubePEC_discretePoincare`,
  `paraPMC_discretePoincare`, `paraPEC_discretePoincare`.

No Poincaré inequality, closed range, compactness or exactness hypothesis enters the
well-posedness, propagation and convergence statements. The rate classes are
hypotheses on the data (regularity of the orbit on `[0, T]`), as in `Feec.Maxwell.CubeFEM`.
The Gauss constraint is reducing, so the departure clauses of the verdict (non-reducing
constraints) concern other constraints, such as the vanishing-field constraint
(`torus_potential_residual_of_approxFEEC`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.4 (Thms 4.6, 4.7), §4.6 (Thm 4.14), §4.9 (Prop. 4.16), §4.10 (Prop. 4.17)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3 (approximation property, bounded cochain projections, Thm 3.6), §5 (the spaces `P_rΛ`,
  `P_r⁻Λ`), §5.5 (smoothed projections)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (rates for smooth
  solutions), Ch. 8 (evolution problems)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap Metric

@[expose] public noncomputable section

namespace Feec.Instances.Maxwell

open Feec.HilbertComplex _root_.Feec.HodgeWave
open Feec.FiniteElement (PolySeq)

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

variable [∀ i, NormedSpace ℝ (V i)] [∀ i, IsScalarTower ℝ 𝕜 (V i)]

/-- **The Gauss laws propagate** in every Maxwell window, for all data and all times `t ∈ ℝ`, with
no discretization: item (2) of the constrained FEEC theorem (`constrainedFEEC_propagates_iff`) at
the reducing constraint `windowGauss H a`. [QuennevilleBelair2015], Prop. 4.16, Prop. 4.17 -/
theorem windowGauss_propagates : ∀ t, ∀ x ∈ windowGauss H a,
    (H.window a 3).waveGroup.S t x ∈ windowGauss H a :=
  ((H.window a 3).isReducing_iff_waveGroup_invariant _ |>.trans C0Group.map_le_iff_forall).1
    (isReducing_windowGauss H a)

/-- **The Gauss laws propagate along strong solutions** on `[0, T]` in every Maxwell window, with
no discretization. [QuennevilleBelair2015], Prop. 4.16 -/
theorem windowGauss_propagates_strong {T : ℝ} {U : ℝ → PiLp 2 fun i : Fin 3 => V (a + i)}
    (h0 : U 0 ∈ windowGauss H a)
    (hU : Evolution.IsStrongSolution (H.window a 3).wave (Icc 0 T) 0 U) :
    ∀ t ∈ Icc 0 T, U t ∈ windowGauss H a :=
  hU.mem_of_isReducing (H.window a 3).isSkewAdjoint_wave.isDissipative
    (isReducing_windowGauss H a) h0 fun _ _ => (windowGauss H a).zero_mem

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

end Window

/-! ### Maxwell discretizations -/

section Discretization

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [AddCommMonoidWithOne α] [IsCancelAdd α]
  [CharZero α] {V : α → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)]
  [∀ i, CompleteSpace (V i)] {H : HilbertComplex 𝕜 (ComplexShape.up α) V} {κ : Type*}
  (F : ConformingFamily H κ) (a : α)

/-- **The constrained FEEC discretization of Maxwell's equations** in the window
`V a → V (a+1) → V (a+2)` of `H`, for every conforming family `F` of `H` (finite-dimensional
subcomplexes, cochain projections bounded uniformly in `L²`, the approximation property): the
windows of `F` (`ConformingFamily.window`) with the Gauss laws as constraint. -/
def feec : ConstrainedFEEC (H.window a 3) κ :=
  (F.window a 3).withConstraint (windowGauss H a) (isClosed_gauss _ _)

variable [∀ i, NormedSpace ℝ (V i)] [∀ i, IsScalarTower ℝ 𝕜 (V i)]

/-- The **rate class of regular data** on `[0, T]` (`ConstrainedFEEC.RateClass.ofDegreewise` on
the window): data `x ∈ D(L²)` whose orbit `e^{tL} x` and derivative `e^{tL} L x` have components
satisfying the degreewise regularity `Reg` for `t ∈ [0, T]`, when every `Reg`-regular form of
degree `k` is within `B k Λ r_h` of `Vₕᵏ` in the graph norm. The constant is
`(3 + 3²) Σᵢ B (a + i) = 12 Σᵢ B (a + i)`, the order `1` in `r_h`, the class norm `Λ`. -/
abbrev regRate (T : ℝ) (Reg : ∀ k, V k → Prop) (B : α → ℝ) (r : κ → ℝ) (Λ : ℝ)
    (happ : ∀ h k (x : V k), Reg k x → ∃ v, ∃ hv : v ∈ (F.V h).V k,
      ‖x - v‖ ≤ B k * Λ * r h ∧ ∀ j (hxj : x ∈ (H.d k j).domain),
        ‖H.d k j ⟨x - v, Submodule.sub_mem _ hxj ((F.V h).le_domain k j hv)⟩‖ ≤ B k * Λ * r h)
    (hB : ∀ k, 0 ≤ B k) (hΛ : 0 ≤ Λ) (hr : ∀ h, 0 ≤ r h) : (feec F a).RateClass T :=
  ConstrainedFEEC.RateClass.ofDegreewise (feec F a) T (fun i => Reg (a + i)) (fun i => B (a + i))
    r Λ (fun h i x hx => by
      obtain ⟨v, hv, h1, h2⟩ := happ h _ x hx
      exact ⟨v, hv, h1, fun j hxj => h2 _ hxj⟩) (fun _ => hB _) hΛ hr

/-! ### The headline statements for every Maxwell discretization -/

/-- **The Gauss laws propagate** for all data and all times `t ∈ ℝ`: the Gauss constraint of
the discretization is reducing. [QuennevilleBelair2015], Prop. 4.16, Prop. 4.17 -/
theorem gauss_propagates : ∀ t, ∀ x ∈ (feec F a).K,
    (H.window a 3).waveGroup.S t x ∈ (feec F a).K :=
  (feec F a).constrainedFEEC_of_approxFEEC.propagates_iff.1 (isReducing_windowGauss H a)

/-- **The Gauss laws propagate along strong solutions** on `[0, T]`. [QuennevilleBelair2015],
Prop. 4.16 -/
theorem gauss_propagates_strong {T : ℝ} {U : ℝ → PiLp 2 fun i : Fin 3 => V (a + i)}
    (h0 : U 0 ∈ (feec F a).K)
    (hU : Evolution.IsStrongSolution (H.window a 3).wave (Icc 0 T) 0 U) :
    ∀ t ∈ Icc 0 T, U t ∈ (feec F a).K :=
  constrainedFEEC_propagates (feec F a) (isReducing_windowGauss H a) h0 hU

/-- **Convergence of the semi-discrete Maxwell solutions**, uniformly on `[0, T]`, for data in
`D(L)` (`ξₕ(0) = Pₕ ξ₀`), and for data in `W` along every family with `ξₕ(0) → ξ₀` (such
families exist). [QuennevilleBelair2015], Thm 4.14 -/
theorem converges (T : ℝ) :
    (∀ x : (H.window a 3).wave.domain, TendstoUniformlyOn
      (fun h t => (H.window a 3).totalD.graphFst ((feec F a).discrete h (waveLift _ x) t))
      (fun t => (H.window a 3).waveGroup.S t x) F.l (Icc 0 T)) ∧
    ∀ x : PiLp 2 fun i : Fin 3 => V (a + i),
      (∀ ξh ξh' : κ → ℝ → (H.window a 3).totalD.GraphSpace,
        (∀ h, IsSemidiscreteSolution ((feec F a).Kh h) (Icc 0 T) (ξh h) (ξh' h)) →
        Tendsto (fun h => (H.window a 3).totalD.graphFst (ξh h 0)) F.l (𝓝 x) →
        TendstoUniformlyOn (fun h t => (H.window a 3).totalD.graphFst (ξh h t))
          (fun t => (H.window a 3).waveGroup.S t x) F.l (Icc 0 T)) ∧
      ∃ ξh ξh' : κ → ℝ → (H.window a 3).totalD.GraphSpace,
        (∀ h, IsSemidiscreteSolution ((feec F a).Kh h) (Icc 0 T) (ξh h) (ξh' h)) ∧
        Tendsto (fun h => (H.window a 3).totalD.graphFst (ξh h 0)) F.l (𝓝 x) :=
  have V := (feec F a).constrainedFEEC_of_approxFEEC
  ⟨fun x => V.converges x T, fun x => ⟨fun ξh ξh' hξh h0 => V.converges_of_tendsto x ξh ξh' hξh h0,
    V.exists_tendsto x T⟩⟩

/-- **The rate of the semi-discrete Maxwell solutions** for data in a rate class on `[0, T]`:
`‖ξ(t) - ξₕ(t)‖ ≤ (1 + C_P) (1 + 2t) C hᵅ ‖ξ₀‖_class`, the conforming factor of the
approximating FEEC theorem (`ConstrainedFEEC.rate_le`; it implies the `(1 + t)²` of
`constrainedFEEC_rate`). [QuennevilleBelair2015], Thm 4.14 -/
theorem rate {T : ℝ} (R : (feec F a).RateClass T) {x : PiLp 2 fun i : Fin 3 => V (a + i)}
    (hxR : x ∈ R.Data) (h : κ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖(H.window a 3).waveGroup.S t x - (H.window a 3).totalD.graphFst
        ((feec F a).discrete h (waveLift _ ⟨x, R.mem_domain x hxR⟩) t)‖ ≤
      (1 + ellipticConst (H.window a 3)) * (1 + 2 * t) *
        (R.C * R.meshSize h ^ R.α * R.classNorm x) :=
  (feec F a).rate_le R hxR h ht

variable {F a}

/-- **Non-vacuity of `regRate`**: the zero datum lies in the rate class whenever the zero form is
regular in every degree. -/
theorem zero_mem_regRate {T : ℝ} {Reg : ∀ k, V k → Prop} {B : α → ℝ} {r : κ → ℝ} {Λ : ℝ}
    {happ hB hΛ hr} (h0 : ∀ k, Reg k 0) :
    (0 : PiLp 2 fun i : Fin 3 => V (a + i)) ∈ (regRate F a T Reg B r Λ happ hB hΛ hr).Data :=
  ConstrainedFEEC.RateClass.zero_mem_ofDegreewise fun _ => h0 _

/-- **The `O(r_h)` rate for regular data** (`regRate`): for `x` whose orbit and derivative are
`Reg`-regular on `[0, T]`, `‖ξ(t) - ξₕ(t)‖ ≤ (1 + C_P) (1 + 2t) · 12 (Σᵢ B (a + i)) r_h Λ`.
[QuennevilleBelair2015], Thm 4.14 -/
theorem rate_regRate {T : ℝ} {Reg : ∀ k, V k → Prop} {B : α → ℝ} {r : κ → ℝ} {Λ : ℝ}
    {happ hB hΛ hr} {x : PiLp 2 fun i : Fin 3 => V (a + i)}
    (hx : x ∈ (regRate F a T Reg B r Λ happ hB hΛ hr).Data) (h : κ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖(H.window a 3).waveGroup.S t x - (H.window a 3).totalD.graphFst
        ((feec F a).discrete h (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst (H.window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, B (a + i)) * r h * Λ) := by
  refine (rate F a _ hx h ht).trans_eq ?_
  simp only [ConstrainedFEEC.RateClass.ofDegreewise, Real.rpow_one, Fintype.card_fin]
  ring

end Discretization

/-! ### The torus: spectral Galerkin -/

section Torus

open Models.Torus.DeRham

variable (d : Type*) [Fintype d] [LinearOrder d]

/-- **The spectral Galerkin family of `𝕋ᵈ`**: the band-limited forms `|n|_∞ ≤ N` with the Fourier
truncations (orthogonal, of norm `1`), a conforming family of the de Rham complex of `𝕋ᵈ`. -/
def torusFamily : ConformingFamily (complex d) ℕ where
  l := atTop
  V := bandSubcomplex d
  π := bandProj d
  bound_π := ⟨1, fun N k x => by
    rw [one_mul, bandProj_apply]; exact Submodule.norm_starProjection_apply_le _ x⟩
  approx k y := by
    refine (tendsto_infDist_submodule_iff _ y).2 fun ε hε => ?_
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
  feec (torusFamily d) a

variable {d} {a : ℕ}

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

end Torus

/-! ### The cube: perfect magnetic and electric conductors, at every polynomial order -/

section Cube

open Models.Cube Feec.Domain Feec.ExteriorFibre

variable (n : ℕ) [NeZero n]

/-- **Maxwell's equations with a perfect magnetic conductor on the cube** `Q = (0, ½)ⁿ`
(degree `a`; `n = 3`, `a = 0` is the system `HΛ⁰(Q) → HΛ¹(Q) → L²Λ²(Q)` of
`Feec.Maxwell.CubeFEM`), discretized by the lowest-order Whitney forms of the Freudenthal meshes
with the smoothed projections (`FEM.whitneyFamily`), as a constrained FEEC discretization with the
Gauss laws. -/
def cubePMC (a : ℤ) : ConstrainedFEEC ((FEM.complex n).window a 3) ℕ :=
  feec (FEM.whitneyFamily n) a

/-- The `O(h)` rate class of `C²` solutions with bound `Λ` on `[0, T]` (`FEM.IsC2Form`). -/
abbrev cubePMCRate (a : ℤ) (T Λ : ℝ) (hΛ : 0 ≤ Λ) : (cubePMC n a).RateClass T :=
  regRate (FEM.whitneyFamily n) a T (fun k x => FEM.IsC2Form k Λ x) (FEM.interpBound n)
    FEM.meshSize Λ (fun N _ _ hx => hx.exists_mem_whitney_le hΛ N) (FEM.interpBound_nonneg n) hΛ
    fun N => (FEM.meshSize_pos N).le

/-- **Maxwell's equations with a perfect electric conductor on the cube** (vanishing tangential
traces: `H̊Λ⁰(Q) → H̊Λ¹(Q) → L²Λ²(Q)` for `n = 3`, `a = 0`), discretized by the Whitney forms with
vanishing boundary DOFs (`FEM.whitneyFamilyMin`), as a constrained FEEC discretization with the
Gauss laws. -/
def cubePEC (a : ℤ) : ConstrainedFEEC ((FEM.complexMin n).window a 3) ℕ :=
  feec (FEM.whitneyFamilyMin n) a

/-- The `O(h)` rate class of `C²` solutions vanishing outside `Q` (`FEM.IsC2FormMin`). -/
abbrev cubePECRate (a : ℤ) (T Λ : ℝ) (hΛ : 0 ≤ Λ) : (cubePEC n a).RateClass T :=
  regRate (FEM.whitneyFamilyMin n) a T (fun k x => FEM.IsC2FormMin k Λ x) (FEM.interpBound n)
    FEM.meshSize Λ (fun N _ _ hx => hx.exists_mem_whitneyMin_le hΛ N) (FEM.interpBound_nonneg n) hΛ
    fun N => (FEM.meshSize_pos N).le

/-- **Maxwell's equations with a perfect magnetic conductor on the cube at every polynomial
order**: the finite element complexes of an admissible sequence `S` (every `P_rΛ`, `P_r⁻Λ` and
mixed sequence of the periodic table, `FEM.polyFamily`) with the smoothed projections. -/
def cubePolyPMC (S : PolySeq) (a : ℤ) : ConstrainedFEEC ((FEM.complex n).window a 3) ℕ :=
  feec (FEM.polyFamily n S) a

/-- The `O(h^{s+1})` rate class of `C^{s+2}` solutions (`FEM.IsCsForm`) for a sequence of order `s`
(`FEM.PolyOrder`: `S` reproduces `P_sΛ`). -/
abbrev cubePolyPMCRate (S : PolySeq) {s : ℕ} (hS : FEM.PolyOrder n S s) (a : ℤ) (T Λ : ℝ)
    (hΛ : 0 ≤ Λ) : (cubePolyPMC n S a).RateClass T :=
  regRate (FEM.polyFamily n S) a T (fun k x => FEM.IsCsForm s k Λ x) (FEM.polyInterpBound n S)
    (fun N => FEM.meshSize N ^ (s + 1)) Λ
    (fun N k _ hx => hx.exists_mem_poly_le (hS.polyOrderAt k) hΛ N)
    (FEM.polyInterpBound_nonneg S) hΛ fun N => pow_nonneg (FEM.meshSize_pos N).le _

/-- **Maxwell's equations with a perfect electric conductor on the cube at every polynomial
order** (`FEM.polyFamilyMin`). -/
def cubePolyPEC (S : PolySeq) (a : ℤ) : ConstrainedFEEC ((FEM.complexMin n).window a 3) ℕ :=
  feec (FEM.polyFamilyMin n S) a

/-- The `O(h^{s+1})` rate class of `C^{s+2}` solutions vanishing outside `Q`
(`FEM.IsCsFormMin`) for a sequence of order `s`. -/
abbrev cubePolyPECRate (S : PolySeq) {s : ℕ} (hS : FEM.PolyOrder n S s) (a : ℤ) (T Λ : ℝ)
    (hΛ : 0 ≤ Λ) : (cubePolyPEC n S a).RateClass T :=
  regRate (FEM.polyFamilyMin n S) a T (fun k x => FEM.IsCsFormMin s k Λ x)
    (FEM.polyInterpBound n S) (fun N => FEM.meshSize N ^ (s + 1)) Λ
    (fun N k _ hx => hx.exists_mem_polyMin_le (hS.polyOrderAt k) hΛ N)
    (FEM.polyInterpBound_nonneg S) hΛ fun N => pow_nonneg (FEM.meshSize_pos N).le _

variable {n} {a : ℤ}

/-- **The `O(h)` rate for `C²` solutions** (perfect magnetic conductor, cube): if the components of
`e^{tL} x` and `e^{tL} L x` are `C²` forms (`FEM.IsC2Form`) with bound `Λ` on `[0, T]`, then
`‖ξ(t) - ξₕ(t)‖ ≤ (1 + C_P) (1 + 2t) · 12 (Σᵢ B_{a+i}) h_N Λ`. [QuennevilleBelair2015], Thm 4.14;
[Arnold2018], Ch. 7 -/
theorem cubePMC_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (cubePMCRate n a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖((FEM.complex n).window a 3).waveGroup.S t x -
        ((FEM.complex n).window a 3).totalD.graphFst
          ((cubePMC n a).discrete N (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst ((FEM.complex n).window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, FEM.interpBound n (a + i)) * FEM.meshSize N * Λ) :=
  rate_regRate hx N ht

/-- **The `O(h)` rate for `C²` solutions** (perfect electric conductor, cube): if the components of
`e^{tL} x` and `e^{tL} L x` are `C²` forms vanishing outside `Q` (`FEM.IsC2FormMin`) with bound `Λ`
on `[0, T]`, then `‖ξ(t) - ξₕ(t)‖ ≤ (1 + C_P) (1 + 2t) · 12 (Σᵢ B_{a+i}) h_N Λ`.
[QuennevilleBelair2015], Thm 4.14; [Arnold2018], Ch. 7 -/
theorem cubePEC_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (cubePECRate n a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖((FEM.complexMin n).window a 3).waveGroup.S t x -
        ((FEM.complexMin n).window a 3).totalD.graphFst
          ((cubePEC n a).discrete N (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst ((FEM.complexMin n).window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, FEM.interpBound n (a + i)) * FEM.meshSize N * Λ) :=
  rate_regRate hx N ht

/-- **The `O(h^{s+1})` rate at every polynomial order** (perfect magnetic conductor, cube): for a
sequence `S` of order `s` and `C^{s+2}` orbits with bound `Λ` on `[0, T]` (`FEM.IsCsForm`),
`‖ξ(t) - ξₕ(t)‖ ≤ (1 + C_P) (1 + 2t) · 12 (Σᵢ B_{a+i}) h_N^{s+1} Λ`. [QuennevilleBelair2015],
Thm 4.14; [AFW2010], §5 -/
theorem cubePolyPMC_rate {S : PolySeq} {s : ℕ} {hS : FEM.PolyOrder n S s} {T Λ : ℝ} {hΛ : 0 ≤ Λ}
    {x} (hx : x ∈ (cubePolyPMCRate n S hS a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖((FEM.complex n).window a 3).waveGroup.S t x -
        ((FEM.complex n).window a 3).totalD.graphFst
          ((cubePolyPMC n S a).discrete N (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst ((FEM.complex n).window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, FEM.polyInterpBound n S (a + i)) * FEM.meshSize N ^ (s + 1) * Λ) :=
  rate_regRate hx N ht

/-- **The `O(h^{s+1})` rate at every polynomial order** (perfect electric conductor, cube), for
`C^{s+2}` orbits vanishing outside `Q` (`FEM.IsCsFormMin`). [QuennevilleBelair2015], Thm 4.14;
[AFW2010], §5 -/
theorem cubePolyPEC_rate {S : PolySeq} {s : ℕ} {hS : FEM.PolyOrder n S s} {T Λ : ℝ} {hΛ : 0 ≤ Λ}
    {x} (hx : x ∈ (cubePolyPECRate n S hS a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖((FEM.complexMin n).window a 3).waveGroup.S t x -
        ((FEM.complexMin n).window a 3).totalD.graphFst
          ((cubePolyPEC n S a).discrete N (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst ((FEM.complexMin n).window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, FEM.polyInterpBound n S (a + i)) * FEM.meshSize N ^ (s + 1) * Λ) :=
  rate_regRate hx N ht

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
  zero_mem_regRate fun k => isC2Form_zero k hΛ

theorem zero_mem_cubePECRate {T Λ : ℝ} (hΛ : 0 ≤ Λ) :
    (0 : PiLp 2 _) ∈ (cubePECRate n a T Λ hΛ).Data :=
  zero_mem_regRate fun k => isC2FormMin_zero k hΛ

end Cube

/-! ### Parallelepipeds -/

section Parallelepiped

open Models.Cube Feec.Domain Feec.ExteriorFibre
open Models.Parallelepiped (complex complexMin domain IsC2Form IsC2FormMin IsCsForm IsCsFormMin
  rateBound rateBound_nonneg polyRateBound polyRateBound_nonneg whitneyFamily whitneyFamilyMin
  polyFamily polyFamilyMin)

variable {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ)

/-- **Maxwell's equations with a perfect magnetic conductor on the parallelepiped**
`Ω = A · Q + b` (every box), with the Whitney forms of the image Freudenthal meshes
(`Parallelepiped.whitneyFamily`), as a constrained FEEC discretization with the Gauss laws. -/
def paraPMC (a : ℤ) : ConstrainedFEEC ((complex A b).window a 3) ℕ :=
  feec (whitneyFamily A hA b) a

/-- The `O(h)` rate class of `C²` solutions on `Ω` (`Parallelepiped.IsC2Form`). -/
abbrev paraPMCRate (a : ℤ) (T Λ : ℝ) (hΛ : 0 ≤ Λ) : (paraPMC A hA b a).RateClass T :=
  regRate (whitneyFamily A hA b) a T (fun k x => IsC2Form A hA b k Λ x) (rateBound A)
    FEM.meshSize Λ (fun N _ _ hx => hx.exists_mem_whitney_le A hA b hΛ N) (rateBound_nonneg A) hΛ
    fun N => (FEM.meshSize_pos N).le

/-- **Maxwell's equations with a perfect electric conductor on the parallelepiped** `Ω`, with the
Whitney forms with vanishing boundary DOFs (`Parallelepiped.whitneyFamilyMin`). -/
def paraPEC (a : ℤ) : ConstrainedFEEC ((complexMin A b).window a 3) ℕ :=
  feec (whitneyFamilyMin A hA b) a

/-- The `O(h)` rate class of `C²` solutions vanishing outside `Ω`. -/
abbrev paraPECRate (a : ℤ) (T Λ : ℝ) (hΛ : 0 ≤ Λ) : (paraPEC A hA b a).RateClass T :=
  regRate (whitneyFamilyMin A hA b) a T (fun k x => IsC2FormMin A hA b k Λ x) (rateBound A)
    FEM.meshSize Λ (fun N _ _ hx => hx.exists_mem_whitneyMin_le A hA b hΛ N) (rateBound_nonneg A)
    hΛ fun N => (FEM.meshSize_pos N).le

/-- **Maxwell's equations with a perfect magnetic conductor on the parallelepiped at every
polynomial order**: the finite element complexes of an admissible sequence `S`
(`Parallelepiped.polyFamily`). -/
def paraPolyPMC (S : PolySeq) (a : ℤ) : ConstrainedFEEC ((complex A b).window a 3) ℕ :=
  feec (polyFamily A hA b S) a

/-- The `O(h^{s+1})` rate class of `C^{s+2}` solutions on `Ω` (`Parallelepiped.IsCsForm`) for a
sequence of order `s`. -/
abbrev paraPolyPMCRate (S : PolySeq) {s : ℕ} (hS : FEM.PolyOrder n S s) (a : ℤ) (T Λ : ℝ)
    (hΛ : 0 ≤ Λ) : (paraPolyPMC A hA b S a).RateClass T :=
  regRate (polyFamily A hA b S) a T (fun k x => IsCsForm A hA b s k Λ x) (polyRateBound A S s)
    (fun N => FEM.meshSize N ^ (s + 1)) Λ
    (fun N k _ hx => by
      obtain ⟨v, hv, h1, h2⟩ := hx.exists_mem_poly_le A hA b (hS.polyOrderAt k) hΛ N
      exact ⟨v, hv, (mul_assoc _ Λ _).symm ▸ h1, fun j hxj => (mul_assoc _ Λ _).symm ▸ h2 j hxj⟩)
    (polyRateBound_nonneg A S s) hΛ fun N => pow_nonneg (FEM.meshSize_pos N).le _

/-- **Maxwell's equations with a perfect electric conductor on the parallelepiped at every
polynomial order** (`Parallelepiped.polyFamilyMin`). -/
def paraPolyPEC (S : PolySeq) (a : ℤ) : ConstrainedFEEC ((complexMin A b).window a 3) ℕ :=
  feec (polyFamilyMin A hA b S) a

/-- The `O(h^{s+1})` rate class of `C^{s+2}` solutions vanishing outside `Ω`
(`Parallelepiped.IsCsFormMin`) for a sequence of order `s`. -/
abbrev paraPolyPECRate (S : PolySeq) {s : ℕ} (hS : FEM.PolyOrder n S s) (a : ℤ) (T Λ : ℝ)
    (hΛ : 0 ≤ Λ) : (paraPolyPEC A hA b S a).RateClass T :=
  regRate (polyFamilyMin A hA b S) a T (fun k x => IsCsFormMin A hA b s k Λ x)
    (polyRateBound A S s) (fun N => FEM.meshSize N ^ (s + 1)) Λ
    (fun N k _ hx => by
      obtain ⟨v, hv, h1, h2⟩ := hx.exists_mem_polyMin_le A hA b (hS.polyOrderAt k) hΛ N
      exact ⟨v, hv, (mul_assoc _ Λ _).symm ▸ h1, fun j hxj => (mul_assoc _ Λ _).symm ▸ h2 j hxj⟩)
    (polyRateBound_nonneg A S s) hΛ fun N => pow_nonneg (FEM.meshSize_pos N).le _

variable {A hA b} {a : ℤ}

/-- **The `O(h)` rate for `C²` solutions** (perfect magnetic conductor, parallelepiped): if the
components of `e^{tL} x` and `e^{tL} L x` are `C²` forms on `cl Ω` (`Parallelepiped.IsC2Form`) with
bound `Λ` on `[0, T]`, then `‖ξ(t) - ξₕ(t)‖ ≤ (1 + C_P) (1 + 2t) · 12 (Σᵢ B_{a+i}) h_N Λ`.
[QuennevilleBelair2015], Thm 4.14; [Arnold2018], Ch. 7 -/
theorem paraPMC_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (paraPMCRate A hA b a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖((complex A b).window a 3).waveGroup.S t x -
        ((complex A b).window a 3).totalD.graphFst
          ((paraPMC A hA b a).discrete N (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst ((complex A b).window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, rateBound A (a + i)) * FEM.meshSize N * Λ) :=
  rate_regRate hx N ht

/-- **The `O(h)` rate for `C²` solutions** (perfect electric conductor, parallelepiped): if the
components of `e^{tL} x` and `e^{tL} L x` are `C²` forms vanishing outside `Ω`
(`Parallelepiped.IsC2FormMin`) with bound `Λ` on `[0, T]`, then
`‖ξ(t) - ξₕ(t)‖ ≤ (1 + C_P) (1 + 2t) · 12 (Σᵢ B_{a+i}) h_N Λ`. [QuennevilleBelair2015], Thm 4.14;
[Arnold2018], Ch. 7 -/
theorem paraPEC_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (paraPECRate A hA b a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖((complexMin A b).window a 3).waveGroup.S t x -
        ((complexMin A b).window a 3).totalD.graphFst
          ((paraPEC A hA b a).discrete N (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst ((complexMin A b).window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, rateBound A (a + i)) * FEM.meshSize N * Λ) :=
  rate_regRate hx N ht

/-- **The `O(h^{s+1})` rate at every polynomial order** (perfect magnetic conductor,
parallelepiped): for a sequence `S` of order `s` and `C^{s+2}` orbits with bound `Λ` on `[0, T]`
(`Parallelepiped.IsCsForm`), `‖ξ(t) - ξₕ(t)‖ ≤ (1 + C_P) (1 + 2t) · 12 (Σᵢ B_{a+i}) h_N^{s+1} Λ`.
[QuennevilleBelair2015], Thm 4.14; [AFW2010], §5 -/
theorem paraPolyPMC_rate {S : PolySeq} {s : ℕ} {hS : FEM.PolyOrder n S s} {T Λ : ℝ}
    {hΛ : 0 ≤ Λ} {x} (hx : x ∈ (paraPolyPMCRate A hA b S hS a T Λ hΛ).Data) (N : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖((complex A b).window a 3).waveGroup.S t x -
        ((complex A b).window a 3).totalD.graphFst
          ((paraPolyPMC A hA b S a).discrete N (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst ((complex A b).window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, polyRateBound A S s (a + i)) * FEM.meshSize N ^ (s + 1) * Λ) :=
  rate_regRate hx N ht

/-- **The `O(h^{s+1})` rate at every polynomial order** (perfect electric conductor,
parallelepiped), for `C^{s+2}` orbits vanishing outside `Ω` (`Parallelepiped.IsCsFormMin`).
[QuennevilleBelair2015], Thm 4.14; [AFW2010], §5 -/
theorem paraPolyPEC_rate {S : PolySeq} {s : ℕ} {hS : FEM.PolyOrder n S s} {T Λ : ℝ}
    {hΛ : 0 ≤ Λ} {x} (hx : x ∈ (paraPolyPECRate A hA b S hS a T Λ hΛ).Data) (N : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖((complexMin A b).window a 3).waveGroup.S t x -
        ((complexMin A b).window a 3).totalD.graphFst
          ((paraPolyPEC A hA b S a).discrete N (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst ((complexMin A b).window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, polyRateBound A S s (a + i)) * FEM.meshSize N ^ (s + 1) * Λ) :=
  rate_regRate hx N ht

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

/-- **Maxwell's equations with a perfect magnetic conductor on a domain star-shaped with respect
to a ball**, with the Whitney forms of a uniformly shape-regular, quasi-uniform mesh family
(`MeshFamily.whitneyFamily`), as a constrained FEEC discretization with the Gauss laws. No
Poincaré inequality is needed. -/
def starPMC (a : ℤ) : ConstrainedFEEC (D.complex.window a 3) ℕ :=
  feec M.whitneyFamily a

/-- The `O(h)` rate class of `C²` solutions on `Ω` (`StarDomain.IsC2Form`), in powers of the mesh
size `h_N` of the family. -/
abbrev starPMCRate (a : ℤ) (T Λ : ℝ) (hΛ : 0 ≤ Λ) : (starPMC M a).RateClass T :=
  regRate M.whitneyFamily a T (fun k x => D.IsC2Form k Λ x) M.interpBound
    (fun N => (M.mesh N).meshSize) Λ (fun N _ _ hx => M.exists_mem_whitney_le_of_isC2Form hx hΛ N)
    M.interpBound_nonneg hΛ fun N => (M.meshSize_pos N).le

/-- **Maxwell's equations with a perfect electric conductor on a domain star-shaped with respect
to a ball**, with the Whitney forms with vanishing boundary DOFs (`MeshFamily.whitneyFamilyMin`). -/
def starPEC (a : ℤ) : ConstrainedFEEC (D.complexMin.window a 3) ℕ :=
  feec M.whitneyFamilyMin a

/-- The `O(h)` rate class of `C²` solutions vanishing outside `Ω` (`StarDomain.IsC2FormMin`). -/
abbrev starPECRate (a : ℤ) (T Λ : ℝ) (hΛ : 0 ≤ Λ) : (starPEC M a).RateClass T :=
  regRate M.whitneyFamilyMin a T (fun k x => D.IsC2FormMin k Λ x) M.interpBound
    (fun N => (M.mesh N).meshSize) Λ
    (fun N _ _ hx => M.exists_mem_whitneyMin_le_of_isC2FormMin hx hΛ N) M.interpBound_nonneg hΛ
    fun N => (M.meshSize_pos N).le

/-- **Maxwell's equations with a perfect magnetic conductor on a star-shaped domain at every
polynomial order**: the finite element complexes of an admissible sequence `S` on the mesh family
(`MeshFamily.polyFamily`). -/
def starPolyPMC (S : PolySeq) (a : ℤ) : ConstrainedFEEC (D.complex.window a 3) ℕ :=
  feec (M.polyFamily S) a

/-- The `O(h^{s+1})` rate class of `C^{s+2}` solutions on `Ω` (`StarDomain.IsCsForm`) for a
sequence of order `s`. -/
abbrev starPolyPMCRate (S : PolySeq) {s : ℕ} (hS : FEM.PolyOrder n S s) (a : ℤ) (T Λ : ℝ)
    (hΛ : 0 ≤ Λ) : (starPolyPMC M S a).RateClass T :=
  regRate (M.polyFamily S) a T (fun k x => D.IsCsForm s k Λ x) (M.polyInterpBound S)
    (fun N => (M.mesh N).meshSize ^ (s + 1)) Λ
    (fun N k _ hx => M.exists_mem_poly_le_of_isCsForm S (hS.polyOrderAt k) hx hΛ N)
    (M.polyInterpBound_nonneg S) hΛ fun N => pow_nonneg (M.meshSize_pos N).le _

/-- **Maxwell's equations with a perfect electric conductor on a star-shaped domain at every
polynomial order** (`MeshFamily.polyFamilyMin`). -/
def starPolyPEC (S : PolySeq) (a : ℤ) : ConstrainedFEEC (D.complexMin.window a 3) ℕ :=
  feec (M.polyFamilyMin S) a

/-- The `O(h^{s+1})` rate class of `C^{s+2}` solutions vanishing outside `Ω`
(`StarDomain.IsCsFormMin`) for a sequence of order `s`. -/
abbrev starPolyPECRate (S : PolySeq) {s : ℕ} (hS : FEM.PolyOrder n S s) (a : ℤ) (T Λ : ℝ)
    (hΛ : 0 ≤ Λ) : (starPolyPEC M S a).RateClass T :=
  regRate (M.polyFamilyMin S) a T (fun k x => D.IsCsFormMin s k Λ x) (M.polyInterpBound S)
    (fun N => (M.mesh N).meshSize ^ (s + 1)) Λ
    (fun N k _ hx => M.exists_mem_polyMin_le_of_isCsFormMin S (hS.polyOrderAt k) hx hΛ N)
    (M.polyInterpBound_nonneg S) hΛ fun N => pow_nonneg (M.meshSize_pos N).le _

variable {M} {a : ℤ}

/-- **The `O(h)` rate for `C²` solutions** (perfect magnetic conductor, star-shaped domain): if the
components of `e^{tL} x` and `e^{tL} L x` are `C²` forms on `cl Ω` (`StarDomain.IsC2Form`) with
bound `Λ` on `[0, T]`, then `‖ξ(t) - ξₕ(t)‖ ≤ (1 + C_P) (1 + 2t) · 12 (Σᵢ B_{a+i}) h_N Λ`.
[QuennevilleBelair2015], Thm 4.14; [Arnold2018], Ch. 7 -/
theorem starPMC_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (starPMCRate M a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖(D.complex.window a 3).waveGroup.S t x -
        (D.complex.window a 3).totalD.graphFst
          ((starPMC M a).discrete N (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst (D.complex.window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, M.interpBound (a + i)) * (M.mesh N).meshSize * Λ) :=
  rate_regRate hx N ht

/-- **The `O(h)` rate for `C²` solutions** (perfect electric conductor, star-shaped domain): if the
components of `e^{tL} x` and `e^{tL} L x` are `C²` forms vanishing outside `Ω`
(`StarDomain.IsC2FormMin`) with bound `Λ` on `[0, T]`, then
`‖ξ(t) - ξₕ(t)‖ ≤ (1 + C_P) (1 + 2t) · 12 (Σᵢ B_{a+i}) h_N Λ`. [QuennevilleBelair2015], Thm 4.14;
[Arnold2018], Ch. 7 -/
theorem starPEC_rate {T Λ : ℝ} {hΛ : 0 ≤ Λ} {x}
    (hx : x ∈ (starPECRate M a T Λ hΛ).Data) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖(D.complexMin.window a 3).waveGroup.S t x -
        (D.complexMin.window a 3).totalD.graphFst
          ((starPEC M a).discrete N (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst (D.complexMin.window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, M.interpBound (a + i)) * (M.mesh N).meshSize * Λ) :=
  rate_regRate hx N ht

/-- **The `O(h^{s+1})` rate at every polynomial order** (perfect magnetic conductor, star-shaped
domain): for a sequence `S` of order `s` and `C^{s+2}` orbits with bound `Λ` on `[0, T]`
(`StarDomain.IsCsForm`), `‖ξ(t) - ξₕ(t)‖ ≤ (1 + C_P) (1 + 2t) · 12 (Σᵢ B_{a+i}) h_N^{s+1} Λ`.
[QuennevilleBelair2015], Thm 4.14; [AFW2010], §5 -/
theorem starPolyPMC_rate {S : PolySeq} {s : ℕ} {hS : FEM.PolyOrder n S s} {T Λ : ℝ}
    {hΛ : 0 ≤ Λ} {x} (hx : x ∈ (starPolyPMCRate M S hS a T Λ hΛ).Data) (N : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖(D.complex.window a 3).waveGroup.S t x -
        (D.complex.window a 3).totalD.graphFst
          ((starPolyPMC M S a).discrete N (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst (D.complex.window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, M.polyInterpBound S (a + i)) * (M.mesh N).meshSize ^ (s + 1) * Λ) :=
  rate_regRate hx N ht

/-- **The `O(h^{s+1})` rate at every polynomial order** (perfect electric conductor, star-shaped
domain), for `C^{s+2}` orbits vanishing outside `Ω` (`StarDomain.IsCsFormMin`).
[QuennevilleBelair2015], Thm 4.14; [AFW2010], §5 -/
theorem starPolyPEC_rate {S : PolySeq} {s : ℕ} {hS : FEM.PolyOrder n S s} {T Λ : ℝ}
    {hΛ : 0 ≤ Λ} {x} (hx : x ∈ (starPolyPECRate M S hS a T Λ hΛ).Data) (N : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖(D.complexMin.window a 3).waveGroup.S t x -
        (D.complexMin.window a 3).totalD.graphFst
          ((starPolyPEC M S a).discrete N (waveLift _ ⟨x, hx.1⟩) t)‖ ≤
      (1 + ellipticConst (D.complexMin.window a 3)) * (1 + 2 * t) *
        (12 * (∑ i : Fin 3, M.polyInterpBound S (a + i)) * (M.mesh N).meshSize ^ (s + 1) * Λ) :=
  rate_regRate hx N ht

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

end StarShaped

/-! ### A non-reducing constraint on the torus, through the approximating FEEC theorem -/

section TorusApprox

open Models.Torus.DeRham

variable {d : Type*} [Fintype d] [LinearOrder d] {a : ℕ}

/-- **The vanishing-field constraint on `𝕋ᵈ` through the approximating FEEC theorem**: the
verdict for the spectral Galerkin discretization with the constraint `E = 0`, `B = 0`
(`ConformingFamily.withConstraint`), together with the fact that the constraint does not reduce `L`
(`torus_not_isReducing_potential`), so the non-reducing departure clauses of the verdict are
not vacuous; `torus_potential_residual_of_approxFEEC` discharges the graded one. -/
theorem torus_potential_approxFEEC [Nonempty d] :
    ((torus d 0).withConstraint (potential ℂ fun i : Fin 3 => L2Form d (0 + i))
        isClosed_potential).toApprox.Verdict
      ((torus d 0).withConstraint (potential ℂ fun i : Fin 3 => L2Form d (0 + i))
        isClosed_potential).toCore ∧
    ¬ ((complex d).window 0 3).wave.IsReducing (potential ℂ fun i : Fin 3 => L2Form d (0 + i)) :=
  ⟨approxFEEC _ _, torus_not_isReducing_potential⟩

-- the instance arguments of `toApprox` at `L2Form d (0 + i)` need more than the default
set_option maxHeartbeats 400000 in
/-- **The non-reducing branch on the torus, read off the approximating FEEC theorem**, derived
from the graded clause of `torus_potential_approxFEEC` (`ApproxFEEC.Verdict.isReducing_iff_keeps`:
reducing iff kept forward in time), its departure clause `DissipFEEC.Verdict.leaves_smooth` and
the corollary `DissipFEEC.Verdict.detects`,
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
  obtain ⟨x, ⟨hxD, hxK⟩, t, ht, hout⟩ := V.leaves_smooth isClosed_potential
    (fun h => hnot ((V.isReducing_iff_keeps (fun _ _ h => ComplexShape.window_parity h)
      (fun _ hx => reversal_mem_totalSub hx) (dense_potential _)).2 h)) (dense_potential _) hT
  obtain ⟨hpos, hdet⟩ := V.detects (Q := (potential ℂ (fun i : Fin 3 => L2Form d (0 + i)) : Set _))
    isClosed_potential ⟨0, Submodule.zero_mem _⟩ ht.1 hout
  obtain ⟨hlim, hev⟩ := hdet (ConstrainedFEEC.mem_toCore_closure _ x) _
    (ConstrainedFEEC.tendsto_incl_ellipticProj _ ⟨x, hxD⟩)
  simp only [ApproxFEEC.S_eq_waveGroup _ ht.1] at hout hpos hlim hev
  refine ⟨⟨x, hxD⟩, hxK, t, ht, hout, hpos, hlim.congr fun N => ?_, hev.mono fun N hN => ?_⟩
  · exact congrArg (infDist · _) (ConstrainedFEEC.toApprox_sol _ N _ t)
  · rwa [ConstrainedFEEC.toApprox_sol] at hN

end TorusApprox

/-! ### Through the discrete complex: discrete Gauss laws -/

section DiscreteGauss

variable {𝕜 : Type*} [RCLike 𝕜] {W : Fin 3 → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  {H : HilbertComplex 𝕜 ComplexShape.fin3 W} {κ : Type*} (F : ConstrainedFEEC H κ)
  (Y : Submodule 𝕜 (W 2))

/-- The **discrete magnetic constraint** `Vₕ² ∩ Y`. -/
abbrev discreteMagnetic (h : κ) : Submodule 𝕜 ((F.V h).V 2) := Y.comap ((F.V h).V 2).subtype

instance (h : κ) : (discreteMagnetic F Y h).HasOrthogonalProjection :=
  haveI := FiniteDimensional.complete 𝕜 (discreteMagnetic F Y h); .ofCompleteSpace _

/-- The **discrete Gauss laws** `{0} × N(𝐝ₕ₀*) × (Vₕ² ∩ Y)` of the discrete complex `Vₕ` (the
adjoint is that of `Vₕ`: the discrete divergence). -/
abbrev discreteGauss (h : κ) : Submodule 𝕜 (PiLp 2 fun i => (F.V h).V i) :=
  gauss (F.V h).toHilbertComplex (discreteMagnetic F Y h)

/-- **The discrete Gauss laws are preserved exactly** by the discrete solutions of `ofComplex`
(conforming case, `ConstrainedFEEC.toComplex`), for every `Y ⊇ R(d₁)`: they form a reducing
subcomplex of the discrete complex `Vₕ`; in `W`, the magnetic component stays in `Y`. The discrete
solutions are those of the scheme (4.10) (`ConstrainedFEEC.toComplex_sol`). Discrete analogue of
the continuous Gauss propagation, cf. [QuennevilleBelair2015], Prop. 4.16 -/
theorem discreteGauss_propagates (hY : ∀ x : (H.d 1 2).domain, H.d 1 2 x ∈ Y) (h : κ)
    {v : PiLp 2 fun i => (F.V h).V i} (hv : v ∈ discreteGauss F Y h) (t : ℝ) :
    (((ApproxFEEC.ofComplex F.toComplex).group h).S t v : PiLp 2 fun i => (F.V h).V i) ∈
        discreteGauss F Y h ∧
      (ApproxFEEC.ofComplex F.toComplex).sol h v t 2 ∈ Y ∧
      (ApproxFEEC.ofComplex F.toComplex).sol h v t = F.toApprox.sol h (F.toXh h v) t := by
  have hYh : ∀ x : (((F.V h).toHilbertComplex).d 1 2).domain,
      ((F.V h).toHilbertComplex).d 1 2 x ∈ discreteMagnetic F Y h := fun x =>
    hY ⟨(x : (F.V h).V 1), (F.V h).le_domain 1 2 (x : (F.V h).V 1).2⟩
  have hmem' := (reducingSubcomplex_gaussFam _ _ hYh).waveGroup_mem t hv
  have e := ApproxFEEC.ofComplex_group F.toComplex h t v
  refine ⟨(congrArg (fun x : PiLp 2 (fun i => (F.V h).V i) => x ∈ discreteGauss F Y h) e).mpr
    hmem', ?_, F.toComplex_sol h v t⟩
  exact (congrArg (fun x : PiLp 2 W => x 2 ∈ Y) (ApproxFEEC.ofComplex_sol F.toComplex h v t)).mpr
    ((mem_gauss _ _).1 hmem').2.2

end DiscreteGauss

section CubeComplex

open Models.Cube Feec.Domain Feec.ExteriorFibre

variable {n : ℕ} [NeZero n] {a : ℤ}

/-- **`cubePMC` through the discrete complex** (`ApproxFEEC.ofComplex` of
`ConstrainedFEEC.toComplex`): the approximating FEEC theorem with the Whitney complexes as
discrete Hilbert complexes (zero inner-product defect), with exactly preserved discrete Gauss
laws `{0} × N(𝐝ₕ₀*) × (Vₕ² ∩ N(d))` whose magnetic component is read in `W` as `dB = 0`; the
discrete solutions are those of `cubePMC`. -/
theorem cubePMC_ofComplex :
    (ApproxFEEC.ofComplex (cubePMC n a).toComplex).Verdict
      (ApproxFEEC.ofComplexCore (cubePMC n a).toComplex) ∧
    (∀ N, (cubePMC n a).toFamily.J N = 1) ∧
    (∀ N (v : PiLp 2 fun i => ((cubePMC n a).V N).V i),
      v ∈ discreteGauss (cubePMC n a) (magnetic (FEM.complex n) a) N → ∀ t,
      (((ApproxFEEC.ofComplex (cubePMC n a).toComplex).group N).S t v :
          PiLp 2 fun i => ((cubePMC n a).V N).V i) ∈
          discreteGauss (cubePMC n a) (magnetic (FEM.complex n) a) N ∧
        (ApproxFEEC.ofComplex (cubePMC n a).toComplex).sol N v t 2 ∈
          magnetic (FEM.complex n) a ∧
        (ApproxFEEC.ofComplex (cubePMC n a).toComplex).sol N v t =
          (cubePMC n a).toApprox.sol N ((cubePMC n a).toXh N v) t) :=
  ⟨(cubePMC n a).toComplex_verdict, (cubePMC n a).toFamily_J,
    fun N _ hv t => discreteGauss_propagates _ _ (d_mem_magnetic (FEM.complex n) a) N hv t⟩

end CubeComplex

end Feec.Instances.Maxwell
