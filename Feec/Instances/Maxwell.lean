module

public import Feec.HilbertComplex.Approximation.Crown
public import Feec.HilbertComplex.Approximation.ApproxComplex
public import Feec.Physics.Maxwell.Constraints
public import Feec.Models.Torus.DeRhamGalerkin
public import Feec.Models.StarShapedWitness
public import Feec.Models.ConformingFamilies
public import Feec.Domain.VectorProxy

/-!
# Maxwell's equations as instances of the FEEC theorem

Maxwell's equations are the Hodge wave equation of a window `V a → V (a+1) → V (a+2)` of a
Hilbert complex, with the **Gauss laws** `σ = 0`, `d†E = 0`, `dB = 0` as constraint
(`Feec.Physics.Maxwell.Constraints`). This module makes them instances of the FEEC theorem
`Feec.HilbertComplex.ConformingFamily.feec`.

* **The Gauss laws of a short complex.** For a Hilbert complex `H` on `ComplexShape.fin3` and a
  closed `Y ⊇ R(d₁)`, `gauss H Y = {0} × N(d₀†) × Y` (`mem_gauss`) is a reducing subcomplex
  (`reducingSubcomplex_gaussFam`), so it reduces the wave operator (`isReducing_gauss`). For a
  window of a complex on `ComplexShape.up α` (`α = ℕ, ℤ`), `windowGauss H a` takes for `Y` the
  magnetic Gauss law `N(d : V (a+2) → V (a+3))` (`magnetic`, `isReducing_windowGauss`); the Gauss
  laws then propagate with no discretization (`windowGauss_propagates`,
  `windowGauss_propagates_strong`).
* **Maxwell discretizations.** `feec F a` is the conforming window of `F` with the Gauss laws
  (`ConformingFamily.windowFEEC`), for every conforming family `F` of `H`
  (`Feec.HilbertComplex.ConformingFamily`: finite-dimensional subcomplexes, cochain projections
  bounded uniformly in `L²`, the approximation property).
* **The FEEC theorem for Maxwell's equations** (`maxwellFEEC`, statement `Verdict`): the field
  `constrained` of the FEEC theorem at this window (well-posedness, convergence, the rate on every
  rate class, discrete cohomology), with the conclusions specific to the Gauss laws: they reduce
  `L`, propagate, and the Gauss residual of the semi-discrete solutions tends to `0`. Every other
  field of the FEEC theorem applies to the window as well: the approximating, heat and fully
  discrete theorems (`F.feec.wave a 3 (windowGauss H a) _`, …), and under a Jackson estimate `J`
  of `F` (`SubcomplexFamily.Jackson`; for the models `FEM.whitneyJackson`, `FEM.polyJackson`, …)
  the rate `(1 + C_P)(1 + 2t) O(hᵒʳᵈ⁽ˢ⁾)` for data whose orbit stays `s`-regular
  (`(F.feec_rated J).rate_wave a 3 (windowGauss H a) _`, on the classes
  `ConstrainedFEEC.RateClass.ofJackson`).
* **A non-reducing Maxwell constraint.** The vanishing-field constraint `potential 𝕜 W`
  (`E = 0`, `B = 0`; `mem_potential`) of a complex on `ComplexShape.fin3` does not reduce `L` as
  soon as `d₀ ≠ 0` (`not_isReducing_potential`, since `L (σ, 0, 0) = (0, dσ, 0)`), and `D(L) ∩ K`
  is dense in it (`dense_potential`). On the torus it is used with the field `wave` of the FEEC
  theorem (`torus_potential_approxFEEC`, whose graded departure clause
  `torus_potential_residual_of_approxFEEC` reads off).

**In vector proxies.** On every open `Ω ⊆ ℝ³` the vector proxies (`Feec.Domain.proxy`) are a
unitary isomorphism of `HΛ(Ω)` onto `H¹(Ω) --grad--> H(curl, Ω) --curl--> H(div, Ω) --div--> L²(Ω)`
(`Feec.Domain.deRhamVec_maximalComplex_eq_map`, `isChainIso_proxy`), carrying every conforming
family `F` of `HΛ(Ω)` to one of the vector complex (`vecFamily`; for the Whitney forms, the
vector proxies of the Whitney forms, classically the Lagrange, Nédélec edge and Raviart–Thomas
face elements). The window at `a = 0` is `H¹ → H(curl) → L²(Ω; ℝ³)` (`vecWindow_d_zero`,
`vecWindow_d_one`), its magnetic Gauss law is `div B = 0` (`vec_magnetic`), and its wave operator
is Maxwell's operator in vector form `L (σ, E, B) = (-grad†E, grad σ - curl†B, curl E)` for the
weak `grad` and `curl` (`vec_wave_apply`), the proxy of the forms one (`vec_wave_intertwines`).
The FEEC theorem for Maxwell's equations holds in this form (`vec_maxwellFEEC`; on the cube
`cubeVec_maxwellFEEC`).

The concrete instances below are pinned in the regression tests
`scripts/FeecCheck/MaxwellInstances.lean`, which also derive the per-instance rate statements of
earlier versions from the FEEC theorem.

**Through the discrete complex.** Every Maxwell discretization is also an instance of the
complex-level front end `Feec.HilbertComplex.ApproxFEEC.ofComplex`
(`Feec.HilbertComplex.ConstrainedFEEC.toComplex`: the subcomplexes as discrete Hilbert
complexes, zero inner-product defect, the same discrete solutions, and the rates of
`Feec.HilbertComplex.ConstrainedFEEC.RateClass.norm_sub_ofComplex_le`). There the **discrete Gauss
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
  DOFs): with the lowest-order Whitney forms of the Freudenthal meshes (`cubePMC`, `cubePEC`;
  `n = 3`, `a = 0` is the system `HΛ⁰(Q) → HΛ¹(Q) → L²Λ²(Q)`, and its PEC version
  `H̊Λ⁰(Q) → H̊Λ¹(Q) → L²Λ²(Q)`), with `O(h)` rates for `C²` orbits (`FEM.whitneyJackson`,
  `FEM.whitneyJacksonMin`; non-vacuity `zero_mem_cubePMC_ofJackson`,
  `zero_mem_cubePEC_ofJackson`), and **at every polynomial order**, with the finite element
  complexes of every admissible sequence `S` of the periodic table (`cubePolyPMC`,
  `cubePolyPEC`), with `O(h^{s+1})` rates for `C^{s+2}` orbits and sequences of order `s`
  (`FEM.polyJackson`, `FEM.polyJacksonMin`), and with the cubical elements `Q_b⁻Λ` of the
  uniform cubical meshes (perfect magnetic conductor, `cubeQMinusPMC`, `cubeQMinus_maxwellFEEC`;
  rates `O(h^{s+1})`, `s + 1 ≤ min b`, `FEM.qMinusJackson`).
* **Parallelepipeds `Ω = A · Q + b`** (every box), with the image Freudenthal meshes, both boundary
  conditions, Whitney forms and every admissible sequence (`paraPMC`, `paraPEC`, `paraPolyPMC`,
  `paraPolyPEC`; Jackson estimates `Parallelepiped.whitneyJackson`, `Parallelepiped.polyJackson`
  and their `Min` versions).
* **Domains star-shaped with respect to a ball**, with any uniformly shape-regular and
  quasi-uniform mesh family, both boundary conditions, Whitney forms and every admissible sequence
  (`starPMC`, `starPEC`, `starPolyPMC`, `starPolyPEC`; Jackson estimates
  `MeshFamily.whitneyJackson`, `MeshFamily.polyJackson` and their `Min` versions). The Poincaré
  inequality (`StarShaped.HasPoincare`) is needed only for the uniform discrete Poincaré inequality
  with its constant (`starPMC_discretePoincare`, `starPEC_discretePoincare`).
* **Unconditional discrete Poincaré inequalities**, from the proved Poincaré inequalities of the
  cube and the parallelepipeds: `cubePMC_discretePoincare`, `cubePEC_discretePoincare`,
  `paraPMC_discretePoincare`, `paraPEC_discretePoincare`.

No Poincaré inequality, closed range, compactness or exactness hypothesis enters the
well-posedness, propagation and convergence statements. The rate classes are hypotheses on the
data (regularity of the orbit on `[0, T]`). The Gauss constraint is reducing, so the departure
clauses of the verdict (non-reducing constraints) concern other constraints, such as the
vanishing-field constraint (`torus_potential_residual_of_approxFEEC`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.4 (Thms 4.6, 4.7), §4.6 (Thm 4.14), §4.9 (Prop. 4.16), §4.10 (Prop. 4.17)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3 (approximation property, bounded cochain projections, Thm 3.6), §5 (the spaces `P_rΛ`,
  `P_r⁻Λ`), §5.5 (smoothed projections)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 7 (rates for smooth
  solutions), Ch. 8 (evolution problems)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006],
  §2 (vector proxies)
* [P. Monk, *Finite Element Methods for Maxwell's Equations*][Monk2003] (Maxwell's equations in
  `(E, H)` form; the Raviart–Thomas and Nédélec elements)

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
conforming window of `F` with the Gauss laws as constraint (`ConformingFamily.windowFEEC`). -/
def feec : ConstrainedFEEC (H.window a 3) κ :=
  F.windowFEEC a 3 (windowGauss H a) (isClosed_gauss _ _)

/-- The projections of `feec F a` are bounded in `W` (those of the conforming family `F`). -/
theorem bound_feec : ∃ C, ∀ h i x, ‖((feec F a).π h).π i x‖ ≤ C * ‖x‖ := (F.window a 3).bound_π

variable [∀ i, NormedSpace ℝ (V i)] [∀ i, IsScalarTower ℝ 𝕜 (V i)]

/-- **The conclusions of the FEEC theorem for Maxwell's equations** (`maxwellFEEC`) in the window
`V a → V (a+1) → V (a+2)` of `H`, discretized by the conforming family `F`: those of the
constrained FEEC theorem for `feec F a` (well-posedness, convergence, the rate on every rate
class, the residual and departure clauses, discrete cohomology), and the conclusions specific to
the Gauss laws: they reduce `L`, propagate for all data and all times `t ∈ ℝ` and along strong
solutions, and the Gauss residual of the semi-discrete solutions from `D(L)` data satisfying them
tends to `0` uniformly on `[0, T]`. [QuennevilleBelair2015], Thms 4.6, 4.7, 4.14,
Props 4.16, 4.17 -/
structure Verdict : Prop extends (feec F a).Verdict where
  /-- the Gauss laws reduce the Maxwell operator `L = 𝐝 - 𝐝†` -/
  isReducing : (H.window a 3).wave.IsReducing (feec F a).K
  /-- the Gauss laws propagate for all data and all times `t ∈ ℝ` -/
  gauss_propagates : ∀ t, ∀ x ∈ (feec F a).K, (H.window a 3).waveGroup.S t x ∈ (feec F a).K
  /-- the Gauss laws propagate along strong solutions on `[0, T]` -/
  gauss_propagates_strong {T : ℝ} {U : ℝ → PiLp 2 fun i : Fin 3 => V (a + i)}
    (h0 : U 0 ∈ (feec F a).K) (hU : Evolution.IsStrongSolution (H.window a 3).wave (Icc 0 T) 0 U) :
    ∀ t ∈ Icc 0 T, U t ∈ (feec F a).K
  /-- the Gauss residual `dist(ξₕ(t), K)` of the semi-discrete solutions from `D(L)` data
  satisfying the Gauss laws tends to `0` uniformly on `[0, T]` -/
  gauss_residual_tendsto (x : (H.window a 3).wave.domain)
    (hxK : (x : PiLp 2 fun i : Fin 3 => V (a + i)) ∈ (feec F a).K) (T : ℝ) :
    TendstoUniformlyOn
      (fun h t => infDist ((H.window a 3).totalD.graphFst ((feec F a).discrete h (waveLift _ x) t))
        ((feec F a).K : Set (PiLp 2 fun i : Fin 3 => V (a + i)))) (fun _ => 0) (feec F a).l
      (Icc 0 T)

/-- **The FEEC theorem for Maxwell's equations**: for every conforming family `F` of a Hilbert
complex on `ℕ` or `ℤ` and every degree `a`, the field `constrained` of the FEEC theorem
`ConformingFamily.feec` at the window `V a → V (a+1) → V (a+2)` with the Gauss laws, which reduce
`L` (`isReducing_windowGauss`). The other fields of the FEEC theorem hold at this window as well:
the approximating, heat and fully discrete ones, and, under a Jackson estimate `J`, the rates
(`(F.feec_rated J).rate_wave a 3 (windowGauss H a) (isClosed_gauss _ _)`).
[QuennevilleBelair2015], Thms 4.6, 4.7, 4.14, Props 4.16, 4.17 -/
theorem maxwellFEEC : Verdict F a :=
  have V := F.feec.constrained a 3 (windowGauss H a) (isClosed_gauss _ _)
  { V with
    isReducing := isReducing_windowGauss H a
    gauss_propagates := windowGauss_propagates H a
    gauss_propagates_strong := windowGauss_propagates_strong H a
    gauss_residual_tendsto := V.residual_tendsto (isReducing_windowGauss H a) }

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

/-- **Maxwell's equations with a perfect magnetic conductor on the cube** `Q = (0, ½)ⁿ` (degree `a`;
`n = 3`, `a = 0` is the system `HΛ⁰(Q) → HΛ¹(Q) → L²Λ²(Q)`), discretized by the lowest-order Whitney
forms of the Freudenthal meshes with the smoothed projections (`FEM.whitneyFamily`), as a
constrained FEEC discretization with the Gauss laws. -/
def cubePMC (a : ℤ) : ConstrainedFEEC ((FEM.complex n).window a 3) ℕ :=
  feec (FEM.whitneyFamily n) a

/-- **Maxwell's equations with a perfect electric conductor on the cube** (vanishing tangential
traces: `H̊Λ⁰(Q) → H̊Λ¹(Q) → L²Λ²(Q)` for `n = 3`, `a = 0`), discretized by the Whitney forms with
vanishing boundary DOFs (`FEM.whitneyFamilyMin`), as a constrained FEEC discretization with the
Gauss laws. -/
def cubePEC (a : ℤ) : ConstrainedFEEC ((FEM.complexMin n).window a 3) ℕ :=
  feec (FEM.whitneyFamilyMin n) a

/-- **Maxwell's equations with a perfect magnetic conductor on the cube at every polynomial
order**: the finite element complexes of an admissible sequence `S` (every `P_rΛ`, `P_r⁻Λ` and
mixed sequence of the periodic table, `FEM.polyFamily`) with the smoothed projections. -/
def cubePolyPMC (S : PolySeq) (a : ℤ) : ConstrainedFEEC ((FEM.complex n).window a 3) ℕ :=
  feec (FEM.polyFamily n S) a

/-- **Maxwell's equations with a perfect electric conductor on the cube at every polynomial
order** (`FEM.polyFamilyMin`). -/
def cubePolyPEC (S : PolySeq) (a : ℤ) : ConstrainedFEEC ((FEM.complexMin n).window a 3) ℕ :=
  feec (FEM.polyFamilyMin n S) a

/-- **Maxwell's equations with a perfect magnetic conductor on the cube with the cubical elements**
`Q_b⁻Λ` of the uniform cubical meshes (`FEM.qMinusFamily`; for `b = fun _ => r`, `Q_r⁻Λ`: in the
degrees `0, 1, 2` of `n = 3`, the tensor-product Lagrange, the first-kind Nédélec edge and
Raviart–Thomas face elements of hexahedra). -/
def cubeQMinusPMC {b : Fin n → ℕ} (hb : ∀ j, 1 ≤ b j) (a : ℤ) :
    ConstrainedFEEC ((FEM.complex n).window a 3) ℕ :=
  feec (FEM.qMinusFamily n hb) a

variable {n} {a : ℤ}

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

/-- **Non-vacuity of the Whitney rate classes on the cube**: the zero datum lies in the rate class
of the Jackson estimate of the Whitney forms (`FEM.whitneyJackson`, `C²` orbits with bound `Λ`
on `[0, T]`) on every Maxwell window. -/
theorem zero_mem_cubePMC_ofJackson {T Λ : ℝ} (hΛ : 0 ≤ Λ) :
    (0 : PiLp 2 _) ∈ (ConstrainedFEEC.RateClass.ofJackson (cubePMC n a)
      ((FEM.whitneyJackson n).window a 3) T () hΛ).Data :=
  ConstrainedFEEC.RateClass.zero_mem_ofDegreewise fun _ => isC2Form_zero _ hΛ

/-- **Non-vacuity of the Whitney rate classes with vanishing boundary DOFs on the cube**
(`FEM.whitneyJacksonMin`, `C²` orbits vanishing outside `Q`). -/
theorem zero_mem_cubePEC_ofJackson {T Λ : ℝ} (hΛ : 0 ≤ Λ) :
    (0 : PiLp 2 _) ∈ (ConstrainedFEEC.RateClass.ofJackson (cubePEC n a)
      ((FEM.whitneyJacksonMin n).window a 3) T () hΛ).Data :=
  ConstrainedFEEC.RateClass.zero_mem_ofDegreewise fun _ => isC2FormMin_zero _ hΛ

/-- **The FEEC theorem for Maxwell's equations on the cubical meshes of the cube**, with the
cubical elements `Q_b⁻Λ` (`cubeQMinusPMC`; `Q_r⁻Λ`, Nédélec's first-kind edge elements on
hexahedra in degree `1`): the Maxwell verdict (`maxwellFEEC`) and the rated FEEC theorem
(`ConformingFamily.feec_rated`) for the Jackson estimate `FEM.qMinusJackson`: the static,
semidiscrete and heat errors are `O(h^{s+1})` along `IsCsForm s` orbits for `s + 1 ≤ min b`, and
the fully discrete errors `O(h^{s+1} + τᵖ)` along smooth comparisons of order `p + 1` (temporal
error `τᵖ ‖Lₕ^{p+1} v‖`, `ConformingFamily.Verdict.Rated.rate_full`). -/
theorem cubeQMinus_maxwellFEEC {b : Fin n → ℕ} (hb : ∀ j, 1 ≤ b j) :
    Verdict (FEM.qMinusFamily n hb) a ∧
      ConformingFamily.Verdict.Rated (FEM.qMinusFamily n hb) (FEM.qMinusJackson n hb) :=
  ⟨maxwellFEEC _ a, (FEM.qMinusFamily n hb).feec_rated _⟩

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

/-- **Maxwell's equations with a perfect electric conductor on the parallelepiped** `Ω`, with the
Whitney forms with vanishing boundary DOFs (`Parallelepiped.whitneyFamilyMin`). -/
def paraPEC (a : ℤ) : ConstrainedFEEC ((complexMin A b).window a 3) ℕ :=
  feec (whitneyFamilyMin A hA b) a

/-- **Maxwell's equations with a perfect magnetic conductor on the parallelepiped at every
polynomial order**: the finite element complexes of an admissible sequence `S`
(`Parallelepiped.polyFamily`). -/
def paraPolyPMC (S : PolySeq) (a : ℤ) : ConstrainedFEEC ((complex A b).window a 3) ℕ :=
  feec (polyFamily A hA b S) a

/-- **Maxwell's equations with a perfect electric conductor on the parallelepiped at every
polynomial order** (`Parallelepiped.polyFamilyMin`). -/
def paraPolyPEC (S : PolySeq) (a : ℤ) : ConstrainedFEEC ((complexMin A b).window a 3) ℕ :=
  feec (polyFamilyMin A hA b S) a

end Parallelepiped

/-! ### The Poincaré inequality of a Maxwell window -/

/-- **The Poincaré inequality of a complex gives that of its Maxwell window**, in the form of
the discrete Poincaré theorem `constrainedFEEC_discretePoincare`. -/
theorem window_poincare {W : ℤ → Type*} [∀ i, NormedAddCommGroup (W i)]
    [∀ i, InnerProductSpace ℝ (W i)] [∀ i, CompleteSpace (W i)]
    {H : HilbertComplex ℝ (ComplexShape.up ℤ) W} {cP : ℝ}
    (hP : Models.StarShaped.HasPoincare H cP) (a : ℤ) {i j : Fin 3}
    (hij : (ComplexShape.window 3).Rel i j) (z : ((H.window a 3).d i j).domain)
    (hz : (z : W (a + i)) ∈ ((H.window a 3).cycles i)ᗮ) :
    ‖(z : W (a + i))‖ ≤ cP * ‖(H.window a 3).d i j z‖ := by
  have hrel : (ComplexShape.up ℤ).Rel (a + (i : ℕ)) (a + (j : ℕ)) := by
    simp only [ComplexShape.window_rel] at hij
    simp only [ComplexShape.up_Rel]; omega
  have e : (H.window a 3).cycles i = H.cycles (a + (i : ℕ)) := by
    unfold HilbertComplex.cycles
    rw [ComplexShape.next_eq' _ hij, ComplexShape.next_eq' _ hrel]; rfl
  exact hP _ _ hrel z (e ▸ hz)

/-! ### Domains star-shaped with respect to a ball -/

section StarShaped

open Models.Cube Models.StarShaped Feec.Domain Feec.ExteriorFibre

variable {n : ℕ} [NeZero n] {D : StarDomain n} (M : MeshFamily D)

/-- **Maxwell's equations with a perfect magnetic conductor on a domain star-shaped with respect
to a ball**, with the Whitney forms of a uniformly shape-regular, quasi-uniform mesh family
(`MeshFamily.whitneyFamily`), as a constrained FEEC discretization with the Gauss laws. No
Poincaré inequality is needed. -/
def starPMC (a : ℤ) : ConstrainedFEEC (D.complex.window a 3) ℕ :=
  feec M.whitneyFamily a

/-- **Maxwell's equations with a perfect electric conductor on a domain star-shaped with respect
to a ball**, with the Whitney forms with vanishing boundary DOFs (`MeshFamily.whitneyFamilyMin`). -/
def starPEC (a : ℤ) : ConstrainedFEEC (D.complexMin.window a 3) ℕ :=
  feec M.whitneyFamilyMin a

/-- **Maxwell's equations with a perfect magnetic conductor on a star-shaped domain at every
polynomial order**: the finite element complexes of an admissible sequence `S` on the mesh family
(`MeshFamily.polyFamily`). -/
def starPolyPMC (S : PolySeq) (a : ℤ) : ConstrainedFEEC (D.complex.window a 3) ℕ :=
  feec (M.polyFamily S) a

/-- **Maxwell's equations with a perfect electric conductor on a star-shaped domain at every
polynomial order** (`MeshFamily.polyFamilyMin`). -/
def starPolyPEC (S : PolySeq) (a : ℤ) : ConstrainedFEEC (D.complexMin.window a 3) ℕ :=
  feec (M.polyFamilyMin S) a

variable {M} {a : ℤ}

/-- **The uniform discrete Poincaré inequality** for the Maxwell window on a star-shaped domain
(perfect magnetic conductor), under the Poincaré inequality of `HΛ(Ω)` (the only place where it
is needed). [AFW2010], Thm 3.6 -/
theorem starPMC_discretePoincare {cP : ℝ} (hP : HasPoincare D.complex cP) {i j : Fin 3}
    (hij : (ComplexShape.window 3).Rel i j) :
    ∃ C, 0 ≤ C ∧ ∀ N, ∀ x (hx : x ∈ ((starPMC M a).V N).V i),
      (∀ y ∈ ((starPMC M a).V N).cyclesW i, ⟪y, x⟫_ℝ = 0) →
        ‖x‖ ≤ C * cP * ‖(D.complex.window a 3).d i j ⟨x, ((starPMC M a).V N).le_domain i j hx⟩‖ :=
  constrainedFEEC_discretePoincare (starPMC M a)
    (bound_feec M.whitneyFamily a) hij (window_poincare hP a hij)

/-- **The uniform discrete Poincaré inequality** for the Maxwell window on a star-shaped domain
(perfect electric conductor), under the Poincaré inequality of `H̊Λ(Ω)`. [AFW2010], Thm 3.6 -/
theorem starPEC_discretePoincare {cP : ℝ} (hP : HasPoincare D.complexMin cP) {i j : Fin 3}
    (hij : (ComplexShape.window 3).Rel i j) :
    ∃ C, 0 ≤ C ∧ ∀ N, ∀ x (hx : x ∈ ((starPEC M a).V N).V i),
      (∀ y ∈ ((starPEC M a).V N).cyclesW i, ⟪y, x⟫_ℝ = 0) →
        ‖x‖ ≤ C * cP *
          ‖(D.complexMin.window a 3).d i j ⟨x, ((starPEC M a).V N).le_domain i j hx⟩‖ :=
  constrainedFEEC_discretePoincare (starPEC M a)
    (bound_feec M.whitneyFamilyMin a) hij (window_poincare hP a hij)

end StarShaped

/-! ### Unconditional discrete Poincaré inequalities: the cube and parallelepipeds -/

section UnconditionalPoincare

open Models.Cube Models.StarShaped Feec.Domain Feec.ExteriorFibre

variable {n : ℕ} [NeZero n] {a : ℤ}

/-- **The uniform discrete Poincaré inequality on the cube** (perfect magnetic conductor), with
`c_P = (2π)⁻¹` (`CubeWitness.hasPoincare`). [AFW2010], Thm 3.6 -/
theorem cubePMC_discretePoincare {i j : Fin 3} (hij : (ComplexShape.window 3).Rel i j) :
    ∃ C, 0 ≤ C ∧ ∀ N, ∀ x (hx : x ∈ ((cubePMC n a).V N).V i),
      (∀ y ∈ ((cubePMC n a).V N).cyclesW i, ⟪y, x⟫_ℝ = 0) →
        ‖x‖ ≤ C * (2 * Real.pi)⁻¹ *
          ‖((FEM.complex n).window a 3).d i j ⟨x, ((cubePMC n a).V N).le_domain i j hx⟩‖ :=
  constrainedFEEC_discretePoincare (cubePMC n a) (bound_feec (FEM.whitneyFamily n) a) hij
    (window_poincare (H := FEM.complex n) (CubeWitness.hasPoincare n) a hij)

/-- **The uniform discrete Poincaré inequality on the cube** (perfect electric conductor), with
`c_P = (2π)⁻¹` (`CubeWitness.hasPoincareMin`). [AFW2010], Thm 3.6 -/
theorem cubePEC_discretePoincare {i j : Fin 3} (hij : (ComplexShape.window 3).Rel i j) :
    ∃ C, 0 ≤ C ∧ ∀ N, ∀ x (hx : x ∈ ((cubePEC n a).V N).V i),
      (∀ y ∈ ((cubePEC n a).V N).cyclesW i, ⟪y, x⟫_ℝ = 0) →
        ‖x‖ ≤ C * (2 * Real.pi)⁻¹ *
          ‖((FEM.complexMin n).window a 3).d i j ⟨x, ((cubePEC n a).V N).le_domain i j hx⟩‖ :=
  constrainedFEEC_discretePoincare (cubePEC n a) (bound_feec (FEM.whitneyFamilyMin n) a) hij
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
  constrainedFEEC_discretePoincare (paraPMC A hA b a)
    (bound_feec (Feec.Models.Parallelepiped.whitneyFamily A hA b) a) hij
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
  constrainedFEEC_discretePoincare (paraPEC A hA b a)
    (bound_feec (Feec.Models.Parallelepiped.whitneyFamilyMin A hA b) a) hij
    (window_poincare (Feec.Models.Parallelepiped.poincare_min A hA b) a hij)

end UnconditionalPoincare

/-! ### A non-reducing constraint on the torus, through the approximating FEEC theorem -/

section TorusApprox

open Models.Torus.DeRham

variable {d : Type*} [Fintype d] [LinearOrder d] {a : ℕ}

/-- **The vanishing-field constraint on `𝕋ᵈ` through the approximating FEEC theorem**: the verdict
for the spectral Galerkin discretization with the constraint `E = 0`, `B = 0` (the field `wave` of
the FEEC theorem `ConformingFamily.feec` at this constraint), together with the fact that the
constraint does not reduce `L` (`torus_not_isReducing_potential`), so the non-reducing departure
clauses of the verdict are not vacuous; `torus_potential_residual_of_approxFEEC` discharges the
graded one. -/
theorem torus_potential_approxFEEC [Nonempty d] :
    ((torusFamily d).windowFEEC 0 3 (potential ℂ fun i : Fin 3 => L2Form d (0 + i))
        isClosed_potential).toApprox.Verdict
      ((torusFamily d).windowFEEC 0 3 (potential ℂ fun i : Fin 3 => L2Form d (0 + i))
        isClosed_potential).toCore ∧
    ¬ ((complex d).window 0 3).wave.IsReducing (potential ℂ fun i : Fin 3 => L2Form d (0 + i)) :=
  ⟨(torusFamily d).feec.wave 0 3 _ isClosed_potential, torus_not_isReducing_potential⟩

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

/-! ### Maxwell's equations in vector proxies -/

section VectorProxy

open Feec.Domain

variable {Ω : Set (Fin 3 → ℝ)} (hΩ : IsOpen Ω) {κ : Type*}

/-- **The vector proxies are an isomorphism of Hilbert complexes**
`H¹(Ω) → H(curl, Ω) → H(div, Ω) → L²(Ω)` `≅` `HΛ(Ω)` (`deRhamVec_maximalComplex_eq_map`). -/
theorem isChainIso_proxy :
    IsChainIso ((deRhamVec ℝ 1).maximalComplex hΩ) ((deRham ℝ 3).maximalComplex hΩ)
      fun k => (proxy k).toContinuousLinearEquiv.symm := by
  rw [deRhamVec_maximalComplex_eq_map hΩ]
  exact (isChainIso_transport _ _).symm

/-- **The vector proxies of a conforming family** `F` of `HΛ(Ω)`: the subcomplexes
`P Vₕ ⊆ H¹(Ω) × H(curl, Ω) × H(div, Ω) × L²(Ω)` with the cochain projections `P πₕ P⁻¹`. For the
Whitney forms these are their vector proxies (classically, the Lagrange `P₁`, Nédélec edge,
Raviart–Thomas face and piecewise constant elements; not formalized here). [AFW2006], §2 -/
def vecFamily (F : ConformingFamily ((deRham ℝ 3).maximalComplex hΩ) κ) :
    ConformingFamily ((deRhamVec ℝ 1).maximalComplex hΩ) κ :=
  haveI : ∀ h i, FiniteDimensional ℝ (((isChainIso_proxy hΩ).comapSub (F.V h)).V i) :=
    fun h i => haveI := F.finiteDimensional h
      (isChainIso_proxy hΩ).finiteDimensional_comapSub _ i
  (isChainIso_proxy hΩ).comapFamily F (fun h => (isChainIso_proxy hΩ).comapSub (F.V h))
    (fun _ _ _ => Iff.rfl) (M := 1) (M' := 1)
    (fun k => (proxy k).symm.toLinearIsometry.norm_toContinuousLinearMap_le)
    (fun k => (proxy k).toLinearIsometry.norm_toContinuousLinearMap_le)

theorem mem_vecFamily_V_iff (F : ConformingFamily ((deRham ℝ 3).maximalComplex hΩ) κ) (h : κ)
    (k : ℤ) (u : L2F ℝ Ω (vecIdx 1 k)) :
    u ∈ ((vecFamily hΩ F).V h).V k ↔ (proxy k).symm u ∈ (F.V h).V k := Iff.rfl

/-- The Maxwell window `H¹(Ω) --grad--> H(curl, Ω) --curl--> L²(Ω; ℝ³)` of the vector-proxy
complex: its first differential is the weak gradient, -/
theorem vecWindow_d_zero :
    (((deRhamVec ℝ 1).maximalComplex hΩ).window 0 3).d 0 1 = (gradOp 3 1).maximal Ω :=
  (deRhamVec ℝ 1).maximalComplex_d hΩ 0

/-- its second differential is the weak curl, -/
theorem vecWindow_d_one :
    (((deRhamVec ℝ 1).maximalComplex hΩ).window 0 3).d 1 2 = (curlOp 1).maximal Ω :=
  (deRhamVec ℝ 1).maximalComplex_d hΩ 1

/-- and its magnetic Gauss law is `div B = 0` for the weak divergence. -/
theorem vec_magnetic :
    magnetic ((deRhamVec ℝ 1).maximalComplex hΩ) 0 = ((divOp 3 1).maximal Ω).ker :=
  congrArg LinearPMap.ker ((deRhamVec ℝ 1).maximalComplex_d hΩ 2)

private theorem apply_of_eq {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] {T S : E →ₗ.[ℝ] F} (e : T = S) {v : E} (h : v ∈ T.domain) :
    T ⟨v, h⟩ = S ⟨v, e ▸ h⟩ := by
  subst e; rfl

/-- **Maxwell's operator in vector form** on the window `H¹(Ω) → H(curl, Ω) → L²(Ω; ℝ³)`:
`L (σ, E, B) = (-grad†E, grad σ - curl†B, curl E)` for the weak `grad` and `curl`
(`wave_apply_fin3_zero`, `_one`, `_two` with `vecWindow_d_zero`, `vecWindow_d_one`). Informally,
with `B = -H` and `curl† = curl` on `H̊(curl)` this is `Ė = curl H`, `Ḣ = -curl E`. -/
theorem vec_wave_apply (x : (((deRhamVec ℝ 1).maximalComplex hΩ).window 0 3).wave.domain) :
    ((((deRhamVec ℝ 1).maximalComplex hΩ).window 0 3).wave x) 0 =
        -((gradOp 3 1).maximal Ω)† ⟨x.1 1, by rw [← vecWindow_d_zero hΩ]; exact x.2.2 1 0⟩ ∧
      ((((deRhamVec ℝ 1).maximalComplex hΩ).window 0 3).wave x) 1 =
        (gradOp 3 1).maximal Ω ⟨x.1 0, by rw [← vecWindow_d_zero hΩ]; exact x.2.1 0 1⟩ -
          ((curlOp 1).maximal Ω)† ⟨x.1 2, by rw [← vecWindow_d_one hΩ]; exact x.2.2 2 1⟩ ∧
      ((((deRhamVec ℝ 1).maximalComplex hΩ).window 0 3).wave x) 2 =
        (curlOp 1).maximal Ω ⟨x.1 1, by rw [← vecWindow_d_one hΩ]; exact x.2.1 1 2⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [wave_apply_fin3_zero]
    exact congrArg Neg.neg (apply_of_eq (congrArg (·†) (vecWindow_d_zero hΩ)) _)
  · rw [wave_apply_fin3_one]
    exact congrArg₂ (· - ·) (apply_of_eq (vecWindow_d_zero hΩ) _)
      (apply_of_eq (congrArg (·†) (vecWindow_d_one hΩ)) _)
  · rw [wave_apply_fin3_two]
    exact apply_of_eq (vecWindow_d_one hΩ) _

/-- **The vector proxies carry the forms Maxwell operator to Maxwell's operator in vector form**
(`vec_wave_apply`): `L_vec (P x) = P (L x)`. -/
theorem vec_wave_intertwines :
    LinearPMap.Intertwines
      (totalMap fun i : Fin 3 => (proxy (Ω := Ω) (0 + (i : ℤ))).toContinuousLinearEquiv)
      (((deRham ℝ 3).maximalComplex hΩ).window 0 3).wave
      (((deRhamVec ℝ 1).maximalComplex hΩ).window 0 3).wave := by
  rw [deRhamVec_maximalComplex_eq_map hΩ]
  exact wave_transport (s := 1) one_pos fun i x y => by
    simpa using (proxy (0 + (i : ℤ))).inner_map_map x y

/-- **Maxwell's equations in vector proxies** on an open `Ω ⊆ ℝ³`: the window
`H¹(Ω) → H(curl, Ω) → L²(Ω; ℝ³)` with the Gauss laws `σ = 0`, `grad†E = 0`, `div B = 0`,
discretized by the vector proxies of a conforming family `F` of `HΛ(Ω)` (`vecFamily`). -/
def vecFEEC (F : ConformingFamily ((deRham ℝ 3).maximalComplex hΩ) κ) :
    ConstrainedFEEC (((deRhamVec ℝ 1).maximalComplex hΩ).window 0 3) κ :=
  feec (vecFamily hΩ F) 0

/-- **The FEEC theorem for Maxwell's equations in vector proxies** (`maxwellFEEC` for
`vecFamily`). -/
theorem vec_maxwellFEEC (F : ConformingFamily ((deRham ℝ 3).maximalComplex hΩ) κ) :
    Verdict (vecFamily hΩ F) 0 :=
  maxwellFEEC _ 0

/-- **Maxwell's equations with a perfect magnetic conductor on the cube in vector proxies**:
`H¹(Q) → H(curl, Q) → L²(Q; ℝ³)` (`cubePMC 3 0` in proxies), discretized by the vector proxies
of the Whitney forms of the Freudenthal meshes (`FEM.whitneyFamily`; classically, the Lagrange,
Nédélec edge and Raviart–Thomas face elements). -/
def cubeVecPMC : ConstrainedFEEC
    (((deRhamVec ℝ 1).maximalComplex (Models.Cube.FEM.isOpen_cubeDomain 3)).window 0 3) ℕ :=
  vecFEEC _ (Models.Cube.FEM.whitneyFamily 3)

/-- **The FEEC theorem for Maxwell's equations on the cube in vector proxies** (`cubeVecPMC`):
well-posedness, convergence and rates, the propagation of the Gauss laws and their residual, for
the vector-proxy Whitney discretization of `H¹ → H(curl) → L²`. -/
theorem cubeVec_maxwellFEEC :
    Verdict (vecFamily (Models.Cube.FEM.isOpen_cubeDomain 3) (Models.Cube.FEM.whitneyFamily 3)) 0 :=
  vec_maxwellFEEC _ _

end VectorProxy

end Feec.Instances.Maxwell
