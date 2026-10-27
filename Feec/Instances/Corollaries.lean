module

public import Feec.HilbertComplex.Approximation.Crown
public import Feec.HilbertComplex.Reducing
public import Feec.Instances.Maxwell
public import Feec.Models.Cube.HeatFEM

/-!
# Corollaries of the FEEC theorem: acoustics, slip Stokes, time stepping, magnetostatics

Short corollaries of the FEEC theorem (`Feec.HilbertComplex.ConformingFamily.feec`) for every
conforming family `F` of a Hilbert complex on `ℕ` or `ℤ`, and their instances on the finite
element families of the models (every admissible sequence `S` of the periodic table on the
Freudenthal meshes of the cube `Q = (0, ½)ⁿ`, on parallelepipeds and on star-shaped domains,
`Feec.Models.ConformingFamilies`):

* **acoustic waves** (`acoustic`): the Hodge wave equation of the window `Vᵃ → V^{a+1}` with no
  constraint (`acousticFEEC`). On the de Rham complex, `a = 0` is the pressure–velocity system
  `p' = div u`, `u' = grad p` (`p` a `0`-form, `u` a `1`-form) and `a = n - 1` its mixed form with
  `u` an `(n - 1)`-form and `p` an `n`-form; the natural boundary condition of `HΛ` is a rigid wall
  (`u · ν = 0`) at `a = 0` and a pressure release (`p = 0`) at `a = n - 1`, and the essential one
  of `H̊Λ` the other way round. The constrained FEEC verdict holds: well-posedness, energy
  conservation, convergence from every datum in `L²`, the rates (`Cube.FEM.acoustic`,
  `Parallelepiped.acoustic`, `StarShaped.MeshFamily.acoustic`);
* **unsteady Stokes flow with slip boundary conditions** (`slipStokes`): the Hodge heat equation
  of a window with the constraint `ker 𝐝†` (`slipStokesFEEC`). In degree `1` of `HΛ(Ω)` a
  velocity `u` orthogonal to the gradients (`div u = 0` and `u · ν = 0`) is a datum
  `single 1 u ∈ ker 𝐝†` (`HilbertComplex.single_mem_ker_adjoint_totalD_of_mem_orthogonal`).
  `ker 𝐝†` reduces the Hodge Laplacian (`HilbertComplex.isReducing_hodgeLaplacian_ker_adjoint`),
  so on these fields `Δ` is the Stokes operator: the pressure gradient, the part of `Δ u` along
  the gradients, vanishes, and the Hodge heat flow is `∂ₜ u + d†d u = 0` (`curl curl u` in `ℝ³`),
  `div u = 0`, with the slip conditions `u · ν = 0`, `curl u × ν = 0` ([GiraultRaviart1986];
  [AFW2010], §3.2). The heat verdict has a kept constraint: the discrete heat flows from every
  convergent family of discrete data of a datum in `ker 𝐝†` have constraint residuals tending to
  `0`. On the cube, `n ≥ 2` (`Cube.FEM.slipStokes`), a nonzero velocity lies in the constraint
  (`HilbertComplex.exists_single_mem_ker_adjoint_totalD`, since `x₀ dx₁` is not closed), and the
  discrete flows from its projections have vanishing residuals;
* **Crank–Nicolson and the θ-schemes** for Maxwell's equations (`maxwell_fullyDiscrete`: the
  fully discrete verdicts, exact energy conservation of Crank–Nicolson, Gauss-law residuals
  tending to `0` as `h, τ → 0`; on the cube at every polynomial order,
  `Cube.FEM.maxwell_crankNicolson`; the reading through the discrete complex of the Whitney
  scheme is `Feec.Instances.FullyDiscrete.maxwell_cubePMC_crankNicolson`) and for the Hodge heat equation (`heat_fullyDiscrete`; on the
  cube with a nonzero datum, `Cube.FEM.heat_crankNicolson`), read from the field `full` of the
  FEEC theorem;
* **magnetostatics** (`Cube.FEM.magnetostatic`, `Parallelepiped.magnetostatic`): the static FEEC
  verdict of `HΛ` and `H̊Λ` in degrees `1` and `2` in dimension `3`, the mixed formulations of
  `curl curl u - grad div u = f` with natural and essential boundary conditions
  ([Monk2003]; [Hiptmair2002]); for every conforming family, the discrete mixed
  solutions of every source `f` converge (`mixed_converges`).

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.2 (the Hodge Laplacian), Thms 3.4–3.9
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thms 4.6, 4.7, 4.14, Prop. 4.17
* [P. Joly, *Variational Methods for Time-Dependent Wave Propagation Problems*][Joly2003]
* [V. Girault, P.-A. Raviart, *Finite Element Methods for Navier–Stokes Equations*][GiraultRaviart1986]
* [P. Monk, *Finite Element Methods for Maxwell's Equations*][Monk2003]
* [R. Hiptmair, *Finite elements in computational electromagnetism*][Hiptmair2002]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006], Ch. 7–9

Bibliography: [references.bib](../../docs/references.bib)
-/

open Set Filter Topology Metric LinearPMap

@[expose] public noncomputable section

namespace Feec.Instances.Corollaries

open Feec.HilbertComplex

/-! ### For every conforming family -/

section Family

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [AddCommMonoidWithOne α] [IsCancelAdd α] [CharZero α]
  {V : α → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)]
  [∀ i, CompleteSpace (V i)] [∀ i, NormedSpace ℝ (V i)] [∀ i, IsScalarTower ℝ 𝕜 (V i)]
  {H : HilbertComplex 𝕜 (ComplexShape.up α) V} {κ : Type*} (F : ConformingFamily H κ)

/-- **The acoustic discretization** in degrees `a, a + 1`: the window `Vₕᵃ → Vₕ^{a+1}` of `F` with
no constraint. -/
abbrev acousticFEEC (a : α) : ConstrainedFEEC (H.window a 2) κ :=
  F.windowFEEC a 2 ⊤ isClosed_univ

/-- **Acoustic waves**: the constrained and the approximating FEEC verdicts of the Hodge wave
equation of the window `Vᵃ → V^{a+1}` (fields `constrained` and `wave` of the FEEC theorem).
[QuennevilleBelair2015], Thms 4.6, 4.7, 4.14; [Joly2003] -/
theorem acoustic (a : α) :
    (acousticFEEC F a).Verdict ∧ (acousticFEEC F a).toApprox.Verdict (acousticFEEC F a).toCore :=
  ⟨F.feec.constrained a 2 _ _, F.feec.wave a 2 _ _⟩

/-- **The slip Stokes discretization**: the window `Vₕᵃ → ⋯ → Vₕ^{a+m-1}` of `F` with the
constraint `ker 𝐝†` (closed: `𝐝†` is closed). -/
abbrev slipStokesFEEC (a : α) (m : ℕ) : ConstrainedFEEC (H.window a m) κ :=
  F.windowFEEC a m ((H.window a m).totalD†).ker
    (isClosed_ker (adjoint_isClosed (H.window a m).dense_totalD_domain))

/-- **Unsteady Stokes flow with slip boundary conditions**, the Hodge heat equation on `ker 𝐝†`:
the heat FEEC verdict of the window with the constraint `ker 𝐝†`, the constraint is kept by the
heat flow (it reduces `-Δ`, `isReducing_hodgeLaplacian_ker_adjoint`, so the pressure is
eliminated), and for every datum `x ∈ ker 𝐝†` (in degree `1` of `HΛ(Ω)`, a velocity with
`div u = 0`, `u · ν = 0`) and every family of discrete data with `ιₕ vₕ → x` the constraint
residuals of the discrete heat flows tend to `0` uniformly on `[0, T]`. [AFW2010], §3.2;
[GiraultRaviart1986] -/
theorem slipStokes (a : α) (m : ℕ) (hcr : ∀ i, (H.window a m).ClosedRangeAt i)
    [∀ i, FiniteDimensional 𝕜 ((H.window a m).harmonic i)] :
    (slipStokesFEEC F a m).toHeat.Verdict ((slipStokesFEEC F a m).heatCore hcr) ∧
      (slipStokesFEEC F a m).toHeat.Keeps (slipStokesFEEC F a m).toHeat.K ∧
      ∀ {x} (_ : x ∈ ((H.window a m).totalD†).ker) {v : ∀ h, (slipStokesFEEC F a m).toHeat.X h},
        (slipStokesFEEC F a m).toHeat.Converges v x → ∀ T,
        TendstoUniformlyOn
          (fun h t => infDist ((slipStokesFEEC F a m).toHeat.sol h (v h) t)
            (slipStokesFEEC F a m).toHeat.K) (fun _ => 0) (slipStokesFEEC F a m).toHeat.l
          (Icc 0 T) := by
  have V : (slipStokesFEEC F a m).toHeat.Verdict ((slipStokesFEEC F a m).heatCore hcr) :=
    F.feec.heat a m _ _ hcr
  have hK := (V.isReducing_iff.1 (H.window a m).isReducing_hodgeLaplacian_ker_adjoint.neg).1
  refine ⟨V, hK, fun hx _ hv T => V.residual_tendsto hK hx ?_ hv T⟩
  rw [ConstrainedFEEC.dense_heatCore_data]
  exact Submodule.mem_top

/-- **Crank–Nicolson and the θ-schemes for Maxwell's equations** in the window
`V a → V (a+1) → V (a+2)` with the Gauss laws (`Feec.Instances.Maxwell.feec`): the fully discrete
verdicts (field `full` of the FEEC theorem), exact energy conservation of the Crank–Nicolson
iterates, and for every datum satisfying the Gauss laws and every family of discrete data with
`ιₕ vₕ → x`, the Gauss-law residuals of the Crank–Nicolson iterates on `[0, T]` tend to `0` as
`τₕ → 0`. [QuennevilleBelair2015], Ch. 7; [Thomee2006], Ch. 7 -/
theorem maxwell_fullyDiscrete (a : α) (θ : ℝ) (hθ : 1 / 2 ≤ θ) {τ : κ → ℝ} (hτ : ∀ h, 0 < τ h) :
    ((Maxwell.feec F a).toApprox.crankNicolson τ hτ).Verdict (Maxwell.feec F a).toCore ∧
      ((Maxwell.feec F a).toApprox.thetaScheme θ hθ τ hτ).Verdict (Maxwell.feec F a).toCore ∧
      (∀ h v k, ‖(((Maxwell.feec F a).toApprox.crankNicolson τ hτ).P h ^ k) v‖ = ‖v‖) ∧
      ∀ {x} (_ : x ∈ Maxwell.windowGauss H a) {v : ∀ h, (Maxwell.feec F a).toApprox.X h},
        (Maxwell.feec F a).toApprox.Converges v x → Tendsto τ (Maxwell.feec F a).toApprox.l (𝓝 0) →
        ∀ T {ε : ℝ}, 0 < ε → ∀ᶠ h in (Maxwell.feec F a).toApprox.l, ∀ n : ℕ,
          (n : ℝ) * τ h ∈ Icc 0 T → infDist
            (((Maxwell.feec F a).toApprox.crankNicolson τ hτ).sol h (v h) n)
            (Maxwell.windowGauss H a) < ε := by
  have V := (F.feec.full a 3 _ _).wave ((Maxwell.feec F a).toApprox.crankNicolson τ hτ)
  have hK := (V.isReducing_iff.1 (Maxwell.isReducing_windowGauss H a)).1
  exact ⟨V, (F.feec.full a 3 _ _).wave _, SkewFEEC.norm_crankNicolson_pow_apply _ hτ,
    fun hx _ hv hτ0 T _ hε =>
      V.residual_tendsto_iterates hK hx ((Maxwell.feec F a).mem_toCore_closure _) hv hτ0 T hε⟩

/-- **Crank–Nicolson and the θ-schemes for the Hodge heat equation** on every window with closed
range and finite-dimensional harmonic forms, with every closed constraint: the fully discrete
verdicts (field `full` of the FEEC theorem). [Thomee2006], Ch. 7–9 -/
theorem heat_fullyDiscrete (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i))))
    (hcr : ∀ i, (H.window a m).ClosedRangeAt i)
    [∀ i, FiniteDimensional 𝕜 ((H.window a m).harmonic i)] (θ : ℝ) (hθ : 1 / 2 ≤ θ)
    {τ : κ → ℝ} (hτ : ∀ h, 0 < τ h) :
    ((F.windowFEEC a m K hK).toHeat.crankNicolson τ hτ).Verdict
        ((F.windowFEEC a m K hK).heatCore hcr) ∧
      ((F.windowFEEC a m K hK).toHeat.thetaScheme θ hθ τ hτ).Verdict
        ((F.windowFEEC a m K hK).heatCore hcr) :=
  ⟨(F.feec.full a m K hK).heat hcr _, (F.feec.full a m K hK).heat hcr _⟩

/-- **The mixed method converges for every source**: in a degree `j` with closed range around it
and finite-dimensional harmonic forms, the discrete mixed solutions of every `f ∈ Wʲ` converge to
the mixed solution (field `static` of the FEEC theorem at the solution of `f`). [AFW2010],
Thm 3.9 -/
theorem mixed_converges (hcr : ∀ i, H.ClosedRangeAt i) {i j k : α}
    [FiniteDimensional 𝕜 (H.harmonic j)] (hij : (ComplexShape.up α).Rel i j)
    (hjk : (ComplexShape.up α).Rel j k) (f : V j) :
    Tendsto (fun h => (F.V h).mixedError hij hjk f
      (H.mixedSolution hij hjk (hcr j) (hcr k) f).fst
      (H.mixedSolution hij hjk (hcr j) (hcr k) f).snd.fst
      (H.mixedSolution hij hjk (hcr j) (hcr k) f).snd.snd) F.l (𝓝 0) :=
  (F.feec.static hcr j).converges hij hjk (H.isMixedSolution_mixedSolution _ _ _ _ f)

end Family

/-! ### The cube -/

namespace Cube.FEM

open Feec.Models.Cube.FEM Feec.FiniteElement
open Feec.Domain (L2F formIdx)

variable (n : ℕ) [NeZero n]

/-- **Acoustic waves on the cube** for every admissible sequence `S`: the constrained FEEC verdict
of the pressure–velocity window `HΛ⁰(Q) → HΛ¹(Q)` and of the mixed window
`HΛⁿ⁻¹(Q) → HΛⁿ(Q)`, with natural (`HΛ`) and essential (`H̊Λ`) boundary conditions. -/
theorem acoustic (S : PolySeq) :
    (acousticFEEC (polyFamily n S) 0).Verdict ∧
      (acousticFEEC (polyFamily n S) ((n : ℤ) - 1)).Verdict ∧
      (acousticFEEC (polyFamilyMin n S) 0).Verdict ∧
      (acousticFEEC (polyFamilyMin n S) ((n : ℤ) - 1)).Verdict :=
  ⟨(Corollaries.acoustic (polyFamily n S) 0).1, (Corollaries.acoustic (polyFamily n S) _).1,
    (Corollaries.acoustic (polyFamilyMin n S) 0).1, (Corollaries.acoustic (polyFamilyMin n S) _).1⟩

/-- **Unsteady Stokes flow with slip boundary conditions on the cube** `Q = (0, ½)ⁿ`, `n ≥ 2`, for
every admissible sequence `S`: the conclusions of `slipStokes` for the window
`HΛ⁰(Q) → ⋯ → HΛⁿ(Q)` (`heatWindow`), and a nonzero velocity field `u` in degree `1`, orthogonal
to the gradients of `H¹(Q)` (`div u = 0`, `u · ν = 0`), whose datum `single 1 u` lies in the
constraint `ker 𝐝†` (`exists_single_mem_ker_adjoint_totalD`: `x₀ dx₁` is not closed,
`Feec.Domain.maximalComplex_cycles_one_ne_top`); the discrete heat flows from its projections
`Πₕ (single 1 u)` have constraint residuals tending to `0` uniformly on every `[0, T]`.
[GiraultRaviart1986]; [AFW2010], §3.2 -/
theorem slipStokes (S : PolySeq) (hn : 2 ≤ n) :
    ((slipStokesFEEC (polyFamily n S) 0 (n + 1)).toHeat.Verdict
        ((slipStokesFEEC (polyFamily n S) 0 (n + 1)).heatCore (closedRangeAt_heatWindow n)) ∧
      (slipStokesFEEC (polyFamily n S) 0 (n + 1)).toHeat.Keeps
        (slipStokesFEEC (polyFamily n S) 0 (n + 1)).toHeat.K) ∧
      ∃ u : L2F ℝ (cubeDomain n) (formIdx n 1), u ≠ 0 ∧
        PiLp.single 2 (⟨1, by omega⟩ : Fin (n + 1)) u ∈ ((heatWindow n).totalD†).ker ∧
        ∀ T, TendstoUniformlyOn (fun N t => infDist
          ((slipStokesFEEC (polyFamily n S) 0 (n + 1)).toHeat.sol N
            ((slipStokesFEEC (polyFamily n S) 0 (n + 1)).toHeat.proj N
              (PiLp.single 2 ⟨1, by omega⟩ u)) t)
          (slipStokesFEEC (polyFamily n S) 0 (n + 1)).toHeat.K) (fun _ => 0)
          (slipStokesFEEC (polyFamily n S) 0 (n + 1)).toHeat.l (Icc 0 T) := by
  classical
  obtain ⟨V, hK, hres⟩ := Corollaries.slipStokes (polyFamily n S) 0 (n + 1)
    (closedRangeAt_heatWindow n)
  have hcyc : (heatWindow n).cycles ⟨1, by omega⟩ ≠ ⊤ :=
    ((heatWindow n).cycles_eq (show (ComplexShape.window (n + 1)).Rel ⟨1, by omega⟩ ⟨2, by omega⟩
      from rfl)).symm ▸ ((complex n).cycles_eq (show (ComplexShape.up ℤ).Rel (1 : ℤ) (1 + 1)
        from rfl)) ▸ Feec.Domain.maximalComplex_cycles_one_ne_top (isOpen_cubeDomain n)
          (isBounded_cubeDomain n) ⟨center n, center_mem_cubeDomain n⟩ hn
  obtain ⟨u, hu0, hu⟩ := (heatWindow n).exists_single_mem_ker_adjoint_totalD hcyc
  refine ⟨⟨V, hK⟩, u, hu0, hu, hres hu (DissipFEEC.tendsto_incl_proj _
    ((slipStokesFEEC (polyFamily n S) 0 (n + 1)).heatCore (closedRangeAt_heatWindow n)) ?_)⟩
  rw [ConstrainedFEEC.dense_heatCore_data]
  exact Submodule.mem_top

/-- **Crank–Nicolson for Maxwell's equations on the cube at every polynomial order**
(`Feec.Instances.Maxwell.cubePolyPMC`, `cubePolyPEC`): the conclusions of
`maxwell_fullyDiscrete`. -/
theorem maxwell_crankNicolson (S : PolySeq) (a : ℤ) {τ : ℕ → ℝ} (hτ : ∀ N, 0 < τ N) :
    ((Maxwell.cubePolyPMC n S a).toApprox.crankNicolson τ hτ).Verdict
        (Maxwell.cubePolyPMC n S a).toCore ∧
      ((Maxwell.cubePolyPEC n S a).toApprox.crankNicolson τ hτ).Verdict
        (Maxwell.cubePolyPEC n S a).toCore :=
  ⟨(maxwell_fullyDiscrete (polyFamily n S) a 1 (by norm_num) hτ).1,
    (maxwell_fullyDiscrete (polyFamilyMin n S) a 1 (by norm_num) hτ).1⟩

/-- **Crank–Nicolson and the θ-schemes for the Hodge heat equation on the cube**
(`heatFamily`, every admissible sequence `S`): the fully discrete verdicts, with a nonzero datum
in the core (`crown_heat_nonvacuous`). -/
theorem heat_crankNicolson (S : PolySeq) (θ : ℝ) (hθ : 1 / 2 ≤ θ) {τ : ℕ → ℝ}
    (hτ : ∀ N, 0 < τ N) :
    ((heatFamily n S).toHeat.crankNicolson τ hτ).Verdict
        ((heatFamily n S).heatCore (closedRangeAt_heatWindow n)) ∧
      ((heatFamily n S).toHeat.thetaScheme θ hθ τ hτ).Verdict
        ((heatFamily n S).heatCore (closedRangeAt_heatWindow n)) ∧
      ∃ x ∈ ((heatFamily n S).heatCore (closedRangeAt_heatWindow n)).Data, x ≠ 0 :=
  ⟨(heat_fullyDiscrete (polyFamily n S) 0 (n + 1) ⊤ _ _ θ hθ hτ).1,
    (heat_fullyDiscrete (polyFamily n S) 0 (n + 1) ⊤ _ _ θ hθ hτ).2,
    (crown_heat_nonvacuous n S).2⟩

/-- **Magnetostatics on the cube** `(0, ½)³` for every admissible sequence `S`: the static FEEC
verdict of `HΛ` and `H̊Λ` in degrees `1` and `2`, the mixed formulations of
`curl curl u - grad div u = f` with natural and essential boundary conditions. [AFW2010],
Thms 3.4–3.9; [Monk2003] -/
theorem magnetostatic (S : PolySeq) :
    (polyFamily 3 S).StaticVerdict 1 ∧ (polyFamily 3 S).StaticVerdict 2 ∧
      (polyFamilyMin 3 S).StaticVerdict 1 ∧ (polyFamilyMin 3 S).StaticVerdict 2 :=
  ⟨(polyFamily 3 S).feec.static closedRangeAt 1, (polyFamily 3 S).feec.static closedRangeAt 2,
    (polyFamilyMin 3 S).feec.static closedRangeAt_min 1,
    (polyFamilyMin 3 S).feec.static closedRangeAt_min 2⟩

end Cube.FEM

/-! ### Parallelepipeds -/

namespace Parallelepiped

open Feec.Models.Parallelepiped Feec.FiniteElement

variable {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ)

/-- **Acoustic waves on a parallelepiped** `Ω = A · Q + b`: the constrained FEEC verdicts of the
windows in degrees `0, 1` and `n - 1, n`, natural and essential boundary conditions. -/
theorem acoustic (S : PolySeq) :
    (acousticFEEC (polyFamily A hA b S) 0).Verdict ∧
      (acousticFEEC (polyFamily A hA b S) ((n : ℤ) - 1)).Verdict ∧
      (acousticFEEC (polyFamilyMin A hA b S) 0).Verdict ∧
      (acousticFEEC (polyFamilyMin A hA b S) ((n : ℤ) - 1)).Verdict :=
  ⟨(Corollaries.acoustic (polyFamily A hA b S) 0).1,
    (Corollaries.acoustic (polyFamily A hA b S) _).1,
    (Corollaries.acoustic (polyFamilyMin A hA b S) 0).1,
    (Corollaries.acoustic (polyFamilyMin A hA b S) _).1⟩

/-- **Magnetostatics on a parallelepiped** in dimension `3`: the static FEEC verdict of `HΛ(Ω)` and
`H̊Λ(Ω)` in degrees `1` and `2`. -/
theorem magnetostatic (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : IsUnit A.det) (b : Fin 3 → ℝ)
    (S : PolySeq) :
    (polyFamily A hA b S).StaticVerdict 1 ∧ (polyFamily A hA b S).StaticVerdict 2 ∧
      (polyFamilyMin A hA b S).StaticVerdict 1 ∧ (polyFamilyMin A hA b S).StaticVerdict 2 :=
  haveI := finiteDimensional_harmonic A hA b 1
  haveI := finiteDimensional_harmonic A hA b 2
  haveI := finiteDimensional_harmonic_min A hA b 1
  haveI := finiteDimensional_harmonic_min A hA b 2
  ⟨(polyFamily A hA b S).feec.static (closedRangeAt A hA b) 1,
    (polyFamily A hA b S).feec.static (closedRangeAt A hA b) 2,
    (polyFamilyMin A hA b S).feec.static (closedRangeAt_min A hA b) 1,
    (polyFamilyMin A hA b S).feec.static (closedRangeAt_min A hA b) 2⟩

end Parallelepiped

/-! ### Domains star-shaped with respect to a ball -/

namespace StarShaped.MeshFamily

open Feec.Models.StarShaped Feec.FiniteElement

variable {n : ℕ} [NeZero n] {D : StarDomain n} (M : MeshFamily D)

/-- **Acoustic waves on a star-shaped domain**, for every shape-regular quasi-uniform mesh family
and every admissible sequence `S`: the constrained FEEC verdicts of the windows in degrees `0, 1`
and `n - 1, n`, natural (`HΛ(Ω)`) and essential (`H̊Λ(Ω)`) boundary conditions. -/
theorem acoustic (S : PolySeq) :
    (acousticFEEC (M.polyFamily S) 0).Verdict ∧
      (acousticFEEC (M.polyFamily S) ((n : ℤ) - 1)).Verdict ∧
      (acousticFEEC (M.polyFamilyMin S) 0).Verdict ∧
      (acousticFEEC (M.polyFamilyMin S) ((n : ℤ) - 1)).Verdict :=
  ⟨(Corollaries.acoustic (M.polyFamily S) 0).1, (Corollaries.acoustic (M.polyFamily S) _).1,
    (Corollaries.acoustic (M.polyFamilyMin S) 0).1, (Corollaries.acoustic (M.polyFamilyMin S) _).1⟩

end StarShaped.MeshFamily

end Feec.Instances.Corollaries
