module

public import Feec.HilbertComplex.Approximation.Crown
public import Feec.HilbertComplex.Reducing
public import Feec.Instances.Maxwell
public import Feec.Models.Cube.HeatFEM
public import Feec.Models.Cube.SobolevRateHigh

/-!
# Corollaries of the FEEC theorem: acoustics, slip Stokes, time stepping, rates, magnetostatics

Corollaries of the FEEC theorem for every conforming family of a Hilbert complex, and their
instances on the cube, on parallelepipeds and on domains star-shaped with respect to a ball.

## Main results

* `acoustic`, `slipStokes`: acoustic waves and unsteady Stokes flow with slip conditions.
* `maxwell_fullyDiscrete`, `heat_fullyDiscrete`: Crank–Nicolson and the θ-schemes.
* `Cube.FEM.feec_sobolev`: the rates `h^{min(s, p + 1)}` for `Hˢ(Q)` data.

## References

* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010]
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques, and applications*][AFW2006]
* [D. N. Arnold, A. Logg, *Periodic table of the finite elements*][ArnoldLogg2014]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]
* [P. Joly, *Variational Methods for Time-Dependent Wave Propagation Problems*][Joly2003]
* [V. Girault, P.-A. Raviart, *Finite Element Methods for Navier–Stokes Equations*][GiraultRaviart1986]
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018]
* [P. Monk, *Finite Element Methods for Maxwell's Equations*][Monk2003]
* [V. Thomée, *Galerkin Finite Element Methods for Parabolic Problems*][Thomee2006]

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

/-- The acoustic discretization: the window `Vₕᵃ → Vₕ^{a+1}` of `F` with no constraint. -/
abbrev acousticFEEC (a : α) : ConstrainedFEEC (H.window a 2) κ :=
  F.windowFEEC a 2 ⊤ isClosed_univ

/-- **Acoustic waves**: the FEEC verdicts of the Hodge wave equation of the window `Vᵃ → V^{a+1}`.
[QuennevilleBelair2015], Thms 4.6, 4.7, 4.14; [Joly2003] -/
theorem acoustic (a : α) :
    (acousticFEEC F a).Verdict ∧ (acousticFEEC F a).toApprox.Verdict (acousticFEEC F a).toCore :=
  ⟨F.feec.constrained a 2 _ _, F.feec.wave a 2 _ _⟩

/-- The slip Stokes discretization: the window `Vₕᵃ → ⋯ → Vₕ^{a+m-1}` with constraint `ker 𝐝†`. -/
abbrev slipStokesFEEC (a : α) (m : ℕ) : ConstrainedFEEC (H.window a m) κ :=
  F.windowFEEC a m ((H.window a m).totalD†).ker
    (isClosed_ker (adjoint_isClosed (H.window a m).dense_totalD_domain))

/-- **Unsteady Stokes flow with slip boundary conditions**: on a window with closed ranges, the heat
verdict on `ker 𝐝†`, which the flow keeps, with residuals tending to `0`.
[GiraultRaviart1986], Ch. I; [Arnold2018], Ch. 4 -/
theorem slipStokes (a : α) (m : ℕ) (hcr : ∀ i, (H.window a m).ClosedRangeAt i) :
    (slipStokesFEEC F a m).toHeat.Verdict ((slipStokesFEEC F a m).heatCore hcr (F.isGraphBounded_windowFEEC a m _ _)) ∧
      (slipStokesFEEC F a m).toHeat.Keeps (slipStokesFEEC F a m).toHeat.K ∧
      ∀ {x} (_ : x ∈ ((H.window a m).totalD†).ker) {v : ∀ h, (slipStokesFEEC F a m).toHeat.X h},
        (slipStokesFEEC F a m).toHeat.Converges v x → ∀ T,
        TendstoUniformlyOn
          (fun h t => infDist ((slipStokesFEEC F a m).toHeat.sol h (v h) t)
            (slipStokesFEEC F a m).toHeat.K) (fun _ => 0) (slipStokesFEEC F a m).toHeat.l
          (Icc 0 T) := by
  have V : (slipStokesFEEC F a m).toHeat.Verdict ((slipStokesFEEC F a m).heatCore hcr (F.isGraphBounded_windowFEEC a m _ _)) :=
    F.feec.heat a m _ _ hcr
  have hK := (V.isReducing_iff.1 (H.window a m).isReducing_hodgeLaplacian_ker_adjoint.neg).1
  refine ⟨V, hK, fun hx _ hv T => V.residual_tendsto hK hx ?_ hv T⟩
  rw [ConstrainedFEEC.dense_heatCore_data]
  exact Submodule.mem_top

/-- **Crank–Nicolson and the θ-schemes (`θ ≥ 1/2`) for Maxwell's equations**: the fully discrete
verdicts, and for Crank–Nicolson exact energy conservation and Gauss-law residuals tending to `0`
as `h, τ → 0`. [QuennevilleBelair2015], Ch. 7 -/
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

/-- **Crank–Nicolson and the θ-schemes (`θ ≥ 1/2`) for the Hodge heat equation**: the fully
discrete verdicts on every window with closed ranges. [Thomee2006], Ch. 7–9 -/
theorem heat_fullyDiscrete (a : α) (m : ℕ) (K : Submodule 𝕜 (PiLp 2 fun i : Fin m => V (a + i)))
    (hK : IsClosed (K : Set (PiLp 2 fun i : Fin m => V (a + i))))
    (hcr : ∀ i, (H.window a m).ClosedRangeAt i) (θ : ℝ) (hθ : 1 / 2 ≤ θ)
    {τ : κ → ℝ} (hτ : ∀ h, 0 < τ h) :
    ((F.windowFEEC a m K hK).toHeat.crankNicolson τ hτ).Verdict
        ((F.windowFEEC a m K hK).heatCore hcr (F.isGraphBounded_windowFEEC a m K hK)) ∧
      ((F.windowFEEC a m K hK).toHeat.thetaScheme θ hθ τ hτ).Verdict
        ((F.windowFEEC a m K hK).heatCore hcr (F.isGraphBounded_windowFEEC a m K hK)) :=
  ⟨(F.feec.full a m K hK).heat hcr (F.isGraphBounded_windowFEEC a m K hK) _,
    (F.feec.full a m K hK).heat hcr (F.isGraphBounded_windowFEEC a m K hK) _⟩

/-- **The mixed method converges for every source**, with closed ranges and finite-dimensional
harmonic forms. [AFW2010], Thm 3.9 -/
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

/-- **Acoustic waves on the cube**: the constrained FEEC verdicts of the windows in degrees `0, 1`
and `n - 1, n`, with natural and essential boundary conditions. -/
theorem acoustic (S : PolySeq) :
    (acousticFEEC (polyFamily n S) 0).Verdict ∧
      (acousticFEEC (polyFamily n S) ((n : ℤ) - 1)).Verdict ∧
      (acousticFEEC (polyFamilyMin n S) 0).Verdict ∧
      (acousticFEEC (polyFamilyMin n S) ((n : ℤ) - 1)).Verdict :=
  ⟨(Corollaries.acoustic (polyFamily n S) 0).1, (Corollaries.acoustic (polyFamily n S) _).1,
    (Corollaries.acoustic (polyFamilyMin n S) 0).1, (Corollaries.acoustic (polyFamilyMin n S) _).1⟩

/-- **Slip Stokes flow on the cube**, `n ≥ 2`: the heat verdict, and a nonzero datum
`single 1 u ∈ ker 𝐝†` with residuals tending to `0`. [GiraultRaviart1986], Ch. I -/
theorem slipStokes (S : PolySeq) (hn : 2 ≤ n) :
    ((slipStokesFEEC (polyFamily n S) 0 (n + 1)).toHeat.Verdict
        ((slipStokesFEEC (polyFamily n S) 0 (n + 1)).heatCore (closedRangeAt_heatWindow n)
          ((polyFamily n S).isGraphBounded_windowFEEC 0 (n + 1) _ _)) ∧
      (slipStokesFEEC (polyFamily n S) 0 (n + 1)).toHeat.Keeps
        (slipStokesFEEC (polyFamily n S) 0 (n + 1)).toHeat.K) ∧
      ∃ u : L2F ℝ (cubeDomain n) (formIdx n 1), u ≠ 0 ∧
        u ∈ ((heatWindow n).cycles ⟨1, by omega⟩)ᗮ ⊓ ((heatWindow n).d _ ⟨2, by omega⟩).domain ∧
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
  obtain ⟨u, hu, hu0⟩ := (heatWindow n).exists_mem_orthogonal_cycles_inf_domain
    (show (ComplexShape.window (n + 1)).Rel ⟨1, by omega⟩ ⟨2, by omega⟩ from rfl) hcyc
  have hK0 := (heatWindow n).single_mem_ker_adjoint_totalD_of_mem_orthogonal
    (Submodule.orthogonal_le ((heatWindow n).boundaries_le_cycles _) hu.1)
  refine ⟨⟨V, hK⟩, u, hu0, hu, hK0, hres hK0 (DissipFEEC.tendsto_incl_proj _
    ((slipStokesFEEC (polyFamily n S) 0 (n + 1)).heatCore (closedRangeAt_heatWindow n)
          ((polyFamily n S).isGraphBounded_windowFEEC 0 (n + 1) _ _)) ?_)⟩
  rw [ConstrainedFEEC.dense_heatCore_data]
  exact Submodule.mem_top

/-- **Crank–Nicolson for Maxwell's equations on the cube at every polynomial order.** -/
theorem maxwell_crankNicolson (S : PolySeq) (a : ℤ) {τ : ℕ → ℝ} (hτ : ∀ N, 0 < τ N) :
    ((Maxwell.cubePolyPMC n S a).toApprox.crankNicolson τ hτ).Verdict
        (Maxwell.cubePolyPMC n S a).toCore ∧
      ((Maxwell.cubePolyPEC n S a).toApprox.crankNicolson τ hτ).Verdict
        (Maxwell.cubePolyPEC n S a).toCore :=
  ⟨(maxwell_fullyDiscrete (polyFamily n S) a 1 (by norm_num) hτ).1,
    (maxwell_fullyDiscrete (polyFamilyMin n S) a 1 (by norm_num) hτ).1⟩

/-- **Crank–Nicolson and the θ-schemes (`θ ≥ 1/2`) for the Hodge heat equation on the cube**,
with a nonzero datum in the core. -/
theorem heat_crankNicolson (S : PolySeq) (θ : ℝ) (hθ : 1 / 2 ≤ θ) {τ : ℕ → ℝ}
    (hτ : ∀ N, 0 < τ N) :
    ((heatFamily n S).toHeat.crankNicolson τ hτ).Verdict
        ((heatFamily n S).heatCore (closedRangeAt_heatWindow n) (isGraphBounded_heatFamily n S)) ∧
      ((heatFamily n S).toHeat.thetaScheme θ hθ τ hτ).Verdict
        ((heatFamily n S).heatCore (closedRangeAt_heatWindow n) (isGraphBounded_heatFamily n S)) ∧
      ∃ x ∈ ((heatFamily n S).heatCore (closedRangeAt_heatWindow n) (isGraphBounded_heatFamily n S)).Data, x ≠ 0 :=
  ⟨(heat_fullyDiscrete (polyFamily n S) 0 (n + 1) ⊤ _ _ θ hθ hτ).1,
    (heat_fullyDiscrete (polyFamily n S) 0 (n + 1) ⊤ _ _ θ hθ hτ).2,
    (crown_heat_nonvacuous n S).2⟩

/-- **Magnetostatics on the cube** `(0, ½)³`: the static FEEC verdicts of `HΛ` and `H̊Λ` in degrees
`1` and `2`. [AFW2010], Thms 3.4–3.9; [Monk2003] -/
theorem magnetostatic (S : PolySeq) :
    (polyFamily 3 S).StaticVerdict 1 ∧ (polyFamily 3 S).StaticVerdict 2 ∧
      (polyFamilyMin 3 S).StaticVerdict 1 ∧ (polyFamilyMin 3 S).StaticVerdict 2 :=
  ⟨(polyFamily 3 S).feec.static closedRangeAt 1, (polyFamily 3 S).feec.static closedRangeAt 2,
    (polyFamilyMin 3 S).feec.static closedRangeAt_min 1,
    (polyFamilyMin 3 S).feec.static closedRangeAt_min 2⟩

/-- **The FEEC theorem for `Hˢ(Q)` data on the cube**: rates `h^{min(s, p + 1)}` where `S`
reproduces `P_p`. [AFW2010], Thm 3.9; [QuennevilleBelair2015], Thm 4.14; [Arnold2018], Ch. 7 -/
theorem feec_sobolev (S : PolySeq) (p : ℕ) :
    ConformingFamily.Verdict.Rated (polyFamily n S) (sobolevHighJackson n S p) :=
  (polyFamily n S).feec_rated _

/-- **The FEEC theorem on affinely invariant shape spaces**, for every admissible sequence on the
cube. [AFW2006], Thm 3.5 -/
theorem feec_affineInvariant (S : PolySeq) :
    (polyFamily n S).Verdict ∧ ∀ k, 1 ≤ k →
      S.space n k = (S.form ℝ k).map (evalForm n) ∧ IsAffineInvariant (S.form ℝ (n := n) k) :=
  ⟨(polyFamily n S).feec, fun k hk => ⟨S.space_eq_map_form k, S.isAffineInvariant_form hk⟩⟩

/-- **The FEEC theorem on the polynomial complexes of the periodic table**, with their exactness
and dimension counts. [AFW2006], §3, Thms 4.9, 4.13; [ArnoldLogg2014] -/
theorem feec_polyComplex (K : Type*) [Field K] [CharZero K] (S : PolySeq) :
    (polyFamily n S).Verdict ∧ (∀ k, S.space n k = (S.form ℝ k).map (evalForm n)) ∧
      (∀ k, ∀ ω ∈ S.form K (n := n) k, Koszul.extDeriv ω ∈ S.form K (k + 1)) ∧
      (∀ k, ∀ ω ∈ S.form K (n := n) (k + 1), Koszul.extDeriv ω = 0 →
        ∃ η ∈ S.form K k, Koszul.extDeriv η = ω) ∧
      (∀ ω ∈ S.form K (n := n) 0, Koszul.extDeriv ω = 0 → ω ∈ Koszul.polyForm K (Fin n) 0 0) ∧
      (∀ k, Module.finrank K (S.form K (n := n) k) =
        ∑ m ∈ Finset.range (n + 1), (n + 1).choose (m + 1) * Module.finrank K (S.testForm K k m)) ∧
      ∀ k, Module.finrank ℝ (S.space n k) =
        ∑ m ∈ Finset.range (n + 1), (n + 1).choose (m + 1) * Module.finrank ℝ (S.test k m) :=
  ⟨(polyFamily n S).feec, S.space_eq_map_form, fun _ _ => S.extDeriv_mem_form,
    fun _ _ => S.exists_extDeriv_eq, fun _ => S.mem_polyForm_zero_of_extDeriv_eq_zero,
    S.finrank_form_eq_sum, fun k => (S.kind k).finrank_space_eq_sum (S.one_le_deg k) k⟩

end Cube.FEM

/-! ### Parallelepipeds -/

namespace Parallelepiped

open Feec.Models.Parallelepiped Feec.FiniteElement

variable {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ)

/-- **Acoustic waves on a parallelepiped** `Ω = A · Q + b`, with natural and essential boundary
conditions. -/
theorem acoustic (S : PolySeq) :
    (acousticFEEC (polyFamily A hA b S) 0).Verdict ∧
      (acousticFEEC (polyFamily A hA b S) ((n : ℤ) - 1)).Verdict ∧
      (acousticFEEC (polyFamilyMin A hA b S) 0).Verdict ∧
      (acousticFEEC (polyFamilyMin A hA b S) ((n : ℤ) - 1)).Verdict :=
  ⟨(Corollaries.acoustic (polyFamily A hA b S) 0).1,
    (Corollaries.acoustic (polyFamily A hA b S) _).1,
    (Corollaries.acoustic (polyFamilyMin A hA b S) 0).1,
    (Corollaries.acoustic (polyFamilyMin A hA b S) _).1⟩

/-- **Magnetostatics on a parallelepiped** in dimension `3`. -/
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

/-- **Acoustic waves on a star-shaped domain**, for every mesh family and admissible sequence. -/
theorem acoustic (S : PolySeq) :
    (acousticFEEC (M.polyFamily S) 0).Verdict ∧
      (acousticFEEC (M.polyFamily S) ((n : ℤ) - 1)).Verdict ∧
      (acousticFEEC (M.polyFamilyMin S) 0).Verdict ∧
      (acousticFEEC (M.polyFamilyMin S) ((n : ℤ) - 1)).Verdict :=
  ⟨(Corollaries.acoustic (M.polyFamily S) 0).1, (Corollaries.acoustic (M.polyFamily S) _).1,
    (Corollaries.acoustic (M.polyFamilyMin S) 0).1, (Corollaries.acoustic (M.polyFamilyMin S) _).1⟩

end StarShaped.MeshFamily

end Feec.Instances.Corollaries
