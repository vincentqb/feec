module

public import Feec.Evolution.BoundaryLifting
public import Feec.Models.BoundedDomain.GradCurl
public import Feec.HilbertComplex.InvariantCore
public import Feec.HilbertComplex.ReducedSystem
public import Feec.Models.Cube.Basic

/-!
# The thesis' experiments with inhomogeneous boundary data

The Crank–Nicolson runs of [QuennevilleBelair2015], Ch. 7, as implemented in `fem4gr`
(<https://github.com/vincentqb/fem4gr>, `ebsystem3d_mixed_crank_triplet.py`), solve the
Einstein–Bianchi system (4.14) `σ' = div E`, `E' = grad σ − curl B`, `B' = curl E` on the unit
cube with **inhomogeneous** essential boundary data taken from the exact plane wave: `σ = 0`,
`E × n = E_ex × n`, `B · n = B_ex · n` on `∂Ω`. The homogeneous problem is the Hodge wave
equation of the thesis' complex `H̊¹ → H̊(curl) → L²` (`Feec.Models.BoundedDomain.gradCurl`).

## Hodge wave equations with boundary data

For a finite Hilbert complex `H` (the boundary conditions, e.g. the minimal realization) and a
complex `H'` with `d ≤ d'` (no boundary conditions, e.g. the maximal realization), the operator
without boundary conditions is `L_max = 𝐝' − 𝐝†` (`waveMax H H'`), and `L = 𝐝 − 𝐝† ≤ L_max`
(`wave_le_waveMax`). The boundary values are prescribed by a lifting through
`Feec.Evolution.IsBoundarySolution L_max L`: the essential conditions are those of `𝐝`, while
`𝐝†` carries none. For the thesis' complex, `L_max (σ, E, B) = (div E, grad σ − curl B, curl E)`
on `H¹ × (H(curl) ∩ H(div)) × H(curl)`, and `U(t) − G(t) ∈ D(L)` says that `σ` and the tangential
trace `E × n` agree with those of `G`. The condition `B · n = h` of `fem4gr` is not an extra
condition of the continuous problem: `B` lies in the last space `L²`.

## Restrictions of whole-space solutions

A **whole-space TSD solution** (`WholeSpaceTSD`) is a classical solution of `E' = −curl B`,
`B' = curl E` on `ℝ × ℝ³`, `C¹` in space with jointly continuous time derivatives, whose fields are
symmetric, trace-free and divergence-free at every point (so `σ = 0`); the plane wave of Ch. 7 is
one (`Feec.Numerics.PlaneWaveCube`). On every bounded open `Ω`:

* its restriction `R(t) = (0, E(t)|_Ω, B(t)|_Ω)` is a strong solution of `U' = L_max U` with values
  in `K = {0} × L²(TSD) × L²(TSD)` (`WholeSpaceTSD.isStrongSolution_restrict`,
  `WholeSpaceTSD.restrict_mem`);
* **it is the unique solution with its own boundary data and initial value**
  (`WholeSpaceTSD.restrict_unique`), so TSD propagates for this datum;
* for an initial value `U₀` with `U₀ − R(0) ∈ D(L)`, the solution with the boundary data of `R`
  exists, is unique (`WholeSpaceTSD.existsUnique`), and equals `R(t) + e^{tL}(U₀ − R(0))`
  (`WholeSpaceTSD.eq_add_waveGroup`); it stays TSD on `[0, T]` **iff** the homogeneous solution
  from `U₀ − R(0)` does (`WholeSpaceTSD.mem_iff`), in particular whenever `U₀ − R(0)` lies in
  the invariant core `K*` of the homogeneous problem (`WholeSpaceTSD.mem_of_mem_coreSub`).

The homogeneous refutation (`Feec.Counterexamples.BoundedDomainTSD.tsd_not_propagates`) then
transfers to these data: TSD propagation fails for `U₀ = R(0) + (0, 0, β)`
(`Feec.Numerics.PlaneWaveCube.not_propagates_perturbed`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Ch. 7, §4.10 (Prop 4.17, (4.14))
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 8
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ContDiff LinearPMap
open MeasureTheory Set Filter Topology Feec.Domain Feec.Models.BoundedDomain

universe u

namespace Feec.Models.Cube.Inhomogeneous

/-! ## Monotonicity of total differentials and the wave operator without boundary conditions -/

section WaveMax

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
  [Fintype ι]

/-- `f ≤ f'` gives `f − g ≤ f' − g`. -/
theorem sub_le_sub_right {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {f f' g : E →ₗ.[𝕜] F} (h : f ≤ f') :
    f - g ≤ f' - g := by
  refine ⟨inf_le_inf_right _ h.1, fun x y hxy => ?_⟩
  rw [LinearPMap.sub_apply, LinearPMap.sub_apply]
  congr 1
  · exact h.2 hxy
  · congr 1; exact Subtype.ext hxy

/-- The total differential is monotone in the differentials. -/
theorem totalD_mono {H H' : HilbertComplex 𝕜 c W} (h : ∀ i j, H.d i j ≤ H'.d i j) :
    H.totalD ≤ H'.totalD := by
  refine ⟨fun x hx i j => (h i j).1 (hx i j), fun x y hxy => ?_⟩
  refine PiLp.ext fun j => ?_
  rw [HilbertComplex.totalD_apply, HilbertComplex.totalD_apply]
  refine Finset.sum_congr rfl fun i _ => (h i j).2 ?_
  change (x : PiLp 2 W) i = (y : PiLp 2 W) i
  rw [hxy]

/-- **The wave operator without boundary conditions** `L_max = 𝐝' − 𝐝†` of a pair of complexes
`H ≤ H'` (`H` carries the boundary conditions, `H'` none): the operator of the Hodge wave
equation with inhomogeneous essential boundary data. -/
def waveMax (H H' : HilbertComplex 𝕜 c W) : PiLp 2 W →ₗ.[𝕜] PiLp 2 W :=
  H'.totalD - H.dual.totalD

/-- `L = 𝐝 − 𝐝† ≤ L_max = 𝐝' − 𝐝†`. -/
theorem wave_le_waveMax {H H' : HilbertComplex 𝕜 c W} (h : ∀ i j, H.d i j ≤ H'.d i j) :
    H.wave ≤ waveMax H H' :=
  sub_le_sub_right (totalD_mono h)

theorem mem_waveMax_domain {H H' : HilbertComplex 𝕜 c W} {x : PiLp 2 W} :
    x ∈ (waveMax H H').domain ↔
      (∀ i j, x i ∈ (H'.d i j).domain) ∧ ∀ i j, x j ∈ ((H.d i j)†).domain :=
  ⟨fun h => ⟨h.1, fun i j => h.2 j i⟩, fun h => ⟨h.1, fun j i => h.2 i j⟩⟩

/-- `(L_max x) j = ∑ i, d' i j (x i) − ∑ k, (d j k)† (x k)`. -/
theorem waveMax_apply {H H' : HilbertComplex 𝕜 c W} (x : (waveMax H H').domain) (j : ι) :
    (waveMax H H' x) j = ∑ i, H'.d i j ⟨(x : PiLp 2 W) i, x.2.1 i j⟩ -
      ∑ k, (H.d j k)† ⟨(x : PiLp 2 W) k, x.2.2 k j⟩ :=
  congrArg₂ (fun a b => a - b) (H'.totalD_apply ⟨x, x.2.1⟩ j) (H.dual.totalD_apply ⟨x, x.2.2⟩ j)

end WaveMax

/-! ## Short complexes -/

section Short

open ShortHilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {W₀ W₁ W₂ : Type u}
  [NormedAddCommGroup W₀] [InnerProductSpace 𝕜 W₀] [CompleteSpace W₀]
  [NormedAddCommGroup W₁] [InnerProductSpace 𝕜 W₁] [CompleteSpace W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace 𝕜 W₂] [CompleteSpace W₂]
  (S S' : ShortHilbertComplex 𝕜 W₀ W₁ W₂)

/-- `L_max = 𝐝' − 𝐝†` for short complexes `S ≤ S'`: `(x₀, x₁, x₂) ↦ (−d₀† x₁, d₀' x₀ − d₁† x₂,
d₁' x₁)` on `D(d₀') × (D(d₁') ∩ D(d₀†)) × D(d₁†)`. -/
abbrev shortWaveMax : PiLp 2 (W3 W₀ W₁ W₂) →ₗ.[𝕜] PiLp 2 (W3 W₀ W₁ W₂) :=
  waveMax S.toHilbertComplex S'.toHilbertComplex

variable {S S'}

theorem d_le_of_le (h₀ : S.d₀ ≤ S'.d₀) (h₁ : S.d₁ ≤ S'.d₁) (i j : Fin 3) :
    S.toHilbertComplex.d i j ≤ S'.toHilbertComplex.d i j := by
  fin_cases i <;> fin_cases j <;> first | exact h₀ | exact h₁ | exact le_rfl

theorem wave_le_shortWaveMax (h₀ : S.d₀ ≤ S'.d₀) (h₁ : S.d₁ ≤ S'.d₁) :
    S.wave ≤ shortWaveMax S S' :=
  wave_le_waveMax (d_le_of_le h₀ h₁)

theorem mem_shortWaveMax_domain {x : PiLp 2 (W3 W₀ W₁ W₂)} : x ∈ (shortWaveMax S S').domain ↔
    (x 0 : W₀) ∈ S'.d₀.domain ∧ (x 1 : W₁) ∈ S'.d₁.domain ∧ (x 1 : W₁) ∈ S.d₀†.domain ∧
      (x 2 : W₂) ∈ S.d₁†.domain := by
  rw [mem_waveMax_domain]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1 0 1, h1 1 2, h2 0 1, h2 1 2⟩
  · rintro ⟨h0, h1, h1', h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · fin_cases i <;> fin_cases j <;> first | exact h0 | exact h1 | exact Submodule.mem_top
    · fin_cases i <;> fin_cases j <;>
        first | exact h1' | exact h2 |
          exact (show ((0 : W3 W₀ W₁ W₂ _ →ₗ.[𝕜] W3 W₀ W₁ W₂ _)†).domain = ⊤ by
            rw [LinearPMap.adjoint_zero]; rfl) ▸ Submodule.mem_top

/-- `(L_max x)₀ = −d₀† x₁`. -/
theorem shortWaveMax_apply_zero (x : (shortWaveMax S S').domain) :
    ((shortWaveMax S S' x : PiLp 2 (W3 W₀ W₁ W₂)) 0 : W₀) =
      -(S.d₀† ⟨(x : PiLp 2 (W3 W₀ W₁ W₂)) 1, x.2.2 1 0⟩) := by
  rw [waveMax_apply, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [LinearPMap.apply_eq_zero_of_eq_zero (show S'.toHilbertComplex.d 0 0 = 0 from rfl),
    LinearPMap.apply_eq_zero_of_eq_zero (show S'.toHilbertComplex.d 1 0 = 0 from rfl),
    LinearPMap.apply_eq_zero_of_eq_zero (show S'.toHilbertComplex.d 2 0 = 0 from rfl),
    LinearPMap.adjoint_apply_eq_zero_of_eq_zero (show S.toHilbertComplex.d 0 0 = 0 from rfl),
    LinearPMap.adjoint_apply_eq_zero_of_eq_zero (show S.toHilbertComplex.d 0 2 = 0 from rfl)]
  simp
  rfl

/-- `(L_max x)₁ = d₀' x₀ − d₁† x₂`. -/
theorem shortWaveMax_apply_one (x : (shortWaveMax S S').domain) :
    ((shortWaveMax S S' x : PiLp 2 (W3 W₀ W₁ W₂)) 1 : W₁) =
      S'.d₀ ⟨(x : PiLp 2 (W3 W₀ W₁ W₂)) 0, x.2.1 0 1⟩ -
        S.d₁† ⟨(x : PiLp 2 (W3 W₀ W₁ W₂)) 2, x.2.2 2 1⟩ := by
  rw [waveMax_apply, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [LinearPMap.apply_eq_zero_of_eq_zero (show S'.toHilbertComplex.d 1 1 = 0 from rfl),
    LinearPMap.apply_eq_zero_of_eq_zero (show S'.toHilbertComplex.d 2 1 = 0 from rfl),
    LinearPMap.adjoint_apply_eq_zero_of_eq_zero (show S.toHilbertComplex.d 1 0 = 0 from rfl),
    LinearPMap.adjoint_apply_eq_zero_of_eq_zero (show S.toHilbertComplex.d 1 1 = 0 from rfl)]
  simp
  rfl

/-- `(L_max x)₂ = d₁' x₁`. -/
theorem shortWaveMax_apply_two (x : (shortWaveMax S S').domain) :
    ((shortWaveMax S S' x : PiLp 2 (W3 W₀ W₁ W₂)) 2 : W₂) =
      S'.d₁ ⟨(x : PiLp 2 (W3 W₀ W₁ W₂)) 1, x.2.1 1 2⟩ := by
  rw [waveMax_apply, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [LinearPMap.apply_eq_zero_of_eq_zero (show S'.toHilbertComplex.d 0 2 = 0 from rfl),
    LinearPMap.apply_eq_zero_of_eq_zero (show S'.toHilbertComplex.d 2 2 = 0 from rfl),
    LinearPMap.adjoint_apply_eq_zero_of_eq_zero (show S.toHilbertComplex.d 2 0 = 0 from rfl),
    LinearPMap.adjoint_apply_eq_zero_of_eq_zero (show S.toHilbertComplex.d 2 1 = 0 from rfl),
    LinearPMap.adjoint_apply_eq_zero_of_eq_zero (show S.toHilbertComplex.d 2 2 = 0 from rfl)]
  simp
  rfl

/-- A point of the graph of `L_max` from its components. -/
theorem mk3_mem_graph_shortWaveMax {x₀ : W₀} {x₁ : W₁} {x₂ : W₂} {y₀ : W₀} {y₁ : W₁} {y₂ : W₂}
    (h0 : x₀ ∈ S'.d₀.domain) (h1 : x₁ ∈ S'.d₁.domain) (h1' : x₁ ∈ S.d₀†.domain)
    (h2 : x₂ ∈ S.d₁†.domain) (e0 : y₀ = -S.d₀† ⟨x₁, h1'⟩)
    (e1 : y₁ = S'.d₀ ⟨x₀, h0⟩ - S.d₁† ⟨x₂, h2⟩) (e2 : y₂ = S'.d₁ ⟨x₁, h1⟩) :
    (mk3 x₀ x₁ x₂, mk3 y₀ y₁ y₂) ∈ (shortWaveMax S S').graph := by
  have hx : mk3 x₀ x₁ x₂ ∈ (shortWaveMax S S').domain :=
    mem_shortWaveMax_domain.2 ⟨h0, h1, h1', h2⟩
  refine (LinearPMap.mem_graph_iff _).2 ⟨⟨_, hx⟩, rfl, ?_⟩
  refine PiLp.ext fun i => ?_
  fin_cases i
  · exact (shortWaveMax_apply_zero ⟨_, hx⟩).trans e0.symm
  · exact (shortWaveMax_apply_one ⟨_, hx⟩).trans e1.symm
  · exact (shortWaveMax_apply_two ⟨_, hx⟩).trans e2.symm

end Short


/-! ## Time derivatives in `L²(Ω)` of classical fields -/

section TimeDerivative

variable {Ω : Set R3}

/-- Scalar multiples of continuous fields. -/
theorem smoothField_smul (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {ι : Type*} (c : ℝ)
    {Ψ : ι → R3 → ℝ} (hΨ : ∀ i, Continuous (Ψ i)) :
    c • smoothField hΩ hb Ψ hΨ =
      smoothField hΩ hb (fun i x => c * Ψ i x) (fun i => continuous_const.mul (hΨ i)) := by
  refine (WithLp.ext_iff 2).2 (funext fun i => Lp.ext ?_)
  filter_upwards [Lp.coeFn_smul c (smoothField hΩ hb Ψ hΨ i), coeFn_smoothField hΩ hb Ψ hΨ i,
    coeFn_smoothField hΩ hb (fun i x => c * Ψ i x) (fun i => continuous_const.mul (hΨ i)) i]
    with x h1 h2 h3
  simp only [PiLp.smul_apply] at h1 ⊢
  rw [h1, Pi.smul_apply, h2, h3, smul_eq_mul]

theorem smoothField_congr (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {ι : Type*}
    {Ψ Φ : ι → R3 → ℝ} (hΨ : ∀ i, Continuous (Ψ i)) (hΦ : ∀ i, Continuous (Φ i)) (h : Ψ = Φ) :
    smoothField hΩ hb Ψ hΨ = smoothField hΩ hb Φ hΦ := by
  subst h; rfl

/-- **Classical time derivatives are `L²(Ω)` time derivatives** on a bounded `Ω`: if
`∂ₜ f(t, x) = f'(t, x)` pointwise with `f'` jointly continuous, then `t ↦ f(t)|_Ω ∈ L²(Ω)` has
derivative `f'(t)|_Ω`. (Mean value theorem and uniform continuity of `f'` on
`[t - 1, t + 1] × cl Ω`.) -/
theorem hasDerivAt_smoothField (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {ι : Type*}
    [Fintype ι] {f f' : ℝ → ι → R3 → ℝ} (hf : ∀ t i, Continuous (f t i))
    (hf' : ∀ i, Continuous fun p : ℝ × R3 => f' p.1 i p.2)
    (hd : ∀ t i x, HasDerivAt (fun s => f s i x) (f' t i x) t) (t : ℝ) :
    HasDerivAt (fun s => smoothField hΩ hb (f s) (hf s))
      (smoothField hΩ hb (f' t) fun i => (hf' i).comp (continuous_const.prodMk continuous_id))
      t := by
  classical
  have : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using hb.measure_lt_top⟩
  set F : ℝ × R3 → (ι → ℝ) := fun p i => f' p.1 i p.2
  have hF : Continuous F := continuous_pi hf'
  set K : Set (ℝ × R3) := Icc (t - 1) (t + 1) ×ˢ closure Ω
  have hK : IsCompact K := isCompact_Icc.prod hb.isCompact_closure
  have huc := hK.uniformContinuousOn_of_continuous hF.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [hasDerivAt_iff_isLittleO]
  refine Asymptotics.IsLittleO.of_bound fun c hc => ?_
  set V : ℝ := (volume.restrict Ω univ).toReal
  set N : ℝ := (Fintype.card ι : ℝ)
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hN : 0 ≤ N := Nat.cast_nonneg _
  set ε : ℝ := c / (Real.sqrt (V * N) + 1)
  have hε : 0 < ε := div_pos hc (by positivity)
  obtain ⟨δ, hδ, hδK⟩ := huc ε hε
  have hη : 0 < min δ 1 := lt_min hδ one_pos
  filter_upwards [Metric.ball_mem_nhds t hη] with s hs
  have hpt : ∀ i, ∀ x ∈ Ω, |f s i x - f t i x - (s - t) * f' t i x| ≤ ε * |s - t| := by
    intro i x hx
    have key := (convex_ball t (min δ 1)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun r => f r i x - r * f' t i x) (f' := fun r => f' r i x - f' t i x) (C := ε)
      (fun r _ => by
        have := (hd r i x).sub ((hasDerivAt_id r).mul_const (f' t i x))
        rw [one_mul] at this
        exact this.hasDerivWithinAt)
      (fun r hr => by
        rw [Metric.mem_ball, Real.dist_eq] at hr
        have hrK : (r, x) ∈ K := ⟨⟨by linarith [abs_lt.1 (lt_of_lt_of_le hr (min_le_right _ _))],
          by linarith [abs_lt.1 (lt_of_lt_of_le hr (min_le_right _ _))]⟩, subset_closure hx⟩
        have htK : (t, x) ∈ K := ⟨⟨by linarith, by linarith⟩, subset_closure hx⟩
        have hdist : dist (r, x) (t, x) < δ := by
          rw [Prod.dist_eq, dist_self, Real.dist_eq]
          exact lt_of_le_of_lt (max_le le_rfl (abs_nonneg _))
            (lt_of_lt_of_le hr (min_le_left _ _))
        have := hδK _ hrK _ htK hdist
        rw [Real.norm_eq_abs, ← Real.dist_eq]
        exact (dist_le_pi_dist (F (r, x)) (F (t, x)) i).trans this.le)
      (Metric.mem_ball_self hη) hs
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at key
    convert key using 2
    ring
  have hcont : ∀ i, Continuous fun x => f s i x - f t i x - (s - t) * f' t i x := fun i =>
    ((hf s i).sub (hf t i)).sub (continuous_const.mul
      ((hf' i).comp (continuous_const.prodMk continuous_id)))
  have e : smoothField hΩ hb (f s) (hf s) - smoothField hΩ hb (f t) (hf t) -
      (s - t) • smoothField hΩ hb (f' t)
        (fun i => (hf' i).comp (continuous_const.prodMk continuous_id)) =
      smoothField hΩ hb (fun i x => f s i x - f t i x - (s - t) * f' t i x) hcont := by
    rw [smoothField_sub, smoothField_smul, smoothField_sub]
  rw [e]
  have hsq : ‖smoothField hΩ hb _ hcont‖ ^ 2 ≤ (Real.sqrt (V * N) * (ε * |s - t|)) ^ 2 := by
    rw [norm_sq_smoothField, mul_pow, Real.sq_sqrt (by positivity)]
    have hb' : ∀ᵐ x ∂(volume.restrict Ω),
        ‖∑ i, (f s i x - f t i x - (s - t) * f' t i x) ^ 2‖ ≤ N * (ε * |s - t|) ^ 2 := by
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      calc ∑ i, (f s i x - f t i x - (s - t) * f' t i x) ^ 2
          ≤ ∑ _i : ι, (ε * |s - t|) ^ 2 := Finset.sum_le_sum fun i _ => by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hpt i x hx) 2
        _ = N * (ε * |s - t|) ^ 2 := by simp [N]
    have := norm_integral_le_of_norm_le_const hb'
    rw [Real.norm_eq_abs] at this
    calc ∫ x, ∑ i, (f s i x - f t i x - (s - t) * f' t i x) ^ 2 ∂volume.restrict Ω
        ≤ |∫ x, ∑ i, (f s i x - f t i x - (s - t) * f' t i x) ^ 2 ∂volume.restrict Ω| :=
          le_abs_self _
      _ ≤ N * (ε * |s - t|) ^ 2 * (volume.restrict Ω univ).toReal := by
          simpa [measureReal_def] using this
      _ = V * N * (ε * |s - t|) ^ 2 := by ring
  have hle := (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  refine hle.trans ?_
  rw [Real.norm_eq_abs, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  have h1 : Real.sqrt (V * N) * ε ≤ (Real.sqrt (V * N) + 1) * ε :=
    mul_le_mul_of_nonneg_right (by linarith) hε.le
  have h2 : (Real.sqrt (V * N) + 1) * ε = c := by
    simp only [ε]; field_simp
  linarith

end TimeDerivative


/-! ## The thesis' complex with inhomogeneous boundary data -/

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3

section Thesis

open ShortHilbertComplex

variable {Ω : Set R3}

/-- The state space `L²(Ω; ℝ³) × L²(Ω; ℝ³ˣ³) × L²(Ω; ℝ³ˣ³)` of `(σ, E, B)`. -/
abbrev State (Ω : Set R3) : Type :=
  PiLp 2 (W3 (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))

/-- The constraint `K = {0} × L²(TSD) × L²(TSD)` of [QuennevilleBelair2015], Prop 4.17. -/
abbrev constraint (Ω : Set R3) :=
  HilbertComplex.totalSub (family3 (⊥ : Submodule ℝ (L2F ℝ Ω (Fin 3))) (tsd Ω) (tsd Ω))

/-- **The operator of (4.14) without boundary conditions**,
`L_max (σ, E, B) = (div E, grad σ − curl B, curl E)` on `H¹ × (H(curl) ∩ H(div)) × H(curl)`:
`L_max = 𝐝_max − 𝐝_min†` for the thesis' complex `H̊¹ → H̊(curl) → L²`. -/
abbrev thesisWaveMax (hΩ : IsOpen Ω) :=
  shortWaveMax (gradCurl ℝ hΩ) (gradCurlMax ℝ hΩ)

/-- The Hodge wave operator of the thesis' complex is the restriction of `L_max` to the fields with
`σ = 0` and `E × n = 0` on `∂Ω` (`σ ∈ H̊¹`, `E ∈ H̊(curl)`). -/
theorem wave_le_thesisWaveMax (hΩ : IsOpen Ω) : (gradCurl ℝ hΩ).wave ≤ thesisWaveMax hΩ :=
  wave_le_shortWaveMax ((gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).minimal_le_maximal hΩ)
    ((curlOp 3 : ConstCoeffOp R3 ℝ _ _).minimal_le_maximal hΩ)

/-- The boundary condition of the homogeneous problem: `U − G ∈ D(L)` iff `σ − σ_G ∈ H̊¹`,
`E − E_G ∈ H̊(curl)` (agreement of `σ` and of the tangential trace `E × n`), given that both lie
in `D(L_max)`. -/
theorem sub_mem_wave_domain_iff (hΩ : IsOpen Ω) {U G : State Ω}
    (hU : U ∈ (thesisWaveMax hΩ).domain) (hG : G ∈ (thesisWaveMax hΩ).domain) :
    U - G ∈ (gradCurl ℝ hΩ).wave.domain ↔
      ((U 0 : L2F ℝ Ω (Fin 3)) - G 0 ∈ ((gradOp 3 3 : ConstCoeffOp R3 ℝ _ _).minimal Ω).domain ∧
        (U 1 : L2F ℝ Ω Ix) - G 1 ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ _ _).minimal Ω).domain) := by
  rw [mem_wave_domain]
  have hU' := mem_shortWaveMax_domain.1 hU
  have hG' := mem_shortWaveMax_domain.1 hG
  constructor
  · rintro ⟨h0, h1, -, -⟩
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩
    exact ⟨h0, h1, Submodule.sub_mem _ hU'.2.2.1 hG'.2.2.1, Submodule.sub_mem _ hU'.2.2.2 hG'.2.2.2⟩

/-- Derivatives of the three components give the derivative of the point of `State Ω`. -/
theorem hasDerivAt_mk3 {f₀ : ℝ → L2F ℝ Ω (Fin 3)} {f₁ f₂ : ℝ → L2F ℝ Ω Ix}
    {f₀' : L2F ℝ Ω (Fin 3)} {f₁' f₂' : L2F ℝ Ω Ix} {t : ℝ} (h₀ : HasDerivAt f₀ f₀' t)
    (h₁ : HasDerivAt f₁ f₁' t) (h₂ : HasDerivAt f₂ f₂' t) :
    HasDerivAt (fun t => (mk3 (f₀ t) (f₁ t) (f₂ t) : State Ω)) (mk3 f₀' f₁' f₂') t := by
  have h : HasDerivAt (fun t => WithLp.ofLp (mk3 (f₀ t) (f₁ t) (f₂ t) : State Ω))
      (WithLp.ofLp (mk3 f₀' f₁' f₂' : State Ω)) t := by
    rw [hasDerivAt_pi]
    intro i; fin_cases i
    exacts [h₀, h₁, h₂]
  have := (PiLp.continuousLinearEquiv 2 ℝ
    (W3 (L2F ℝ Ω (Fin 3)) (L2F ℝ Ω Ix) (L2F ℝ Ω Ix))).symm.hasFDerivAt.comp_hasDerivAt t h
  simpa [Function.comp_def] using this

end Thesis

/-! ## Whole-space TSD solutions and their restrictions -/

/-- A **classical TSD solution of the Einstein–Bianchi system on `ℝ³`** with `σ = 0`: fields
`E, B : ℝ → ℝ³ˣ³-valued functions on ℝ³`, `C¹` in space, with jointly continuous `curl E`,
`curl B`, solving `∂ₜ E = −curl B`, `∂ₜ B = curl E` pointwise, and symmetric, trace-free and
row-wise divergence-free at every point and time. The plane wave of [QuennevilleBelair2015], Ch. 7,
is one (`Feec.Numerics.PlaneWaveCube.planeWaveTSD`). No integrability on `ℝ³` is assumed. -/
structure WholeSpaceTSD where
  E : ℝ → Ix → R3 → ℝ
  B : ℝ → Ix → R3 → ℝ
  contDiff_E : ∀ t ij, ContDiff ℝ 1 (E t ij)
  contDiff_B : ∀ t ij, ContDiff ℝ 1 (B t ij)
  continuous_curl_E : ∀ ij, Continuous fun p : ℝ × R3 => curlM (E p.1) ij p.2
  continuous_curl_B : ∀ ij, Continuous fun p : ℝ × R3 => curlM (B p.1) ij p.2
  hasDerivAt_E : ∀ t ij x, HasDerivAt (fun s => E s ij x) (-curlM (B t) ij x) t
  hasDerivAt_B : ∀ t ij x, HasDerivAt (fun s => B s ij x) (curlM (E t) ij x) t
  symm_E : ∀ t i j x, E t (i, j) x = E t (j, i) x
  symm_B : ∀ t i j x, B t (i, j) x = B t (j, i) x
  trace_E : ∀ t x, ∑ i, E t (i, i) x = 0
  trace_B : ∀ t x, ∑ i, B t (i, i) x = 0
  div_E : ∀ t j x, ∑ k, pd k (E t (j, k)) x = 0
  div_B : ∀ t j x, ∑ k, pd k (B t (j, k)) x = 0

namespace WholeSpaceTSD

open ShortHilbertComplex

variable (W : WholeSpaceTSD) {Ω : Set R3} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)

theorem continuous_E (t : ℝ) (ij : Ix) : Continuous (W.E t ij) := (W.contDiff_E t ij).continuous

theorem continuous_B (t : ℝ) (ij : Ix) : Continuous (W.B t ij) := (W.contDiff_B t ij).continuous

theorem continuous_curlM_E (t : ℝ) (ij : Ix) : Continuous (curlM (W.E t) ij) :=
  (W.continuous_curl_E ij).comp (continuous_const.prodMk continuous_id)

theorem continuous_curlM_B (t : ℝ) (ij : Ix) : Continuous (curlM (W.B t) ij) :=
  (W.continuous_curl_B ij).comp (continuous_const.prodMk continuous_id)

/-- `E(t)|_Ω ∈ L²(Ω; ℝ³ˣ³)`. -/
abbrev fieldE (t : ℝ) : L2F ℝ Ω Ix := smoothField hΩ hb (W.E t) (W.continuous_E t)

/-- `B(t)|_Ω ∈ L²(Ω; ℝ³ˣ³)`. -/
abbrev fieldB (t : ℝ) : L2F ℝ Ω Ix := smoothField hΩ hb (W.B t) (W.continuous_B t)

/-- **The restriction** `R(t) = (0, E(t)|_Ω, B(t)|_Ω)`. -/
def restrict (t : ℝ) := mk3 (0 : L2F ℝ Ω (Fin 3)) (W.fieldE hΩ hb t) (W.fieldB hΩ hb t)

/-- Its time derivative `R'(t) = (0, −curl B(t)|_Ω, curl E(t)|_Ω) = L_max R(t)`. -/
def restrictDeriv (t : ℝ) :=
  mk3 (0 : L2F ℝ Ω (Fin 3)) (smoothField hΩ hb (fun ij x => -curlM (W.B t) ij x)
      fun ij => (W.continuous_curlM_B t ij).neg)
    (smoothField hΩ hb (curlM (W.E t)) (W.continuous_curlM_E t))

theorem fieldE_mem_tsd (t : ℝ) : W.fieldE hΩ hb t ∈ tsd Ω :=
  smoothField_mem_tsd hΩ hb (W.contDiff_E t) (fun i j x _ => W.symm_E t i j x)
    (fun x _ => W.trace_E t x) (fun j x _ => W.div_E t j x)

theorem fieldB_mem_tsd (t : ℝ) : W.fieldB hΩ hb t ∈ tsd Ω :=
  smoothField_mem_tsd hΩ hb (W.contDiff_B t) (fun i j x _ => W.symm_B t i j x)
    (fun x _ => W.trace_B t x) (fun j x _ => W.div_B t j x)

/-- **The restriction is TSD at every time**: `R(t) ∈ K = {0} × L²(TSD) × L²(TSD)`. -/
theorem restrict_mem (t : ℝ) : W.restrict hΩ hb t ∈ constraint Ω :=
  mem_totalSub_family3.2 ⟨Submodule.zero_mem _, W.fieldE_mem_tsd hΩ hb t, W.fieldB_mem_tsd hΩ hb t⟩

/-- `E ∈ H(curl)` with `curl_max E = curl E`. -/
theorem fieldE_mem_curl_maximal (t : ℝ) :
    ∃ h : W.fieldE hΩ hb t ∈ ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).maximal Ω).domain,
      (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).maximal Ω ⟨_, h⟩ =
        smoothField hΩ hb (curlM (W.E t)) (W.continuous_curlM_E t) := by
  have hcurl : ∀ ij, MemLp ((curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).apply (W.E t) ij) 2
      (volume.restrict Ω) := fun ij => by
    rw [← curlM_eq_apply]
    exact memLp_of_continuous hΩ.measurableSet hb (W.continuous_curlM_E t ij)
  obtain ⟨hmem, hval⟩ := (curlOp 3 : ConstCoeffOp R3 ℝ Ix Ix).smooth_mem_maximal_domain
    hΩ (N := 1) curlOp_isOrderLE (W.contDiff_E t)
    (fun ij => memLp_of_continuous hΩ.measurableSet hb (W.continuous_E t ij)) hcurl
  refine ⟨hmem, hval.trans ?_⟩
  refine (WithLp.ext_iff 2).2 (funext fun ij => ?_)
  exact MemLp.toLp_congr (hcurl ij) (memLp_of_continuous hΩ.measurableSet hb
    (W.continuous_curlM_E t ij)) (Eventually.of_forall fun x => by rw [← curlM_eq_apply])

/-- `(R(t), R'(t)) ∈ graph L_max`: `L_max R(t) = (div E, −curl B, curl E) = (0, −curl B, curl E)`. -/
theorem mem_graph_thesisWaveMax (t : ℝ) :
    (W.restrict hΩ hb t, W.restrictDeriv hΩ hb t) ∈ (thesisWaveMax hΩ).graph := by
  obtain ⟨hE1, hE1v⟩ := W.fieldE_mem_curl_maximal hΩ hb t
  obtain ⟨y, hyE, hy0⟩ :=
    LinearPMap.mem_ker_iff.1 ((mem_tsd_iff_ker hΩ).1 (W.fieldE_mem_tsd hΩ hb t)).2.2
  have hE0 : W.fieldE hΩ hb t ∈ (gradCurl ℝ hΩ).d₀†.domain := hyE ▸ y.2
  have hE0v : (gradCurl ℝ hΩ).d₀† ⟨_, hE0⟩ = 0 := by
    rw [← hy0]; congr 1; exact Subtype.ext hyE
  obtain ⟨hB2, hB2v⟩ := smoothField_mem_adjoint hΩ hb (gradCurl ℝ hΩ) le_rfl (W.contDiff_B t)
  refine mk3_mem_graph_shortWaveMax (S := gradCurl ℝ hΩ) (S' := gradCurlMax ℝ hΩ)
    (Submodule.zero_mem _) hE1 hE0 hB2 ?_ ?_ ?_
  · rw [hE0v, neg_zero]
  · have h00 : (gradCurlMax ℝ hΩ).d₀ ⟨0, Submodule.zero_mem _⟩ = 0 := LinearPMap.map_zero _
    rw [h00, zero_sub, hB2v, ← neg_one_smul ℝ (smoothField _ _ _ _), smoothField_smul]
    exact smoothField_congr hΩ hb _ _ (by funext ij x; ring)
  · exact hE1v.symm

/-- `R' = (0, −curl B, curl E)` in `L²(Ω)`. -/
theorem hasDerivAt_restrict (t : ℝ) :
    HasDerivAt (W.restrict hΩ hb) (W.restrictDeriv hΩ hb t) t := by
  have hE := hasDerivAt_smoothField hΩ hb (W.continuous_E) (f' := fun s ij x => -curlM (W.B s) ij x)
    (fun ij => (W.continuous_curl_B ij).neg) W.hasDerivAt_E t
  have hB := hasDerivAt_smoothField hΩ hb (W.continuous_B) (f' := fun s ij x => curlM (W.E s) ij x)
    W.continuous_curl_E W.hasDerivAt_B t
  exact hasDerivAt_mk3 (hasDerivAt_const t (0 : L2F ℝ Ω (Fin 3))) hE hB

/-- **The restriction solves the problem without boundary conditions**: `R' = L_max R` on every
time set. -/
theorem isStrongSolution_restrict (I : Set ℝ) :
    Evolution.IsStrongSolution (thesisWaveMax hΩ) I 0 (W.restrict hΩ hb) :=
  Evolution.IsStrongSolution.of_deriv fun t _ => ⟨_, W.mem_graph_thesisWaveMax hΩ hb t, by
    rw [Pi.zero_apply, add_zero]; exact (W.hasDerivAt_restrict hΩ hb t).hasDerivWithinAt⟩

/-- `R` is a lifting with `R' = L_max R`. -/
theorem isLifting (I : Set ℝ) :
    Evolution.IsLifting (thesisWaveMax hΩ) I (W.restrict hΩ hb) (W.restrictDeriv hΩ hb)
      (W.restrictDeriv hΩ hb) :=
  ⟨fun t _ => W.mem_graph_thesisWaveMax hΩ hb t, fun t _ =>
    (W.hasDerivAt_restrict hΩ hb t).hasDerivWithinAt⟩


/-! ### Uniqueness, existence and TSD propagation for the data of `R` -/

/-- The restriction solves the problem with its own boundary data. -/
theorem isBoundarySolution_restrict (I : Set ℝ) :
    Evolution.IsBoundarySolution (thesisWaveMax hΩ) (gradCurl ℝ hΩ).wave I 0 (W.restrict hΩ hb)
      (W.restrict hΩ hb) :=
  Evolution.isBoundarySolution_self (W.isStrongSolution_restrict hΩ hb I)

/-- **The restriction is the unique solution with its own boundary data**: every solution `V` of
`V' = L_max V` on `[a, b]` with `σ = 0` and `E × n = E_R × n` on `∂Ω` and `V(a) = R(a)` is `R`.
In particular it is TSD at every time (`restrict_mem`). -/
theorem restrict_unique {a b : ℝ} {V : ℝ → State Ω}
    (hV : Evolution.IsBoundarySolution (thesisWaveMax hΩ) (gradCurl ℝ hΩ).wave (Icc a b) 0
      (W.restrict hΩ hb) V) (hV0 : V a = W.restrict hΩ hb a) :
    EqOn V (W.restrict hΩ hb) (Icc a b) :=
  Evolution.isBoundarySolution_self_unique (wave_le_thesisWaveMax hΩ)
    (gradCurl ℝ hΩ).isSkewAdjoint_wave.isDissipative (W.isStrongSolution_restrict hΩ hb _) hV0 hV

/-- **TSD propagation for the data of `R`**: the solution with the boundary data and the initial
value of `R` stays in `K` for all `t ∈ [a, b]`. -/
theorem restrict_propagates {a b : ℝ} {V : ℝ → State Ω}
    (hV : Evolution.IsBoundarySolution (thesisWaveMax hΩ) (gradCurl ℝ hΩ).wave (Icc a b) 0
      (W.restrict hΩ hb) V) (hV0 : V a = W.restrict hΩ hb a) :
    ∀ t ∈ Icc a b, V t ∈ constraint Ω := fun t ht => by
  rw [W.restrict_unique hΩ hb hV hV0 ht]
  exact W.restrict_mem hΩ hb t

theorem forcing_eq_zero :
    (0 - W.restrictDeriv hΩ hb + W.restrictDeriv hΩ hb : ℝ → State Ω) = 0 := by
  funext t; simp

/-- **Existence and uniqueness** with the boundary data of `R`: for every `U₀` with
`U₀ − R(a) ∈ D(L)` there is a unique solution of `U' = L_max U` on `[a, b]` with the boundary
data of `R` (`σ = 0`, `E × n = E_R × n`) and `U(a) = U₀`. -/
theorem existsUnique {a b : ℝ} {U₀ : State Ω} (hU₀ : U₀ - W.restrict hΩ hb a ∈ (gradCurl ℝ hΩ).wave.domain) :
    ∃ U, U a = U₀ ∧ Evolution.IsBoundarySolution (thesisWaveMax hΩ) (gradCurl ℝ hΩ).wave
        (Icc a b) 0 (W.restrict hΩ hb) U ∧
      ∀ V, V a = U₀ → Evolution.IsBoundarySolution (thesisWaveMax hΩ) (gradCurl ℝ hΩ).wave
        (Icc a b) 0 (W.restrict hΩ hb) V → EqOn V U (Icc a b) := by
  have hF : Evolution.ForcingClass.admissible (gradCurl ℝ hΩ).wave a b
      (0 - W.restrictDeriv hΩ hb + W.restrictDeriv hΩ hb) := by
    rw [W.forcing_eq_zero hΩ hb]
    exact Evolution.ForcingClass.admissible_zero _ a b
  obtain ⟨U, hU0, hU, -, huniq⟩ := Evolution.existsUnique_isBoundarySolution
    (gradCurl ℝ hΩ).isSkewAdjoint_wave (wave_le_thesisWaveMax hΩ) (W.isLifting hΩ hb _) hU₀ hF
  exact ⟨U, hU0, hU, huniq⟩

/-- **The solution is `R` plus a homogeneous solution**: `U(t) = R(t) + e^{tL}(U(0) − R(0))` on
`[0, T]`, where `e^{tL}` is the wave group of the thesis' complex (homogeneous boundary
conditions). -/
theorem eq_add_waveGroup {T : ℝ} {U : ℝ → State Ω}
    (hU : Evolution.IsBoundarySolution (thesisWaveMax hΩ) (gradCurl ℝ hΩ).wave (Icc 0 T) 0
      (W.restrict hΩ hb) U) :
    ∀ t ∈ Icc 0 T, U t = W.restrict hΩ hb t +
      (gradCurl ℝ hΩ).toHilbertComplex.waveGroup.S t (U 0 - W.restrict hΩ hb 0) := by
  have hW := (Evolution.isBoundarySolution_iff (wave_le_thesisWaveMax hΩ) (W.isLifting hΩ hb _)).1 hU
  rw [W.forcing_eq_zero hΩ hb] at hW
  intro t ht
  have h0mem : U 0 - W.restrict hΩ hb 0 ∈ (gradCurl ℝ hΩ).wave.domain :=
    hU.sub_mem 0 ⟨le_rfl, ht.1.trans ht.2⟩
  have := (gradCurl ℝ hΩ).toHilbertComplex.eq_waveGroup_of_isStrongSolution h0mem rfl hW ht
  rw [← this, Pi.sub_apply, add_sub_cancel]


/-- **TSD propagation for data from a whole-space TSD solution, characterized**: a solution `U`
on `[0, T]` with the boundary data of `R` stays in `K = {0} × L²(TSD) × L²(TSD)` iff the
homogeneous solution `e^{tL}(U(0) − R(0))` (thesis' boundary conditions, no inhomogeneous data)
from the difference of the initial values stays in `K`. -/
theorem mem_iff {T : ℝ} {U : ℝ → State Ω}
    (hU : Evolution.IsBoundarySolution (thesisWaveMax hΩ) (gradCurl ℝ hΩ).wave (Icc 0 T) 0
      (W.restrict hΩ hb) U) :
    (∀ t ∈ Icc 0 T, U t ∈ constraint Ω) ↔ ∀ t ∈ Icc 0 T,
      (gradCurl ℝ hΩ).toHilbertComplex.waveGroup.S t (U 0 - W.restrict hΩ hb 0) ∈
        constraint Ω := by
  refine forall₂_congr fun t ht => ?_
  rw [W.eq_add_waveGroup hΩ hb hU t ht]
  exact Submodule.add_mem_iff_right _ (W.restrict_mem hΩ hb t)

/-- **Sufficient condition**: if `U(0) − R(0)` lies in the invariant core `K*` of the homogeneous
problem (the largest reducing subcomplex inside `K`), the solution with the boundary data of `R`
stays TSD. This contains the datum `U(0) = R(0)` (`restrict_propagates`). -/
theorem mem_of_mem_coreSub {T : ℝ} {U : ℝ → State Ω}
    (hU : Evolution.IsBoundarySolution (thesisWaveMax hΩ) (gradCurl ℝ hΩ).wave (Icc 0 T) 0
      (W.restrict hΩ hb) U)
    (hcore : U 0 - W.restrict hΩ hb 0 ∈ (gradCurl ℝ hΩ).coreSub (tsd Ω) (tsd Ω)) :
    ∀ t ∈ Icc 0 T, U t ∈ constraint Ω :=
  (W.mem_iff hΩ hb hU).2 fun t _ => ShortHilbertComplex.mem_coreSub.1 hcore t

end WholeSpaceTSD


end Feec.Models.Cube.Inhomogeneous
