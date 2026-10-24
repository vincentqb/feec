module

public import Feec.HilbertComplex.Approximation.ConstrainedFEEC
public import Feec.HilbertComplex.Approximation.SkewFEEC
public import Feec.Semigroup.DomainSq

/-!
# The approximating FEEC theorem

An **approximating FEEC discretization** (`Feec.HilbertComplex.ApproxFEEC`) of the Hodge wave
equation `ξ' = L ξ` (`L = 𝐝 - 𝐝†`) of a Hilbert complex `H` is a skew FEEC discretization
(`Feec.HilbertComplex.SkewFEEC`) of the skew-adjoint wave operator: it allows variational crimes
(its discrete spaces `Xₕ` are Hilbert spaces of their own, not subspaces of `W`, with their own
inner products, not necessarily finite-dimensional), its discrete generators `Lₕ` are bounded and
skew in the discrete inner product (so `e^{tLₕ}` is unitary: uniform stability), and it is read
in `W` through uniformly bounded maps `ιₕ : Xₕ → W` with uniformly bounded left inverses `πₕ`
(`πₕ ιₕ = 1`). Its comparisons, cores and rate classes are those of `Feec.HilbertComplex.DissipFEEC`;
its exact group `SkewFEEC.U` is the wave group `e^{tL}` of `H`.

`ApproxFEEC` is a **semigroup-form** abstraction: it carries no discrete differential `𝐝ₕ` and
no cochain condition on `ιₕ`; the complex structure of the discrete spaces is not a hypothesis.
Consequently it cannot express discrete constraints such as `𝐝ₕ`-closedness being preserved; the
constraint residual is measured in `W`, through `ιₕ`. The complex-level front end
`ApproxFEEC.ofComplex` (`Feec.HilbertComplex.Approximation.ApproxComplex`) builds an `ApproxFEEC`
from a family of discrete Hilbert complexes with cochain maps `iₕ` ([HolstStern2012], §3), derives
its core from the inner-product defect and the graph-norm approximation property, and states the
discrete constraints (`approxFEEC_ofComplex`).

## Main results

The **approximating FEEC theorem** `approxFEEC` (statement `ApproxFEEC.Verdict`) is the
skew-adjoint FEEC theorem `skewFEEC` for the wave operator (which contains the dissipative FEEC
theorem `dissipFEEC`), together with the conclusions specific to Hilbert complexes:

1. `approxFEEC_unique_weak`: weak solutions of the Hodge wave equation are unique
   ([QuennevilleBelair2015], Thm 4.7);
2. `approxFEEC_isReducing_iff_keeps`: on a graded complex, for an `R`-invariant `K` with
   `D(L) ∩ K` dense in `K`, `K` reduces `L` iff `e^{tL} K ⊆ K` for `t ≥ 0` (forward propagation
   suffices, [QuennevilleBelair2015], Prop. 4.17); with `dissipFEEC_leaves_smooth`, a
   non-reducing such `K` is left by a datum of `D(L) ∩ K` forward in time.

Constructions of cores: `ApproxFEEC.Core.ofOperator` (the Trotter–Kato bridge on the graph space:
an operator `Rₕ : Γ(𝐝) → Xₕ` with `ιₕ Rₕ → graphFst` pointwise and a defect identity on `D(L²)`
with uniformly bounded defect operators tending to `0` pointwise; uniformity on `[0, T]` comes
from the compactness of the orbits `waveOrbit`), and `ApproxFEEC.complexify` runs a real scheme on
real and imaginary parts.

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3 (Thm 3.9, Thm 3.10)
* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §3.4 (Trotter–Kato approximation theorems)
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.4 (Thms 4.6, 4.7), §4.10 (Prop. 4.17)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap Metric

@[expose] public noncomputable section

universe u

namespace Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

/-! ### Orbits of `D(L²)` in the graph space -/

section Orbit

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- `L e^{tL} x = e^{tL} L x` on `D(L)`. -/
theorem wave_waveGroup {H : HilbertComplex 𝕜 c W} {x : PiLp 2 W} (hx : x ∈ H.wave.domain)
    (t : ℝ) :
    H.wave ⟨H.waveGroup.S t x, waveGroup_mem_domain H hx t⟩ =
      H.waveGroup.S t (H.wave ⟨x, hx⟩) := by
  have hg := H.generator_waveGroup
  have hx' : x ∈ H.waveGroup.generator.domain := by rw [hg]; exact hx
  have h := H.waveGroup.generator_apply_S ⟨x, hx'⟩ t
  rwa [LinearPMap.apply_eq_of_eq hg _ ⟨H.waveGroup.S t x, waveGroup_mem_domain H hx t⟩ rfl,
    LinearPMap.apply_eq_of_eq hg _ ⟨x, hx⟩ rfl] at h

variable (H : HilbertComplex 𝕜 c W)

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
open scoped Classical in
/-- `L` on `D(L)`, extended by `0`. -/
def waveExt (x : PiLp 2 W) : PiLp 2 W :=
  if hx : x ∈ H.wave.domain then H.wave ⟨x, hx⟩ else 0

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
variable {H} in
theorem waveExt_of_mem {x : PiLp 2 W} (hx : x ∈ H.wave.domain) :
    H.waveExt x = H.wave ⟨x, hx⟩ := by
  unfold waveExt; simp [hx]

open scoped Classical in
/-- The graph-space orbit `t ↦ (e^{tL} x, 𝐝 e^{tL} x)` of `x ∈ D(L)` (`0` off `D(L)`). -/
def waveOrbit (x : PiLp 2 W) (t : ℝ) : H.totalD.GraphSpace :=
  if hx : x ∈ H.wave.domain then waveLift H ⟨H.waveGroup.S t x, waveGroup_mem_domain H hx t⟩
  else 0

theorem waveOrbit_of_mem {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (t : ℝ) :
    waveOrbit H x t = waveLift H ⟨H.waveGroup.S t x, waveGroup_mem_domain H hx t⟩ := by
  unfold waveOrbit; simp [hx]

theorem graphFst_waveOrbit {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (t : ℝ) :
    H.totalD.graphFst (waveOrbit H x t) = H.waveGroup.S t x := by
  rw [waveOrbit_of_mem H hx]; rfl

/-- The orbit of `L x` is the lift of `L e^{tL} x`. -/
theorem waveOrbit_waveExt {x : PiLp 2 W} (hx : x ∈ H.wave.domainSq) (t : ℝ) :
    waveOrbit H (waveExt H x) t = waveLift H ⟨H.wave ⟨H.waveGroup.S t x,
      waveGroup_mem_domain H (domainSq_le_domain hx) t⟩, by
        rw [wave_waveGroup (domainSq_le_domain hx) t]
        exact waveGroup_mem_domain H (mem_domainSq.1 hx).2 t⟩ := by
  have hx1 := domainSq_le_domain hx
  have hx2 : waveExt H x ∈ H.wave.domain := by
    rw [waveExt_of_mem hx1]; exact (mem_domainSq.1 hx).2
  rw [waveOrbit_of_mem H hx2]
  congr 2
  rw [wave_waveGroup hx1 t, waveExt_of_mem hx1]

/-- **The graph-space orbit of `x ∈ D(L²)` is `C¹`**, with derivative the orbit of `L x`. -/
theorem waveOrbit_isC1 {x : PiLp 2 W} (hx : x ∈ H.wave.domainSq) {b : ℝ} (hb : 0 < b) :
    ContinuousOn (waveOrbit H x) (Icc 0 b) ∧
      ContinuousOn (waveOrbit H (waveExt H x)) (Icc 0 b) ∧
      ∀ t ∈ Icc 0 b, HasDerivWithinAt (waveOrbit H x) (waveOrbit H (waveExt H x) t)
        (Icc 0 b) t := by
  have hx1 := domainSq_le_domain hx
  have hLx : H.wave ⟨x, hx1⟩ ∈ H.wave.domain := (mem_domainSq.1 hx).2
  have hx2 : waveExt H x ∈ H.wave.domain := by rw [waveExt_of_mem hx1]; exact hLx
  obtain ⟨ξ, ξ', hξ, hξS, hξ'S⟩ := exists_isGraphSolution_waveGroup H hx1 hLx hb
  have e1 : ξ = waveOrbit H x := funext fun t => H.totalD.graphFst_injective (by
    rw [hξS, graphFst_waveOrbit H hx1])
  have e2 : EqOn ξ' (waveOrbit H (waveExt H x)) (Icc 0 b) := fun t ht =>
    H.totalD.graphFst_injective (by
      rw [hξ'S t ht, graphFst_waveOrbit H hx2, waveExt_of_mem hx1])
  subst e1
  refine ⟨hξ.continuousOn, hξ.continuousOn_deriv.congr fun t ht => (e2 ht).symm,
    fun t ht => ?_⟩
  rw [← e2 ht]
  exact hξ.deriv t ht

/-- The `C¹` facts of `waveOrbit_isC1` on `[0, T]`, with right derivatives. -/
theorem waveOrbit_isC1' {x : PiLp 2 W} (hx : x ∈ H.wave.domainSq) (T : ℝ) :
    ContinuousOn (waveOrbit H x) (Icc 0 T) ∧
      ContinuousOn (waveOrbit H (waveExt H x)) (Icc 0 T) ∧
      ∀ t ∈ Ico 0 T, HasDerivWithinAt (waveOrbit H x) (waveOrbit H (waveExt H x) t)
        (Ici t) t := by
  have hb : (0 : ℝ) < max T 0 + 1 := by positivity
  have hsub : Icc 0 T ⊆ Icc 0 (max T 0 + 1) :=
    Icc_subset_Icc le_rfl (by linarith [le_max_left T 0])
  obtain ⟨h1, h2, h3⟩ := waveOrbit_isC1 H hx hb
  refine ⟨h1.mono hsub, h2.mono hsub, fun t ht => ?_⟩
  have ht' : t ∈ Ico 0 (max T 0 + 1) := ⟨ht.1, by linarith [ht.2, le_max_left T 0]⟩
  exact (h3 t (Ico_subset_Icc_self ht')).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht')

/-- The orbits of `x ∈ D(L²)` and of `L x` on `[0, T]` are compact in the graph space. -/
theorem isCompact_waveOrbit {x : PiLp 2 W} (hx : x ∈ H.wave.domainSq) (T : ℝ) :
    IsCompact (waveOrbit H x '' Icc 0 T) ∧ IsCompact (waveOrbit H (waveExt H x) '' Icc 0 T) :=
  ⟨isCompact_Icc.image_of_continuousOn (waveOrbit_isC1' H hx T).1,
    isCompact_Icc.image_of_continuousOn (waveOrbit_isC1' H hx T).2.1⟩

end Orbit

/-! ### Approximating FEEC discretizations -/

/-- An **approximating FEEC discretization** (semigroup form) of the Hodge wave equation of `H`:
a skew FEEC discretization of the skew-adjoint wave operator `L = 𝐝 - 𝐝†`, that is, a closed
constraint `K`; Hilbert spaces `Xₕ` with their own inner products (not subspaces of `W`, not
necessarily finite-dimensional) and skew bounded generators `Lₕ`; uniformly bounded
`ιₕ : Xₕ → W`, `πₕ : W → Xₕ` with `πₕ ιₕ = 1`. [HolstStern2012], §3 -/
abbrev ApproxFEEC (H : HilbertComplex 𝕜 c W) (κ : Type*) :=
  SkewFEEC.{u} H.isSkewAdjoint_wave κ

namespace ApproxFEEC

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxFEEC.{u} H κ)

/-- For `t ≥ 0`, the exact flow of an approximating FEEC discretization is the wave group
(its exact group `SkewFEEC.U` is the wave group by definition). -/
theorem S_apply {t : ℝ} (ht : 0 ≤ t) (x : PiLp 2 W) : F.S t x = H.waveGroup.S t x :=
  SkewFEEC.S_apply F ht x

/-! ### The Trotter–Kato bridge -/

/-- Comparison trajectories `pₕ(t) = Rₕ (e^{tL} x, 𝐝 e^{tL} x)` of an operator
`Rₕ : Γ(𝐝) → Xₕ`, on `D(L²)`, with derivatives `pₕ'(t) = Rₕ (L e^{tL} x, 𝐝 L e^{tL} x)`. -/
def Comparison.ofOperator (R : ∀ h, H.totalD.GraphSpace →L[𝕜] F.X h) (T : ℝ) :
    F.Comparison T where
  Data := H.wave.domainSq
  p x h t := R h (waveOrbit H x t)
  p' x h t := R h (waveOrbit H (waveExt H x) t)
  continuousOn _ hx h := (R h).continuous.comp_continuousOn (waveOrbit_isC1' H hx T).1
  continuousOn' _ hx h := (R h).continuous.comp_continuousOn (waveOrbit_isC1' H hx T).2.1
  hasDerivWithinAt _ hx h t ht :=
    ((R h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t
      ((waveOrbit_isC1' H hx T).2.2 t ht)

/-- Uniform approximation along the orbits, from pointwise approximation by uniformly bounded
`ιₕ Rₕ` (compactness of the orbit). -/
theorem tendstoUniformlyOn_ofOperator (R : ∀ h, H.totalD.GraphSpace →L[𝕜] F.X h)
    (hR : ∃ C, ∀ h, ‖R h‖ ≤ C)
    (happrox : ∀ ζ, Tendsto (fun h => F.incl h (R h ζ)) F.l (𝓝 (H.totalD.graphFst ζ)))
    (T : ℝ) {x : PiLp 2 W} (hx : x ∈ H.wave.domainSq) :
    TendstoUniformlyOn (fun h t => F.incl h (R h (waveOrbit H x t)))
      (fun t => H.waveGroup.S t x) F.l (Icc 0 T) := by
  obtain ⟨C, hC⟩ := hR
  set A : ∀ _ : κ, H.totalD.GraphSpace →L[𝕜] PiLp 2 W := fun h =>
    H.totalD.graphFst - F.incl h ∘L R h
  have hA : ∀ h ζ, ‖A h ζ‖ ≤ (1 + F.boundConst * max C 0) * ‖ζ‖ := fun h ζ => by
    have h1 := HodgeWave.norm_graphFst_le (T := H.totalD) ζ
    have h2 : ‖F.incl h (R h ζ)‖ ≤ F.boundConst * (max C 0 * ‖ζ‖) :=
      (F.norm_incl_apply_le h _).trans (mul_le_mul_of_nonneg_left
        (((R h).le_opNorm ζ).trans (mul_le_mul_of_nonneg_right
          ((hC h).trans (le_max_left _ _)) (norm_nonneg _))) F.boundConst_nonneg)
    calc ‖A h ζ‖ ≤ ‖H.totalD.graphFst ζ‖ + ‖F.incl h (R h ζ)‖ := norm_sub_le _ _
      _ ≤ _ := by nlinarith
  have hlim : ∀ ζ, Tendsto (fun h => ‖A h ζ‖) F.l (𝓝 0) := fun ζ => by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 (happrox ζ))
    refine this.congr fun h => ?_
    rw [norm_sub_rev]; rfl
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_forall_norm_lt_of_tendsto hA hlim (isCompact_waveOrbit H hx T).1
    hε] with h hh t ht
  have := hh _ (mem_image_of_mem _ ht)
  rw [dist_eq_norm]
  convert this using 2
  simp only [A, _root_.sub_apply, ContinuousLinearMap.comp_apply,
    graphFst_waveOrbit H (domainSq_le_domain hx)]

/-- **The Trotter–Kato bridge**: an operator `Rₕ : Γ(𝐝) → Xₕ`, uniformly bounded, with
`ιₕ Rₕ ζ → graphFst ζ`, and a defect identity on `D(L²)`,
`Rₕ (L y) - Lₕ Rₕ y = Δₕ (L y) + Δₕ' y` (lifted to `Γ(𝐝)`), with uniformly bounded `Δₕ`, `Δₕ'`
tending to `0` pointwise, give a core `D(L²)`; uniformity on `[0, T]` comes from the compactness
of the orbits. [Pazy1983], §3.4 -/
def Core.ofOperator (R : ∀ h, H.totalD.GraphSpace →L[𝕜] F.X h)
    (hR : ∃ C, ∀ h, ‖R h‖ ≤ C)
    (happrox : ∀ ζ, Tendsto (fun h => F.incl h (R h ζ)) F.l (𝓝 (H.totalD.graphFst ζ)))
    (Δ Δ' : ∀ h, H.totalD.GraphSpace →L[𝕜] F.X h) (hΔ : ∃ C, ∀ h, ‖Δ h‖ ≤ C ∧ ‖Δ' h‖ ≤ C)
    (hdef : ∀ h (y : H.wave.domain) (hLy : H.wave y ∈ H.wave.domain),
      R h (waveLift H ⟨_, hLy⟩) - F.L h (R h (waveLift H y)) =
        Δ h (waveLift H ⟨_, hLy⟩) + Δ' h (waveLift H y))
    (hΔ0 : ∀ ζ, Tendsto (fun h => ‖Δ h ζ‖) F.l (𝓝 0))
    (hΔ'0 : ∀ ζ, Tendsto (fun h => ‖Δ' h ζ‖) F.l (𝓝 0)) : F.Core where
  Data := H.wave.domainSq
  cmp T := Comparison.ofOperator F R T
  data_eq _ := rfl
  tendsto_approx T _ hx := (F.tendstoUniformlyOn_ofOperator R hR happrox T hx).congr_right
    fun t ht => (F.S_apply ht.1 _).symm
  tendsto_defect T x hx := by
    obtain ⟨C, hC⟩ := hΔ
    have hb1 : ∀ h ζ, ‖Δ h ζ‖ ≤ C * ‖ζ‖ := fun h ζ => ((Δ h).le_opNorm ζ).trans
      (mul_le_mul_of_nonneg_right (hC h).1 (norm_nonneg _))
    have hb2 : ∀ h ζ, ‖Δ' h ζ‖ ≤ C * ‖ζ‖ := fun h ζ => ((Δ' h).le_opNorm ζ).trans
      (mul_le_mul_of_nonneg_right (hC h).2 (norm_nonneg _))
    have hx1 := domainSq_le_domain hx
    have hdefect : ∀ h t, ‖(Comparison.ofOperator F R T).defect x h t‖ ≤
        ‖Δ h (waveOrbit H (waveExt H x) t)‖ + ‖Δ' h (waveOrbit H x t)‖ := fun h t => by
      have e := hdef h ⟨H.waveGroup.S t x, waveGroup_mem_domain H hx1 t⟩ (by
        rw [wave_waveGroup hx1 t]; exact waveGroup_mem_domain H (mem_domainSq.1 hx).2 t)
      change ‖R h (waveOrbit H (waveExt H x) t) - F.L h (R h (waveOrbit H x t))‖ ≤ _
      rw [waveOrbit_waveExt H (SetLike.mem_coe.1 hx), waveOrbit_of_mem H hx1, e]
      exact norm_add_le _ _
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [eventually_forall_norm_lt_of_tendsto hb1 hΔ0
      (isCompact_waveOrbit H hx T).2 (half_pos hε),
      eventually_forall_norm_lt_of_tendsto hb2 hΔ'0 (isCompact_waveOrbit H hx T).1
        (half_pos hε)] with h h1 h2 t ht
    rw [dist_eq_norm, zero_sub, norm_neg, Real.norm_of_nonneg (norm_nonneg _)]
    have := hdefect h t
    linarith [h1 _ (mem_image_of_mem _ ht), h2 _ (mem_image_of_mem _ ht)]

/-! ### Complexification (real schemes for complex data: real and imaginary parts) -/

section Complexify

variable {W' : ι → Type*} [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace ℝ (W' i)]
  [∀ i, CompleteSpace (W' i)] {H' : HilbertComplex ℝ c W'} {κ' : Type*}

/-- Over `ℝ`, the field `normedSpaceReal` need not be the normed space structure of the inner
product: the constructions below use the latter, the one of `Lₕ`, `ιₕ`, `πₕ`. -/
local instance (priority := high) instNormedSpaceRealOfInner (F : ApproxFEEC.{u} H' κ')
    (h : κ') : NormedSpace ℝ (F.X h) :=
  (F.innerProductSpace h).toNormedSpace

/-- The discrete generator `Lₕ ⊕ Lₕ` on `Xₕ ⊕₂ Xₕ`. -/
def complexifyL (F : ApproxFEEC.{u} H' κ') (h : κ') :
    WithLp 2 (F.X h × F.X h) →L[ℝ] WithLp 2 (F.X h × F.X h) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (F.X h) (F.X h)).symm.toContinuousLinearMap ∘L
    ((F.L h ∘L WithLp.fstL 2 ℝ (F.X h) (F.X h)).prod (F.L h ∘L WithLp.sndL 2 ℝ (F.X h) (F.X h)))

@[simp] theorem complexifyL_apply (F : ApproxFEEC.{u} H' κ') (h : κ') (a b : F.X h) :
    complexifyL F h (WithLp.toLp 2 (a, b)) = WithLp.toLp 2 (F.L h a, F.L h b) := rfl

/-- Run a real scheme on the real and imaginary parts: `X' = Xₕ ⊕₂ Xₕ`, `L' = Lₕ ⊕ Lₕ`,
`ι'(a, b) = ιₕ a + J ιₕ b`, `π' y = (πₕ y, -πₕ (J y))`, for an isometric complex structure `J`
(multiplication by `i`) with `πₕ J ιₕ = 0` and `ιₕ Xₕ ⊥ J ιₕ Xₕ` (real states and imaginary states
are orthogonal and not confused by `πₕ`). -/
def complexify (F : ApproxFEEC.{u} H' κ') (J : PiLp 2 W' →L[ℝ] PiLp 2 W')
    (hJJ : ∀ x, J (J x) = -x) (hJ : ∀ x, ‖J x‖ = ‖x‖)
    (hπJ : ∀ h b, F.proj h (J (F.incl h b)) = 0)
    (hJι : ∀ h a b, ⟪F.incl h a, J (F.incl h b)⟫_ℝ = 0) : ApproxFEEC.{u} H' κ' where
  K := F.K
  isClosed_K := F.isClosed_K
  l := F.l
  X h := WithLp 2 (F.X h × F.X h)
  normedAddCommGroup _ := inferInstance
  innerProductSpace _ := inferInstance
  completeSpace _ := inferInstance
  normedSpaceReal _ := inferInstance
  isScalarTower _ := IsScalarTower.left _
  L := complexifyL F
  skew h x y := by
    obtain ⟨⟨a, b⟩⟩ := x
    obtain ⟨⟨a', b'⟩⟩ := y
    simp only [complexifyL_apply, WithLp.prod_inner_apply, F.skew h]
    ring
  incl h := F.incl h ∘L WithLp.fstL 2 ℝ (F.X h) (F.X h) +
    J ∘L F.incl h ∘L WithLp.sndL 2 ℝ (F.X h) (F.X h)
  proj h := (WithLp.prodContinuousLinearEquiv 2 ℝ (F.X h) (F.X h)).symm.toContinuousLinearMap ∘L
    ((F.proj h).prod (-(F.proj h ∘L J)))
  proj_incl h x := by
    obtain ⟨⟨a, b⟩⟩ := x
    change WithLp.toLp 2 (F.proj h (F.incl h a + J (F.incl h b)),
      -F.proj h (J (F.incl h a + J (F.incl h b)))) = WithLp.toLp 2 (a, b)
    rw [_root_.map_add, _root_.map_add, _root_.map_add, F.proj_incl, hπJ, hJJ, _root_.map_neg,
      F.proj_incl, add_zero, hπJ, zero_add, neg_neg]
  bound := by
    refine ⟨2 * F.boundConst, fun h => ⟨?_, ?_⟩⟩
    · refine ContinuousLinearMap.opNorm_le_bound _ (by have := F.boundConst_nonneg; positivity)
        fun x => ?_
      obtain ⟨⟨a, b⟩⟩ := x
      simp only [ContinuousLinearMap.comp_apply, _root_.add_apply, WithLp.fstL_apply,
        WithLp.sndL_apply]
      have hn := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (a, b))
      have h1 := F.norm_incl_apply_le h a
      have h2 := F.norm_incl_apply_le h b
      have h0 := F.boundConst_nonneg
      have hsq : ‖F.incl h a + J (F.incl h b)‖ ^ 2 ≤
          (F.boundConst * ‖WithLp.toLp 2 (a, b)‖) ^ 2 := by
        rw [norm_add_sq_real, hJι, hJ, mul_pow, hn]
        simp only [WithLp.fst, WithLp.snd, mul_zero, add_zero]
        have := pow_le_pow_left₀ (norm_nonneg _) h1 2
        have := pow_le_pow_left₀ (norm_nonneg _) h2 2
        nlinarith
      change ‖F.incl h a + J (F.incl h b)‖ ≤ 2 * F.boundConst * ‖WithLp.toLp 2 (a, b)‖
      have hle := (pow_le_pow_iff_left₀ (norm_nonneg _)
        (mul_nonneg h0 (norm_nonneg (WithLp.toLp 2 (a, b)))) two_ne_zero).1 hsq
      have := mul_nonneg h0 (norm_nonneg (WithLp.toLp 2 (a, b)))
      linarith
    · refine ContinuousLinearMap.opNorm_le_bound _ (by have := F.boundConst_nonneg; positivity)
        fun y => ?_
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        _root_.neg_apply, ContinuousLinearEquiv.coe_coe,
        WithLp.prodContinuousLinearEquiv_symm_apply]
      have hn := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (F.proj h y, -F.proj h (J y)))
      simp only [WithLp.fst, WithLp.snd, norm_neg] at hn
      have h1 : ‖F.proj h y‖ ≤ F.boundConst * ‖y‖ := ((F.proj h).le_opNorm y).trans
        (mul_le_mul_of_nonneg_right (F.norm_proj_le h) (norm_nonneg _))
      have h2 : ‖F.proj h (J y)‖ ≤ F.boundConst * ‖y‖ := ((F.proj h).le_opNorm _).trans
        (by rw [hJ]; exact mul_le_mul_of_nonneg_right (F.norm_proj_le h) (norm_nonneg _))
      have h0 := F.boundConst_nonneg
      have := norm_nonneg (WithLp.toLp 2 (F.proj h y, -F.proj h (J y)))
      have := norm_nonneg (F.proj h y)
      have := norm_nonneg (F.proj h (J y))
      have := norm_nonneg y
      nlinarith

theorem complexify_incl (F : ApproxFEEC.{u} H' κ') (J : PiLp 2 W' →L[ℝ] PiLp 2 W') hJJ hJ hπJ
    hJι (h : κ') (a b : F.X h) :
    (F.complexify J hJJ hJ hπJ hJι).incl h (WithLp.toLp 2 (a, b)) =
      F.incl h a + J (F.incl h b) := rfl

/-- The complexified discrete solution is the real solution of the real part plus `J` times the
real solution of the imaginary part. -/
theorem complexify_sol (F : ApproxFEEC.{u} H' κ') (J : PiLp 2 W' →L[ℝ] PiLp 2 W') hJJ hJ hπJ
    hJι (h : κ') (a b : F.X h) (t : ℝ) :
    (F.complexify J hJJ hJ hπJ hJι).sol h (WithLp.toLp 2 (a, b)) t =
      F.sol h a t + J (F.sol h b t) := by
  set F' := F.complexify J hJJ hJ hπJ hJι
  set u : ℝ → F'.X h := fun s => WithLp.toLp 2 ((F.group h).S s a, (F.group h).S s b)
  have hu : ∀ s, HasDerivAt u (F'.L h (u s)) s := fun s => by
    have ha := C0Group.hasDerivAt_exp_ofReal_smul_apply (F.L h) a s
    have hb := C0Group.hasDerivAt_exp_ofReal_smul_apply (F.L h) b s
    have hp := ha.prodMk hb
    exact (WithLp.prodContinuousLinearEquiv 2 ℝ (F.X h) (F.X h)).symm.hasFDerivAt.comp_hasDerivAt
      s hp
  have e := eq_ofBounded_of_hasDerivAt (F'.L h) (F'.skew h) hu t
  have e0 : u 0 = WithLp.toLp 2 (a, b) := by
    change WithLp.toLp 2 ((F.group h).S 0 a, (F.group h).S 0 b) = _
    rw [C0Group.S_zero_apply, C0Group.S_zero_apply]
  rw [e0] at e
  change F'.incl h ((C0Group.ofBounded (F'.L h)).S t (WithLp.toLp 2 (a, b))) = _
  rw [← e]
  rfl

end Complexify

end ApproxFEEC

/-! ### The approximating FEEC theorem -/

section Main

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxFEEC.{u} H κ)

/-- **Weak solutions are unique**: for `x ∈ D(L)`, every weak solution of the Hodge wave equation
on `[0, T]` with initial value `x` is the orbit `t ↦ e^{tL} x`. [QuennevilleBelair2015], Thm 4.7 -/
theorem approxFEEC_unique_weak (x : H.wave.domain) (T : ℝ) (U : ℝ → PiLp 2 W)
    (hU0 : U 0 = (x : PiLp 2 W)) (hU : HodgeWave.IsWeakSolution H (Icc 0 T) 0 U) :
    EqOn U (fun t => F.S t x) (Icc 0 T) := fun t ht => by
  change U t = F.S t x
  rw [F.S_apply ht.1]
  exact (constrainedFEEC_wellPosed x.2 T).2.2.1 U hU0 hU ht

/-- **Forward propagation characterizes reducing constraints on graded complexes**: for a
grading `p` and an `R`-invariant `K` with `D(L) ∩ K` dense in `K`, `K` reduces `L` iff
`e^{tL} K ⊆ K` for every `t ≥ 0`. [QuennevilleBelair2015], Prop. 4.17 -/
theorem approxFEEC_isReducing_iff_keeps {p : ι → Bool} (hp : ∀ i j, c.Rel i j → p j ≠ p i)
    (hRK : ∀ x ∈ F.K, reversal 𝕜 p x ∈ F.K)
    (hD : (F.K : Set (PiLp 2 W)) ⊆ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K)) :
    H.wave.IsReducing F.K ↔ F.Keeps F.K := by
  refine ⟨fun h t ht x hx => ?_, fun h => (H.isReducing_iff_forall_nonneg hp F.K hRK
    fun k hk => hD hk).2 fun t ht x _ hx => ?_⟩
  · rw [F.S_apply ht]
    exact (skewFEEC_isReducing_iff_invariant F).1 h t x hx
  · have := h t ht x hx
    rwa [F.S_apply ht] at this

/-- The conclusions of the approximating FEEC theorem (`approxFEEC`) for `F` and the core `Z`:
those of the skew-adjoint FEEC theorem for the wave operator, and those specific to Hilbert
complexes. -/
structure ApproxFEEC.Verdict (Z : F.Core) : Prop extends toSkew : SkewFEEC.Verdict F Z where
  /-- for `x ∈ D(L)`, the orbit is the only weak solution of the Hodge wave equation on `[0, T]` -/
  unique_weak (x : H.wave.domain) (T : ℝ) (U : ℝ → PiLp 2 W) (hU0 : U 0 = (x : PiLp 2 W))
    (hU : HodgeWave.IsWeakSolution H (Icc 0 T) 0 U) : EqOn U (fun t => F.S t x) (Icc 0 T)
  /-- on a graded complex, for an `R`-invariant `K` with `D(L) ∩ K` dense in `K`: `K` reduces `L`
  iff `K` is kept (forward in time) -/
  isReducing_iff_keeps {p : ι → Bool} (hp : ∀ i j, c.Rel i j → p j ≠ p i)
    (hRK : ∀ x ∈ F.K, reversal 𝕜 p x ∈ F.K)
    (hD : (F.K : Set (PiLp 2 W)) ⊆ closure ((H.wave.domain : Set (PiLp 2 W)) ∩ F.K)) :
    H.wave.IsReducing F.K ↔ F.Keeps F.K

/-- **The approximating FEEC theorem.** For an approximating FEEC discretization `F` (discrete
Hilbert spaces with their own inner products, skew bounded generators, uniformly bounded reading
maps `ιₕ` with uniformly bounded left inverses `πₕ`; variational crimes allowed) and an
orbit-consistent core `Z`, the skew-adjoint FEEC theorem holds for the wave operator `L`
(`skewFEEC`, containing the dissipative FEEC theorem `dissipFEEC`): well-posedness and the energy
identity, conservation of the norm by `e^{tL}`, propagation iff reducing, convergence on the
closure of the core for every convergent family of discrete initial values, the rate
`(C + ‖ιₕ‖ C' t) hᵅ ‖ξ₀‖_c + ‖ιₕ‖ ‖pₕ(0) - v‖` (best approximation plus consistency), the
constraint residual through `ιₕ` and the departures from constraints that are not kept; and:

1. (**weak solutions**) for `ξ₀ ∈ D(L)`, `t ↦ e^{tL} ξ₀` is the only weak solution;
2. (**graded complexes**) for an `R`-invariant `K` with `D(L) ∩ K` dense in `K`, `K` reduces `L`
   iff it is kept forward in time.

Cf. [HolstStern2012], Thm 3.9, Thm 3.10 (elliptic analogues); [QuennevilleBelair2015], Thms 4.6,
4.7, Prop. 4.17 -/
theorem approxFEEC (Z : F.Core) : F.Verdict Z where
  toSkew := skewFEEC F Z
  unique_weak := approxFEEC_unique_weak F
  isReducing_iff_keeps := fun {_} hp hRK hD => approxFEEC_isReducing_iff_keeps F hp hRK hD

end Main

end Feec.HilbertComplex
