module

public import Feec.HilbertComplex.Approximation.ConstrainedFEEC
public import Feec.HilbertComplex.Approximation.Ritz
public import Feec.HilbertComplex.Approximation.SkewFEEC
public import Feec.Semigroup.DomainSq

/-!
# The approximating FEEC theorem

Approximating FEEC discretizations of the Hodge wave equation of a Hilbert complex: skew FEEC
discretizations of `L = 𝐝 - 𝐝†` on Hilbert spaces read through uniformly bounded maps, with cores
from the graph lift of `D(L²)`.

## Main results

* `approxFEEC`: the approximating FEEC theorem.
* `approxFEEC_unique_weak`: weak solutions of the Hodge wave equation are unique.
* `approxFEEC_isReducing_iff_keeps`: on graded complexes, forward propagation iff reducing.

## References

* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

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

theorem isCompact_waveOrbit {x : PiLp 2 W} (hx : x ∈ H.wave.domainSq) (T : ℝ) :
    IsCompact (waveOrbit H x '' Icc 0 T) ∧ IsCompact (waveOrbit H (waveExt H x) '' Icc 0 T) :=
  ⟨isCompact_Icc.image_of_continuousOn (waveOrbit_isC1' H hx T).1,
    isCompact_Icc.image_of_continuousOn (waveOrbit_isC1' H hx T).2.1⟩

theorem waveExt_waveGroup {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (t : ℝ) :
    waveExt H (H.waveGroup.S t x) = H.waveGroup.S t (waveExt H x) := by
  rw [waveExt_of_mem (waveGroup_mem_domain H hx t), waveExt_of_mem hx]
  exact wave_waveGroup hx t

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem waveExt_mem_domain {x : PiLp 2 W} (hx : x ∈ H.wave.domainSq) :
    waveExt H x ∈ H.wave.domain := by
  rw [waveExt_of_mem (domainSq_le_domain hx)]; exact (mem_domainSq.1 hx).2

theorem hasDerivAt_waveGroup_waveExt {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (t : ℝ) :
    HasDerivAt (fun s => H.waveGroup.S s x) (H.waveGroup.S t (waveExt H x)) t := by
  rw [waveExt_of_mem hx]; exact hasDerivAt_waveGroup H hx t

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem waveExt_eq_genExt : waveExt H = DissipFEEC.genExt H.wave := rfl

theorem waveGroup_mem_domainSq {x : PiLp 2 W} (hx : x ∈ H.wave.domainSq) (t : ℝ) :
    H.waveGroup.S t x ∈ H.wave.domainSq := by
  have hx1 := domainSq_le_domain hx
  refine mem_domainSq.2 ⟨waveGroup_mem_domain H hx1 t, ?_⟩
  rw [wave_waveGroup hx1 t]
  exact waveGroup_mem_domain H (mem_domainSq.1 hx).2 t

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
open scoped Classical in
/-- The graph-space lift `y ↦ (y, 𝐝 y)` of `y ∈ D(𝐝)` (`0` off `D(𝐝)`). -/
def graphOf (y : PiLp 2 W) : H.totalD.GraphSpace :=
  if hy : y ∈ H.totalD.domain then H.totalD.toGraphSpace ⟨y, hy⟩ else 0

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem graphOf_eq_waveLift {y : PiLp 2 W} (hy : y ∈ H.wave.domain) :
    graphOf H y = waveLift H ⟨y, hy⟩ := by
  have h : y ∈ H.totalD.domain := (H.mem_wave_domain.1 hy).1
  unfold graphOf; simp only [h, dite_true]; rfl

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem graphFst_graphOf {y : PiLp 2 W} (hy : y ∈ H.wave.domain) :
    H.totalD.graphFst (graphOf H y) = y := by
  rw [graphOf_eq_waveLift H hy, graphFst_waveLift]

theorem waveOrbit_eq_graphOf {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (t : ℝ) :
    waveOrbit H x t = graphOf H (H.waveGroup.S t x) := by
  rw [waveOrbit_of_mem H hx, graphOf_eq_waveLift]

theorem continuousOn_waveOrbit {x : PiLp 2 W} (hx : x ∈ H.wave.domainSq) :
    ContinuousOn (waveOrbit H x) (Ici 0) ∧ ContinuousOn (waveOrbit H (waveExt H x)) (Ici 0) := by
  have key : ∀ f : ℝ → H.totalD.GraphSpace, (∀ b : ℝ, 0 < b → ContinuousOn f (Icc 0 b)) →
      ContinuousOn f (Ici 0) := fun f hf t ht =>
    ((hf (t + 1) (by linarith [mem_Ici.1 ht])) t ⟨ht, by linarith⟩).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨Iio (t + 1), isOpen_Iio, by simp, fun s hs => ⟨hs.2, hs.1.le⟩⟩)
  exact ⟨key _ fun b hb => (waveOrbit_isC1 H hx hb).1,
    key _ fun b hb => (waveOrbit_isC1 H hx hb).2.1⟩

end Orbit

/-! ### Approximating FEEC discretizations -/

/-- An **approximating FEEC discretization**: a skew FEEC discretization of `L = 𝐝 - 𝐝†`. -/
abbrev ApproxFEEC (H : HilbertComplex 𝕜 c W) (κ : Type*) := SkewFEEC.{u} H.wave κ

namespace ApproxFEEC

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxFEEC.{u} H κ)

theorem U_eq_waveGroup (t : ℝ) : F.U t = H.waveGroup.S t := rfl

theorem S_eq_waveGroup {t : ℝ} (ht : 0 ≤ t) : F.S t = H.waveGroup.S t := F.S_eq_U ht

/-! ### The graph lift and the Trotter–Kato bridge -/

/-- The **graph lift**: data `D(L²)`, lifted into `Γ(𝐝)` by `y ↦ (y, 𝐝 y)`. -/
def graphLift : F.Lift H.totalD.GraphSpace where
  Data := H.wave.domainSq
  le_domain := domainSq_le_domain
  S_mem x hx t ht := by rw [F.S_eq_waveGroup ht]; exact waveGroup_mem_domainSq H hx t
  lift := graphOf H
  read := H.totalD.graphFst
  read_lift y hy := graphFst_graphOf H (domainSq_le_domain hy)
  continuousOn x hx := (continuousOn_waveOrbit H hx).1.congr fun t ht => by
    rw [F.S_eq_waveGroup ht, waveOrbit_eq_graphOf H (domainSq_le_domain hx)]
  continuousOn' x hx := (continuousOn_waveOrbit H hx).2.congr fun t ht => by
    rw [F.S_eq_waveGroup ht, ← waveExt_eq_genExt, waveOrbit_eq_graphOf H (waveExt_mem_domain H hx)]
  hasDerivWithinAt x hx t ht := by
    have e : ∀ s, 0 ≤ s → graphOf H (F.S s x) = waveOrbit H x s := fun s hs => by
      rw [F.S_eq_waveGroup hs, waveOrbit_eq_graphOf H (domainSq_le_domain hx)]
    rw [F.S_eq_waveGroup ht, ← waveExt_eq_genExt,
      ← waveOrbit_eq_graphOf H (waveExt_mem_domain H hx)]
    exact ((waveOrbit_isC1' H hx (t + 1)).2.2 t ⟨ht, by linarith⟩).congr
      (fun s hs => e s (ht.trans hs)) (e t ht)

/-- The **Ritz projection of the graph lift** of `Rₕ : Γ(𝐝) → Xₕ` with a defect identity. -/
def graphRitz (R Δ Δ' : ∀ h, H.totalD.GraphSpace →L[𝕜] F.X h) (hR : ∃ C, ∀ h, ‖R h‖ ≤ C)
    (hΔ : ∃ C, ∀ h, ‖Δ h‖ ≤ C ∧ ‖Δ' h‖ ≤ C)
    (hdef : ∀ h (y : H.wave.domain) (hLy : H.wave y ∈ H.wave.domain),
      R h (waveLift H ⟨_, hLy⟩) - F.L h (R h (waveLift H y)) =
        Δ h (waveLift H ⟨_, hLy⟩) + Δ' h (waveLift H y)) : F.Ritz (graphLift F) where
  R := R
  Δ := Δ
  Δ' := Δ'
  defect_eq h y hy := by
    have hy1 := domainSq_le_domain hy
    have hLy := waveExt_mem_domain H hy
    change R h (graphOf H (DissipFEEC.genExt H.wave y)) - F.L h (R h (graphOf H y)) =
      Δ h (graphOf H (DissipFEEC.genExt H.wave y)) + Δ' h (graphOf H y)
    rw [← waveExt_eq_genExt, graphOf_eq_waveLift H hy1, graphOf_eq_waveLift H hLy]
    have e : (⟨waveExt H y, hLy⟩ : H.wave.domain) =
        ⟨H.wave ⟨y, hy1⟩, by rw [← waveExt_of_mem hy1]; exact hLy⟩ :=
      Subtype.ext (waveExt_of_mem hy1)
    rw [e]
    exact hdef h ⟨y, hy1⟩ _
  bound :=
    let ⟨C₁, h₁⟩ := hR
    let ⟨C₂, h₂⟩ := hΔ
    ⟨max C₁ C₂, fun h => ⟨(h₁ h).trans (le_max_left _ _), (h₂ h).1.trans (le_max_right _ _),
      (h₂ h).2.trans (le_max_right _ _)⟩⟩

/-- Comparison trajectories `pₕ(t) = Rₕ (e^{tL} x, 𝐝 e^{tL} x)` of `Rₕ : Γ(𝐝) → Xₕ` on `D(L²)`. -/
def Comparison.ofOperator (R : ∀ h, H.totalD.GraphSpace →L[𝕜] F.X h) (T : ℝ) :
    F.Comparison T :=
  (graphLift F).cmp R T

theorem Comparison.ofOperator_p (R : ∀ h, H.totalD.GraphSpace →L[𝕜] F.X h) (T : ℝ)
    {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (h : κ) {t : ℝ} (ht : 0 ≤ t) :
    (Comparison.ofOperator F R T).p x h t = R h (waveOrbit H x t) := by
  change R h (graphOf H (F.S t x)) = _
  rw [F.S_eq_waveGroup ht, waveOrbit_eq_graphOf H hx]

theorem Comparison.ofOperator_p' (R : ∀ h, H.totalD.GraphSpace →L[𝕜] F.X h) (T : ℝ)
    {x : PiLp 2 W} (hx : x ∈ H.wave.domainSq) (h : κ) {t : ℝ} (ht : 0 ≤ t) :
    (Comparison.ofOperator F R T).p' x h t = R h (waveOrbit H (waveExt H x) t) := by
  change R h (graphOf H (F.S t (DissipFEEC.genExt H.wave x))) = _
  rw [F.S_eq_waveGroup ht, ← waveExt_eq_genExt, waveOrbit_eq_graphOf H (waveExt_mem_domain H hx)]

/-- **The Trotter–Kato bridge**: the core `D(L²)` of `Rₕ : Γ(𝐝) → Xₕ` ([Pazy1983], §3.4). -/
def Core.ofOperator (R : ∀ h, H.totalD.GraphSpace →L[𝕜] F.X h)
    (hR : ∃ C, ∀ h, ‖R h‖ ≤ C)
    (happrox : ∀ ζ, Tendsto (fun h => F.incl h (R h ζ)) F.l (𝓝 (H.totalD.graphFst ζ)))
    (Δ Δ' : ∀ h, H.totalD.GraphSpace →L[𝕜] F.X h) (hΔ : ∃ C, ∀ h, ‖Δ h‖ ≤ C ∧ ‖Δ' h‖ ≤ C)
    (hdef : ∀ h (y : H.wave.domain) (hLy : H.wave y ∈ H.wave.domain),
      R h (waveLift H ⟨_, hLy⟩) - F.L h (R h (waveLift H y)) =
        Δ h (waveLift H ⟨_, hLy⟩) + Δ' h (waveLift H y))
    (hΔ0 : ∀ ζ, Tendsto (fun h => ‖Δ h ζ‖) F.l (𝓝 0))
    (hΔ'0 : ∀ ζ, Tendsto (fun h => ‖Δ' h ζ‖) F.l (𝓝 0)) : F.Core :=
  (graphRitz F R Δ Δ' hR hΔ hdef).toCore happrox hΔ0 hΔ'0

@[simp] theorem Core.ofOperator_data (R hR happrox Δ Δ' hΔ hdef hΔ0 hΔ'0) :
    (Core.ofOperator F R hR happrox Δ Δ' hΔ hdef hΔ0 hΔ'0).Data = H.wave.domainSq :=
  rfl

theorem Core.ofOperator_cmp (R hR happrox Δ Δ' hΔ hdef hΔ0 hΔ'0) (T : ℝ) :
    (Core.ofOperator F R hR happrox Δ Δ' hΔ hdef hΔ0 hΔ'0).cmp T = Comparison.ofOperator F R T :=
  rfl

/-! ### Complexification -/

section Complexify

variable {W' : ι → Type*} [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace ℝ (W' i)]
  [∀ i, CompleteSpace (W' i)] {H' : HilbertComplex ℝ c W'} {κ' : Type*}

/-- The real normed space structure of `Xₕ` given by its inner product. -/
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

/-- A real scheme run on real and imaginary parts, `ι'(a, b) = ιₕ a + J ιₕ b`. -/
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
  isSkewAdjoint := F.isSkewAdjoint
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

theorem complexify_sol (F : ApproxFEEC.{u} H' κ') (J : PiLp 2 W' →L[ℝ] PiLp 2 W') hJJ hJ hπJ
    hJι (h : κ') (a b : F.X h) (t : ℝ) :
    (F.complexify J hJJ hJ hπJ hJι).sol h (WithLp.toLp 2 (a, b)) t =
      F.sol h a t + J (F.sol h b t) := by
  set F' := F.complexify J hJJ hJ hπJ hJι
  set u : ℝ → F'.X h := fun s => WithLp.toLp 2 ((F.group h).S s a, (F.group h).S s b)
  have hu : ∀ s, HasDerivAt u (F'.L h (u s)) s := fun s => by
    have ha := ContinuousLinearMap.hasDerivAt_exp_ofReal_smul_apply (F.L h) a s
    have hb := ContinuousLinearMap.hasDerivAt_exp_ofReal_smul_apply (F.L h) b s
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

/-- **Weak solutions are unique**: for `x ∈ D(L)`, every weak solution from `x` is `e^{tL} x`
([QuennevilleBelair2015], Thm 4.7). -/
theorem approxFEEC_unique_weak (x : H.wave.domain) (T : ℝ) (U : ℝ → PiLp 2 W)
    (hU0 : U 0 = (x : PiLp 2 W)) (hU : HodgeWave.IsWeakSolution H (Icc 0 T) 0 U) :
    EqOn U (fun t => F.S t x) (Icc 0 T) := fun t ht => by
  change U t = F.S t x
  rw [F.S_eq_waveGroup ht.1]
  exact (constrainedFEEC_wellPosed x.2 T).2.2.1 U hU0 hU ht

/-- `p` alternates along `c`: `p j ≠ p i` whenever `c.Rel i j`. -/
abbrev Alternates (c : ComplexShape ι) (p : ι → Bool) : Prop := ∀ i j, c.Rel i j → p j ≠ p i

/-- The constraint of `F` is invariant under the reversal by `p`. -/
abbrev ApproxFEEC.ReversalInvariant (p : ι → Bool) : Prop := ∀ x ∈ F.K, reversal 𝕜 p x ∈ F.K

/-- **Forward propagation characterizes reducing constraints on graded complexes**, for
reversal-invariant `K` with `D(L) ∩ K` dense in `K` ([QuennevilleBelair2015], Prop 4.17). -/
theorem approxFEEC_isReducing_iff_keeps {p : ι → Bool} (hp : Alternates c p)
    (hRK : F.ReversalInvariant p) (hD : F.SmoothDense F.K) :
    H.wave.IsReducing F.K ↔ F.Keeps F.K :=
  ⟨fun h => (F.isMDissipative.isReducing_iff.1 h).1, fun h =>
    (H.isReducing_iff_forall_nonneg hp F.K hRK hD).2 fun t ht x _ hx => by
      rw [← F.S_eq_waveGroup ht]; exact h t ht x hx⟩

/-- The conclusions of the approximating FEEC theorem for `F` and the core `Z`. -/
structure ApproxFEEC.Verdict (Z : F.Core) : Prop extends toSkew : SkewFEEC.Verdict F Z where
  /-- weak solutions are unique -/
  unique_weak (x : H.wave.domain) (T : ℝ) (U : ℝ → PiLp 2 W) (hU0 : U 0 = (x : PiLp 2 W))
    (hU : HodgeWave.IsWeakSolution H (Icc 0 T) 0 U) : EqOn U (fun t => F.S t x) (Icc 0 T)
  /-- on graded complexes, forward propagation iff reducing -/
  isReducing_iff_keeps {p : ι → Bool} (hp : Alternates c p) (hRK : F.ReversalInvariant p)
    (hD : F.SmoothDense F.K) : H.wave.IsReducing F.K ↔ F.Keeps F.K

/-- **The approximating FEEC theorem**: a discretization with an orbit-consistent core satisfies
`ApproxFEEC.Verdict` (cf. [QuennevilleBelair2015], Thms 4.6, 4.7). -/
theorem approxFEEC (Z : F.Core) : F.Verdict Z where
  toSkew := skewFEEC F Z
  unique_weak := approxFEEC_unique_weak F
  isReducing_iff_keeps := fun {_} hp hRK hD => approxFEEC_isReducing_iff_keeps F hp hRK hD

end Main

end Feec.HilbertComplex
