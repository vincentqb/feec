module

public import Feec.HilbertComplex.Approximation.ApproxFEEC

/-!
# Conforming special cases of the approximating FEEC theorem

Two families of discretizations without variational crimes are approximating FEEC
discretizations (`Feec.HilbertComplex.ApproxFEEC`), with `ιₕ` the inclusion of a subspace of `W`:

* **Constrained FEEC discretizations** (`Feec.HilbertComplex.ConstrainedFEEC`, finite-dimensional
  subcomplexes approximating in the graph norm): `ConstrainedFEEC.toApprox` has
  `Xₕ = ∏ Vₕⁱ ⊆ W` with the `W` inner product, the discrete wave operator `Lₕ` of (4.10)
  (`ConstrainedFEEC.discreteWave`, `⟪Lₕ x, ψ⟫ = ⟪𝐝 x, ψ⟫ - ⟪x, 𝐝 ψ⟫`), `ιₕ` the inclusion and
  `πₕ = Qₕ` the orthogonal projection onto `Xₕ`. Its **wave Ritz projection**
  (`ConstrainedFEEC.waveRitz`, a `DissipFEEC.Ritz` of the graph lift `ApproxFEEC.graphLift`) is
  the elliptic projection (4.11),
  with the defect identity `Rₕ (L y) - Lₕ Rₕ y = Qₕ (Pₕ - 1)(L y) - Qₕ (Pₕ - 1) y` (`Qₕ` the
  orthogonal projection onto `Xₕ`; `ConstrainedFEEC.ellipticProj_defect`). Its core
  `ConstrainedFEEC.toCore` (data `D(L²)`, dense) is the core of the wave Ritz projection, and the
  conforming rate classes are its rate classes (`ConstrainedFEEC.RateClass.toApprox`, through the
  static estimates of the elliptic projection along the orbit; for degreewise regular data along
  the trajectory, `ConstrainedFEEC.RateClass.ofDegreewise`, and for the classes of a Jackson
  estimate, `ConstrainedFEEC.RateClass.ofJackson`). The discrete solutions are those of
  (4.10) (`ConstrainedFEEC.toApprox_sol`, `ConstrainedFEEC.exists_eq_sol`), which gives the
  improved rate `(1 + C_P)(1 + 2t) C hᵅ ‖ξ₀‖_class` (`ConstrainedFEEC.rate_le`) and the rate
  `(1 + C_P)(1 + t)²` of `constrainedFEEC_rate` (`1 + 2t ≤ (1 + t)²`). **The constrained FEEC
  theorem** `constrainedFEEC` (`ConstrainedFEEC.Verdict`) is proved here from the verdict of
  `approxFEEC` for `toApprox`: it is the special case `ιₕ` = inclusion, `πₕ = Qₕ`. The consistency
  defect of this special case is in general not zero: by `ConstrainedFEEC.ellipticProj_defect` it
  is `Δₕ(L y) - Δₕ(y)` along the orbit, which tends to `0` (the conforming discretization commits
  no variational crime, but `Rₕ` does not commute with `L`). Non-vacuity:
  `constrainedFEEC_nonvacuous`.
* **Reducing families** (`Feec.HilbertComplex.ReducingFamily`, in
  `Feec.HilbertComplex.Approximation.Spectral`): closed reducing subspaces `B_N ⊆ D(L)` on which
  `L` is bounded, with projections converging strongly to `1` (spectral Galerkin methods).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.4 (Thms 4.6, 4.7), §4.6 ((4.10), (4.11), Prop. 4.13, Thm 4.14), §4.10 (Prop. 4.17),
  §4.12–4.13
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3 (Thm 3.4)
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 5

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap Metric

@[expose] public noncomputable section

namespace Feec.HilbertComplex

open _root_.Feec.HodgeWave

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

/-- **The weak form of the wave operator**: `⟪L y, ψ⟫ = ⟪𝐝 y, ψ⟫ - ⟪y, 𝐝 ψ⟫` for `y ∈ D(L)`,
`ψ ∈ D(𝐝)`. -/
theorem inner_wave_left (H : HilbertComplex 𝕜 c W) (y : H.wave.domain) (ψ : H.totalD.domain) :
    ⟪H.wave y, (ψ : PiLp 2 W)⟫_𝕜 =
      ⟪H.totalD ⟨y, (H.mem_wave_domain.1 y.2).1⟩, (ψ : PiLp 2 W)⟫_𝕜 -
        ⟪(y : PiLp 2 W), H.totalD ψ⟫_𝕜 := by
  have h₀ := mem_domain_sub_adjoint H y.2
  have e : H.wave y = H.totalD ⟨y, h₀.1⟩ - H.totalD† ⟨y, h₀.2⟩ := by
    rw [LinearPMap.apply_eq_of_eq H.wave_eq y ⟨y, h₀⟩ rfl]; rfl
  have h2 : (y : PiLp 2 W) ∈ H.totalD†.domain := h₀.2
  have hf : ⟪H.totalD† ⟨y, h2⟩, (ψ : PiLp 2 W)⟫_𝕜 = ⟪(y : PiLp 2 W), H.totalD ψ⟫_𝕜 :=
    adjoint_isFormalAdjoint H.dense_totalD_domain ⟨y, h2⟩ ψ
  rw [e, inner_sub_left, hf]

/-! ### Constrained FEEC discretizations are approximating -/

namespace ConstrainedFEEC

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ConstrainedFEEC H κ)

/-- The discrete space `Xₕ = ∏ Vₕⁱ ⊆ W` with the `W` inner product. -/
abbrev Xh (h : κ) : Type _ := ↥(totalSub (F.V h).V)

instance (h : κ) : FiniteDimensional 𝕜 (F.Xh h) := by
  let f : F.Xh h →ₗ[𝕜] ∀ i, (F.V h).V i :=
    { toFun := fun v i => ⟨(v : PiLp 2 W) i, v.2 i⟩
      map_add' := fun v w => funext fun i => Subtype.ext (by simp)
      map_smul' := fun a v => funext fun i => Subtype.ext (by simp) }
  refine Module.Finite.of_injective f fun v w hvw => Subtype.ext (PiLp.ext fun i => ?_)
  exact congrArg Subtype.val (congrFun hvw i)

theorem Xh_mem_domain (h : κ) (x : F.Xh h) : (x : PiLp 2 W) ∈ H.totalD.domain :=
  fun i j => (F.V h).le_domain i j (x.2 i)

/-- The lift `x ↦ (x, 𝐝 x)` of `Xₕ` into the graph space (onto `Vₕ` there). -/
def liftXh (h : κ) : F.Xh h →L[𝕜] H.totalD.GraphSpace :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => H.totalD.toGraphSpace ⟨x, F.Xh_mem_domain h x⟩
      map_add' := fun x y => H.totalD.graphFst_injective (by rw [_root_.map_add]; rfl)
      map_smul' := fun a x => H.totalD.graphFst_injective (by rw [_root_.map_smul]; rfl) }

@[simp] theorem graphFst_liftXh (h : κ) (x : F.Xh h) :
    H.totalD.graphFst (F.liftXh h x) = x := rfl

theorem graphSnd_liftXh (h : κ) (x : F.Xh h) :
    H.totalD.graphSnd (F.liftXh h x) = H.totalD ⟨x, F.Xh_mem_domain h x⟩ := rfl

theorem liftXh_mem (h : κ) (x : F.Xh h) : F.liftXh h x ∈ F.Kh h := fun i => x.2 i

theorem liftXh_graphFst (h : κ) {v : H.totalD.GraphSpace} (hv : v ∈ F.Kh h) :
    F.liftXh h ⟨H.totalD.graphFst v, hv⟩ = v := H.totalD.graphFst_injective rfl

theorem liftXh_injective (h : κ) : Function.Injective (F.liftXh h) := fun x y hxy =>
  Subtype.ext (by rw [← F.graphFst_liftXh h x, ← F.graphFst_liftXh h y, hxy])

/-- The discrete differential `𝐝ₕ : Xₕ → Xₕ` (the restriction of `𝐝`). -/
def discreteD (h : κ) : F.Xh h →L[𝕜] F.Xh h :=
  LinearMap.toContinuousLinearMap (LinearMap.codRestrict (totalSub (F.V h).V)
    ((H.totalD.graphSnd ∘L F.liftXh h : F.Xh h →L[𝕜] PiLp 2 W) : F.Xh h →ₗ[𝕜] PiLp 2 W)
    fun x => by
      have := (F.V h).graphD_mem_graphSub (F.liftXh_mem h x)
      exact this)

theorem coe_discreteD (h : κ) (x : F.Xh h) :
    (F.discreteD h x : PiLp 2 W) = H.totalD ⟨x, F.Xh_mem_domain h x⟩ := rfl

/-- The discrete wave operator: `⟪Lₕ x, ψ⟫ = ⟪𝐝 x, ψ⟫ - ⟪x, 𝐝 ψ⟫` on `Xₕ`
([QuennevilleBelair2015], (4.10)). -/
def discreteWave (h : κ) : F.Xh h →L[𝕜] F.Xh h := F.discreteD h - (F.discreteD h).adjoint

theorem inner_discreteWave (h : κ) (x y : F.Xh h) :
    ⟪F.discreteWave h x, y⟫_𝕜 =
      ⟪H.totalD ⟨x, F.Xh_mem_domain h x⟩, (y : PiLp 2 W)⟫_𝕜 -
        ⟪(x : PiLp 2 W), H.totalD ⟨y, F.Xh_mem_domain h y⟩⟫_𝕜 := by
  rw [discreteWave, _root_.sub_apply, inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
    Submodule.coe_inner, Submodule.coe_inner, coe_discreteD, coe_discreteD]

theorem discreteWave_skew (h : κ) (x y : F.Xh h) :
    ⟪F.discreteWave h x, y⟫_𝕜 = -⟪x, F.discreteWave h y⟫_𝕜 := by
  rw [discreteWave, _root_.sub_apply, _root_.sub_apply, inner_sub_left, inner_sub_right,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  ring

/-- `Pₕ` (the elliptic projection (4.11)) read in `Xₕ`. -/
def ellipticProj (h : κ) : H.totalD.GraphSpace →L[𝕜] F.Xh h :=
  (H.totalD.graphFst ∘L ellipticProjection (F.Kh h)).codRestrict (totalSub (F.V h).V)
    fun ζ => ellipticProjection_mem (F.Kh h) ζ

theorem coe_ellipticProj (h : κ) (ζ : H.totalD.GraphSpace) :
    (F.ellipticProj h ζ : PiLp 2 W) = H.totalD.graphFst (ellipticProjection (F.Kh h) ζ) := rfl

theorem liftXh_ellipticProj (h : κ) (ζ : H.totalD.GraphSpace) :
    F.liftXh h (F.ellipticProj h ζ) = ellipticProjection (F.Kh h) ζ :=
  F.liftXh_graphFst h (ellipticProjection_mem (F.Kh h) ζ)

theorem norm_ellipticProj_le (h : κ) : ‖F.ellipticProj h‖ ≤ ellipticConst H :=
  ContinuousLinearMap.opNorm_le_bound _ (ellipticConst_nonneg H) fun ζ =>
    (norm_graphFst_le _).trans ((F.V h).norm_ellipticProjection_le ζ)

/-- The orthogonal projection `Qₕ : W → Xₕ`. -/
abbrev orthProj (h : κ) : PiLp 2 W →L[𝕜] F.Xh h := (totalSub (F.V h).V).orthogonalProjectionOnto

/-- The defect operator `Δₕ = Qₕ graphFst (Pₕ - 1)`. -/
def ellipticDefect (h : κ) : H.totalD.GraphSpace →L[𝕜] F.Xh h :=
  F.orthProj h ∘L H.totalD.graphFst ∘L (ellipticProjection (F.Kh h) - 1)

theorem norm_ellipticDefect_apply_le (h : κ) (ζ : H.totalD.GraphSpace) :
    ‖F.ellipticDefect h ζ‖ ≤ ‖ellipticProjection (F.Kh h) ζ - ζ‖ := by
  have e : F.ellipticDefect h ζ =
      F.orthProj h (H.totalD.graphFst (ellipticProjection (F.Kh h) ζ - ζ)) := rfl
  rw [e]
  exact ((totalSub (F.V h).V).norm_orthogonalProjectionOnto_apply_le _).trans
    (norm_graphFst_le _)

theorem norm_ellipticDefect_le (h : κ) : ‖F.ellipticDefect h‖ ≤ ellipticConst H + 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by have := ellipticConst_nonneg H; positivity)
    fun ζ => (F.norm_ellipticDefect_apply_le h ζ).trans (by
      have : ‖ellipticProjection (F.Kh h) ζ‖ ≤ ellipticConst H * ‖ζ‖ :=
        (F.V h).norm_ellipticProjection_le ζ
      have := norm_sub_le (ellipticProjection (F.Kh h) ζ) ζ
      nlinarith [norm_nonneg ζ])

theorem ellipticDefect_apply (h : κ) (ζ : H.totalD.GraphSpace) :
    F.ellipticDefect h ζ = F.ellipticProj h ζ - F.orthProj h (H.totalD.graphFst ζ) := by
  have e : F.ellipticDefect h ζ =
      F.orthProj h (H.totalD.graphFst (ellipticProjection (F.Kh h) ζ - ζ)) := rfl
  rw [e, H.totalD.graphFst.map_sub, (F.orthProj h).map_sub]
  congr 1
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (F.ellipticProj h ζ)

/-- **The elliptic projection and the discrete wave operator**: for `y ∈ D(L)`,
`Lₕ Rₕ y = Rₕ y - Qₕ y + Qₕ L y` (Galerkin orthogonality of the shifted form). -/
theorem discreteWave_ellipticProj (h : κ) (y : H.wave.domain) :
    F.discreteWave h (F.ellipticProj h (waveLift H y)) =
      F.ellipticProj h (waveLift H y) - F.orthProj h y + F.orthProj h (H.wave y) := by
  refine ext_inner_right 𝕜 fun ψ => ?_
  set ζ := waveLift H y
  set r := F.ellipticProj h ζ
  have hG := shiftedForm_ellipticProjection_sub (F.Kh h) ζ (F.liftXh_mem h ψ)
  rw [shiftedForm_apply, waveForm_apply, ← F.liftXh_ellipticProj h ζ] at hG
  simp only [H.totalD.graphFst.map_sub, H.totalD.graphSnd.map_sub, graphFst_liftXh,
    graphSnd_liftXh] at hG
  have hζ1 : H.totalD.graphFst ζ = y := rfl
  have hζ2 : H.totalD.graphSnd ζ = H.totalD ⟨y, (H.mem_wave_domain.1 y.2).1⟩ := rfl
  rw [hζ1, hζ2] at hG
  have hw : ⟪H.wave y, (ψ : PiLp 2 W)⟫_𝕜 =
      ⟪H.totalD ⟨y, (H.mem_wave_domain.1 y.2).1⟩, (ψ : PiLp 2 W)⟫_𝕜 -
        ⟪(y : PiLp 2 W), H.totalD ⟨ψ, F.Xh_mem_domain h ψ⟩⟫_𝕜 :=
    inner_wave_left H y ⟨ψ, F.Xh_mem_domain h ψ⟩
  rw [F.inner_discreteWave h r ψ, inner_add_left, inner_sub_left,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right, Submodule.coe_inner, hw]
  have hc := congrArg (starRingEnd 𝕜) hG
  simp only [_root_.map_add, _root_.map_sub, inner_conj_symm, _root_.map_zero,
    inner_sub_right] at hc
  linear_combination -hc

/-- **The defect identity** of the elliptic projection:
`Rₕ (L y) - Lₕ Rₕ y = Δₕ (L y) - Δₕ y`, `Δₕ = Qₕ graphFst (Pₕ - 1)`. -/
theorem ellipticProj_defect (h : κ) (y : H.wave.domain) (hLy : H.wave y ∈ H.wave.domain) :
    F.ellipticProj h (waveLift H ⟨_, hLy⟩) - F.discreteWave h (F.ellipticProj h (waveLift H y)) =
      F.ellipticDefect h (waveLift H ⟨_, hLy⟩) + (-F.ellipticDefect h) (waveLift H y) := by
  rw [F.discreteWave_ellipticProj h y, _root_.neg_apply, F.ellipticDefect_apply,
    F.ellipticDefect_apply, graphFst_waveLift, graphFst_waveLift]
  abel

/-- **The static estimates of the elliptic projection**: for every `w ∈ Kₕ`,
`‖graphFst ζ - Pₕ ζ‖ ≤ (1 + C_P) ‖ζ - w‖` (quasi-optimality, `norm_sub_ellipticProjection_le`). -/
theorem norm_graphFst_sub_ellipticProj_le (h : κ) (ζ : H.totalD.GraphSpace)
    {w : H.totalD.GraphSpace} (hw : w ∈ F.Kh h) :
    ‖H.totalD.graphFst ζ - (F.ellipticProj h ζ : PiLp 2 W)‖ ≤ (1 + ellipticConst H) * ‖ζ - w‖ := by
  rw [coe_ellipticProj, ← H.totalD.graphFst.map_sub]
  exact (norm_graphFst_le _).trans (F.norm_sub_ellipticProjection_le h ζ hw)

/-- The defect `Δₕ ζ` is at most `(1 + C_P) ‖ζ - w‖` for every `w ∈ Kₕ`. -/
theorem norm_ellipticDefect_le_of_mem (h : κ) (ζ : H.totalD.GraphSpace)
    {w : H.totalD.GraphSpace} (hw : w ∈ F.Kh h) :
    ‖F.ellipticDefect h ζ‖ ≤ (1 + ellipticConst H) * ‖ζ - w‖ :=
  (F.norm_ellipticDefect_apply_le h ζ).trans (by
    rw [norm_sub_rev]; exact F.norm_sub_ellipticProjection_le h ζ hw)

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- **Every constrained FEEC discretization is an approximating one**: `Xₕ = ∏ Vₕⁱ`, `ιₕ` the
inclusion, `πₕ = Qₕ` the orthogonal projection onto `Xₕ`, `Lₕ` the discrete wave operator of
(4.10). -/
def toApprox : ApproxFEEC H κ where
  K := F.K
  isClosed_K := F.isClosed_K
  l := F.l
  X := F.Xh
  L := F.discreteWave
  isSkewAdjoint := H.isSkewAdjoint_wave
  skew := F.discreteWave_skew
  incl h := (totalSub (F.V h).V).subtypeL
  proj := F.orthProj
  proj_incl h x := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x
  bound := ⟨1, fun h =>
    ⟨ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [one_mul]; exact le_rfl,
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
        rw [one_mul]; exact (totalSub (F.V h).V).norm_orthogonalProjectionOnto_apply_le x⟩⟩

theorem norm_toApprox_incl_le (h : κ) : ‖F.toApprox.incl h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [one_mul]; exact le_rfl

/-- **The wave Ritz projection**: the elliptic projection `Rₕ = Pₕ` (4.11) on the graph lift
(`ApproxFEEC.graphRitz`), with the defect identity `ellipticProj_defect`:
`Δₕ = Qₕ graphFst (Pₕ - 1)`, `Δₕ' = -Δₕ`. [QuennevilleBelair2015], (4.11) -/
def waveRitz : DissipFEEC.Ritz (ApproxFEEC.graphLift F.toApprox) :=
  ApproxFEEC.graphRitz F.toApprox F.ellipticProj F.ellipticDefect (fun h => -F.ellipticDefect h)
    ⟨_, F.norm_ellipticProj_le⟩
    ⟨_, fun h => ⟨F.norm_ellipticDefect_le h,
      (norm_neg (F.ellipticDefect h)).trans_le (F.norm_ellipticDefect_le h)⟩⟩
    F.ellipticProj_defect

/-- Its core: the core of the wave Ritz projection (`DissipFEEC.Ritz.toCore`), data `D(L²)`;
`ιₕ Pₕ ζ → graphFst ζ` and `Δₕ ζ → 0` by the approximation property. -/
def toCore : F.toApprox.Core :=
  F.waveRitz.toCore
    (fun ζ => H.totalD.graphFst.continuous.continuousAt.tendsto.comp
      ((F.isApproximating.tendstoUniformlyOn_ellipticProjection isCompact_singleton).tendsto_at
        (mem_singleton ζ)))
    (fun ζ => squeeze_zero (fun _ => norm_nonneg _) (fun h => F.norm_ellipticDefect_apply_le h ζ)
      (by
        have := (F.isApproximating.tendstoUniformlyOn_ellipticProjection
          isCompact_singleton).tendsto_at (mem_singleton ζ)
        exact tendsto_iff_norm_sub_tendsto_zero.1 this))
    (fun ζ => squeeze_zero (fun _ => norm_nonneg _)
      (fun h => (norm_neg (F.ellipticDefect h ζ)).trans_le (F.norm_ellipticDefect_apply_le h ζ))
      (by
        have := (F.isApproximating.tendstoUniformlyOn_ellipticProjection
          isCompact_singleton).tendsto_at (mem_singleton ζ)
        exact tendsto_iff_norm_sub_tendsto_zero.1 this))

theorem dense_toCore_data : Dense (F.toCore.Data : Set (PiLp 2 W)) :=
  H.isSkewAdjoint_wave.dense_domainSq

theorem mem_toCore_closure (x : PiLp 2 W) : x ∈ F.toCore.Data.topologicalClosure := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, F.dense_toCore_data.closure_eq]
  trivial

/-- The discrete group `e^{t Lₕ}` on `Xₕ`. -/
abbrev discreteGroup (h : κ) : C0Group 𝕜 (F.Xh h) := C0Group.ofBounded (F.discreteWave h)

theorem toApprox_sol_eq (h : κ) (v : F.Xh h) (t : ℝ) :
    F.toApprox.sol h v t = ((F.discreteGroup h).S t v : PiLp 2 W) := rfl

/-- **The `Xₕ`-orbits are semi-discrete solutions** of (4.10): `s ↦ (e^{(s-a) Lₕ} w, 𝐝 ·)`. -/
theorem isSemidiscreteSolution_orbit (h : κ) (w : F.Xh h) (a : ℝ) (I : Set ℝ) :
    IsSemidiscreteSolution (F.Kh h) I (fun s => F.liftXh h ((F.discreteGroup h).S (s - a) w))
      (fun s => F.liftXh h (F.discreteWave h ((F.discreteGroup h).S (s - a) w))) := by
  refine ⟨fun s _ => F.liftXh_mem h _, fun s _ => ?_, fun s _ ψ hψ => ?_⟩
  · have hd := (ContinuousLinearMap.hasDerivAt_exp_ofReal_smul_apply (F.discreteWave h) w
      (s - a)).comp_sub_const s a
    exact (((F.liftXh h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hd).hasDerivWithinAt
  · set z := (F.discreteGroup h).S (s - a) w
    set p : F.Xh h := ⟨H.totalD.graphFst ψ, hψ⟩
    rw [← F.liftXh_graphFst h hψ, waveForm_apply]
    change ⟪(p : PiLp 2 W), (F.discreteWave h z : PiLp 2 W)⟫_𝕜 +
      (⟪H.totalD ⟨p, F.Xh_mem_domain h p⟩, (z : PiLp 2 W)⟫_𝕜 -
        ⟪(p : PiLp 2 W), H.totalD ⟨z, F.Xh_mem_domain h z⟩⟫_𝕜) = 0
    rw [← Submodule.coe_inner, ← inner_conj_symm, F.inner_discreteWave h z p, _root_.map_sub,
      inner_conj_symm, inner_conj_symm]
    ring

/-- **The discrete solutions agree with (4.10)**: `ιₕ e^{tLₕ} Rₕ ζ = graphFst ξₕ(t)` for all `t`. -/
theorem toApprox_sol (h : κ) (ζ : H.totalD.GraphSpace) (t : ℝ) :
    F.toApprox.sol h (F.ellipticProj h ζ) t = H.totalD.graphFst (F.discrete h ζ t) := by
  rw [toApprox_sol_eq]
  set G := F.discreteGroup h
  rcases le_total 0 t with ht | ht
  · have hξ := F.isSemidiscreteSolution_orbit h (F.ellipticProj h ζ) 0 (Icc 0 t)
    have h0 : F.liftXh h (G.S (0 - 0) (F.ellipticProj h ζ)) = ellipticProjection (F.Kh h) ζ := by
      rw [sub_self, C0Group.S_zero_apply, F.liftXh_ellipticProj]
    have e := F.eqOn_discrete h ζ hξ h0 ⟨ht, le_rfl⟩
    simp only [sub_zero] at e
    rw [← e]
    rfl
  · have hmem := (F.isSemidiscreteSolution_discrete h ζ univ).mem t (mem_univ t)
    set w : F.Xh h := ⟨H.totalD.graphFst (F.discrete h ζ t), hmem⟩
    have hξ := F.isSemidiscreteSolution_orbit h w t (Icc t 0)
    have hd := (F.isSemidiscreteSolution_discrete h ζ (Icc t 0))
    have h0 : F.liftXh h (G.S (t - t) w) = F.discrete h ζ t := by
      rw [sub_self, C0Group.S_zero_apply, F.liftXh_graphFst]
    have e := hξ.eqOn hd h0 ⟨ht, le_rfl⟩
    simp only [zero_sub] at e
    rw [F.discrete_zero, ← F.liftXh_ellipticProj] at e
    have e' : G.S (-t) w = F.ellipticProj h ζ := F.liftXh_injective h e
    have : G.S t (F.ellipticProj h ζ) = w := by
      rw [← e', ← C0Group.map_add_apply, add_neg_cancel, C0Group.S_zero_apply]
    rw [this]

/-- **The method is exact on the eigenvectors of `L` in `Vₕ`**: if `x ∈ ∏ Vₕⁱ` and `L x = c x`,
the discrete solution from `(x, 𝐝 x)` is `e^{tc} x` (`Pₕ (x, 𝐝 x) = (x, 𝐝 x)`,
`Lₕ x = Qₕ L x = c x`). -/
theorem graphFst_discrete_of_wave_eq_smul (h : κ) {x : H.wave.domain}
    (hx : (x : PiLp 2 W) ∈ totalSub (F.V h).V) {c : 𝕜} (e : H.wave x = c • (x : PiLp 2 W))
    (t : ℝ) :
    H.totalD.graphFst (F.discrete h (waveLift H x) t) =
      NormedSpace.exp (t • c) • (x : PiLp 2 W) := by
  set v : F.Xh h := ⟨x, hx⟩
  have hv : F.ellipticProj h (waveLift H x) = v :=
    Subtype.ext (by rw [coe_ellipticProj, ellipticProjection_of_mem _ hx]; rfl)
  have hw : F.discreteWave h v = c • v := by
    rw [← hv, F.discreteWave_ellipticProj, hv, e, _root_.map_smul,
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self v, sub_self, zero_add]
  rw [← F.toApprox_sol, hv, toApprox_sol_eq,
    (C0Group.isIsometric_ofBounded (F.discreteWave_skew h)).S_eq_of_generator_eq_smul
      (C0Group.mem_domain_generator_ofBounded _ v)
      (by rw [C0Group.generator_ofBounded_apply]; exact hw)]
  rfl

/-- **Every semi-discrete solution is a discrete orbit**: on `[0, T]` (`T ≥ 0`), a solution of
(4.10) is `ιₕ e^{tLₕ} v` with `ιₕ v = ξₕ(0)`. -/
theorem exists_eq_sol {T : ℝ} (hT : 0 ≤ T) {h : κ} {ξh ξh' : ℝ → H.totalD.GraphSpace}
    (hξ : IsSemidiscreteSolution (F.Kh h) (Icc 0 T) ξh ξh') :
    ∃ v : F.toApprox.X h, F.toApprox.incl h v = H.totalD.graphFst (ξh 0) ∧
      ∀ t ∈ Icc 0 T, H.totalD.graphFst (ξh t) = F.toApprox.sol h v t := by
  have hmem := hξ.mem 0 ⟨le_rfl, hT⟩
  set v : F.Xh h := ⟨H.totalD.graphFst (ξh 0), hmem⟩
  refine ⟨v, rfl, fun t ht => ?_⟩
  rw [toApprox_sol_eq]
  have hO := F.isSemidiscreteSolution_orbit h v 0 (Icc 0 T)
  have h0 : F.liftXh h ((F.discreteGroup h).S (0 - 0) v) = ξh 0 := by
    rw [sub_self, C0Group.S_zero_apply, F.liftXh_graphFst]
  have e := hξ.eqOn hO h0.symm ht
  rw [e]
  simp only [sub_zero]
  rfl

variable {F} in
/-- **Rate classes transfer**, with `C ↦ (1 + C_P) C`, `C' ↦ 2 (1 + C_P) C`: the rate class of the
wave Ritz projection (`DissipFEEC.Ritz.orbitRateClass`), from the static estimates of the elliptic
projection along the orbit. -/
def RateClass.toApprox {T : ℝ} (R : F.RateClass T) : F.toApprox.RateClass T :=
  F.waveRitz.orbitRateClass R.Data
    (fun x hx => mem_domainSq.2 ⟨R.mem_domain x hx, R.mem_domain_sq x _ hx⟩) R.classNorm
    R.meshSize R.α ((1 + ellipticConst H) * R.C) (2 * ((1 + ellipticConst H) * R.C))
    (fun x hx h t ht => by
      have hy := waveGroup_mem_domain H (R.mem_domain x hx) t
      obtain ⟨w, hw, hwb⟩ := R.approx x hx h t ht (graphOf H _) (graphFst_graphOf H hy)
      rw [F.toApprox.S_eq_waveGroup ht.1]
      change ‖H.waveGroup.S t x - (F.ellipticProj h (graphOf H (H.waveGroup.S t x)) : PiLp 2 W)‖ ≤ _
      have hP := F.norm_graphFst_sub_ellipticProj_le h (graphOf H (H.waveGroup.S t x)) hw
      rw [graphFst_graphOf H hy] at hP
      refine hP.trans ?_
      rw [mul_assoc, mul_assoc, ← mul_assoc R.C]
      exact mul_le_mul_of_nonneg_left hwb (by linarith [ellipticConst_nonneg H]))
    (fun x hx h t ht => by
      have hx1 := R.mem_domain x hx
      have hLx : waveExt H x ∈ H.wave.domain := by
        rw [waveExt_of_mem hx1]; exact R.mem_domain_sq x hx1 hx
      have hb : ∀ y ∈ H.wave.domain, (y = H.waveGroup.S t x ∨
          y = H.waveGroup.S t (H.wave ⟨x, hx1⟩)) → ‖F.ellipticDefect h (graphOf H y)‖ ≤
            (1 + ellipticConst H) * R.C * R.meshSize h ^ R.α * R.classNorm x := fun y hy hy' => by
        obtain ⟨w, hw, hwb⟩ : ∃ w ∈ F.Kh h, ‖graphOf H y - w‖ ≤
            R.C * R.meshSize h ^ R.α * R.classNorm x := by
          rcases hy' with rfl | rfl
          exacts [R.approx x hx h t ht _ (graphFst_graphOf H hy),
            R.approx_deriv x hx1 hx h t ht _ (graphFst_graphOf H hy)]
        refine (F.norm_ellipticDefect_le_of_mem h _ hw).trans ?_
        rw [mul_assoc, mul_assoc, ← mul_assoc R.C]
        exact mul_le_mul_of_nonneg_left hwb (by linarith [ellipticConst_nonneg H])
      rw [F.toApprox.S_eq_waveGroup ht.1, ← waveExt_eq_genExt]
      change ‖F.ellipticDefect h (graphOf H (H.waveGroup.S t (waveExt H x)))‖ +
        ‖-F.ellipticDefect h (graphOf H (H.waveGroup.S t x))‖ ≤ _
      rw [norm_neg]
      have h1 := hb _ (waveGroup_mem_domain H hLx t) (Or.inr (by rw [waveExt_of_mem hx1]))
      have h2 := hb _ (waveGroup_mem_domain H hx1 t) (Or.inl rfl)
      linarith)

variable {F} in
theorem RateClass.toApprox_p {T : ℝ} (R : F.RateClass T) {x : PiLp 2 W} (hx : x ∈ R.Data)
    (h : κ) :
    R.toApprox.p x h 0 = F.ellipticProj h (waveLift H ⟨x, R.mem_domain x hx⟩) := by
  change F.ellipticProj h (graphOf H (F.toApprox.S 0 x)) = _
  rw [F.toApprox.S_eq_waveGroup le_rfl, C0Group.S_zero_apply, graphOf_eq_waveLift]

/-- **The improved conforming rate** `(1 + C_P)(1 + 2t) C hᵅ ‖ξ₀‖_class`, from
`dissipFEEC_rate`. -/
theorem rate_le {T : ℝ} (R : F.RateClass T) {x : PiLp 2 W} (hxR : x ∈ R.Data) (h : κ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖H.waveGroup.S t x -
        H.totalD.graphFst (F.discrete h (waveLift H ⟨x, R.mem_domain x hxR⟩) t)‖ ≤
      (1 + ellipticConst H) * (1 + 2 * t) * (R.C * R.meshSize h ^ R.α * R.classNorm x) := by
  have hr := dissipFEEC_rate F.toApprox.toDissipFEEC R.toApprox hxR h (R.toApprox.p x h 0) ht
  rw [F.toApprox.S_eq_waveGroup ht.1, sub_self, norm_zero, mul_zero, add_zero, R.toApprox_p hxR,
    F.toApprox_sol] at hr
  refine hr.trans ?_
  have hx1 := R.mem_domain x hxR
  obtain ⟨w, -, hwb⟩ := R.approx x hxR h t ht (waveOrbit H x t) (graphFst_waveOrbit H hx1 t)
  have hδ : 0 ≤ R.C * R.meshSize h ^ R.α * R.classNorm x := (norm_nonneg _).trans hwb
  have hι := F.norm_toApprox_incl_le h
  have hP := ellipticConst_nonneg H
  have e : (R.toApprox.C + ‖F.toApprox.incl h‖ * R.toApprox.C' * t) *
      (R.toApprox.meshSize h ^ R.toApprox.α * R.toApprox.classNorm x) =
      (1 + ellipticConst H) * (1 + 2 * ‖F.toApprox.incl h‖ * t) *
        (R.C * R.meshSize h ^ R.α * R.classNorm x) := by
    change ((1 + ellipticConst H) * R.C + ‖F.toApprox.incl h‖ *
      (2 * ((1 + ellipticConst H) * R.C)) * t) * (R.meshSize h ^ R.α * R.classNorm x) = _
    ring
  rw [e]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by linarith)) hδ
  nlinarith [ht.1]

/-- **The rate of the constrained FEEC discretization** for data in a rate class on `[0, T]`:
`‖e^{tL} ξ₀ - ξₕ(t)‖ ≤ (1 + C_P) (1 + t)² C hᵅ ‖ξ₀‖_class` for `t ∈ [0, T]`, with
`ξₕ(0) = Pₕ ξ₀` and `C_P = √12 ‖A‖` (`ellipticConst`); implied by the improved rate `rate_le`
since `1 + 2t ≤ (1 + t)²`. [QuennevilleBelair2015], Prop. 4.13, Thm 4.14 -/
theorem _root_.Feec.HilbertComplex.constrainedFEEC_rate {T : ℝ} (R : F.RateClass T)
    {x : PiLp 2 W} (hxR : x ∈ R.Data) (h : κ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖H.waveGroup.S t x -
        H.totalD.graphFst (F.discrete h (waveLift H ⟨x, R.mem_domain x hxR⟩) t)‖ ≤
      (1 + ellipticConst H) * (1 + t) ^ 2 * (R.C * R.meshSize h ^ R.α * R.classNorm x) := by
  refine (F.rate_le R hxR h ht).trans ?_
  have hx1 := R.mem_domain x hxR
  obtain ⟨w, -, hwb⟩ := R.approx x hxR h t ht (waveOrbit H x t) (graphFst_waveOrbit H hx1 t)
  have hδ : 0 ≤ R.C * R.meshSize h ^ R.α * R.classNorm x := (norm_nonneg _).trans hwb
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_
    (by linarith [ellipticConst_nonneg H])) hδ
  nlinarith [sq_nonneg t]

/-- The elliptic projections `Rₕ ξ₀` of `ξ₀ ∈ D(L)` converge to `ξ₀` through `ιₕ`. -/
theorem tendsto_incl_ellipticProj (x : H.wave.domain) :
    Tendsto (fun h => F.toApprox.incl h (F.ellipticProj h (waveLift H x))) F.l (𝓝 x) :=
  H.totalD.graphFst.continuous.continuousAt.tendsto.comp
    ((F.isApproximating.tendstoUniformlyOn_ellipticProjection isCompact_singleton).tendsto_at
      (mem_singleton (waveLift H x)))

/-- **The constrained FEEC theorem**, the special case `ιₕ` = inclusion, `πₕ = Qₕ` of the
approximating one. For a constrained FEEC discretization `F` (a Hilbert complex on any finite
window, a closed constraint `K`, finite-dimensional subcomplexes `Vₕ` with commuting cochain
projections and the approximation property in the graph norm) of the Hodge wave equation
`ξ' = L ξ` (`ConstrainedFEEC.Verdict`):

1. (**well-posedness**, Stone) for `ξ₀ ∈ D(L)`, `t ↦ e^{tL} ξ₀` is a classical solution on
   `[0, T]`, the only strong and the only weak solution, and conserves energy;
2. (**propagation**) `K` reduces `L` iff `e^{tL} K ⊆ K` for all `t ∈ ℝ` (both time directions);
3. (**convergence**) the semi-discrete solutions `ξₕ` with `ξₕ(0) = Pₕ ξ₀` converge to
   `e^{tL} ξ₀` uniformly on `[0, T]` for `ξ₀ ∈ D(L)`; for `ξ₀ ∈ W`, every family with
   `ξₕ(0) → ξ₀` converges uniformly on `[0, T]`, and such families exist; for data in a rate class
   on `[0, T]`, `‖ξ(t) - ξₕ(t)‖ ≤ (1 + C_P) (1 + t)² C hᵅ ‖ξ₀‖_class` for `t ∈ [0, T]`
   (`constrainedFEEC_rate`; the improved `(1 + C_P)(1 + 2t)` is `rate_le`);
4. (**constraint residual**) if `K` reduces `L`, then for `ξ₀ ∈ D(L) ∩ K`,
   `dist(ξₕ(t), K) ≤ ‖e^{tL} ξ₀ - ξₕ(t)‖ → 0` uniformly on `[0, T]`; if `K` does not reduce `L`,
   then for every `T > 0`:
   (a) some datum of `K` (or of `Kᗮ`) leaves the constraint at some `t ∈ [0, T]`, and the
   residuals of every convergent discretization tend to a positive limit;
   (b) if `D(L) ∩ K` is dense in `K`, some `ξ₀ ∈ D(L) ∩ K` has `e^{tL} ξ₀ ∉ K` for some
   `t ∈ [-T, T]`;
   (c) on a graded complex, for an `R`-invariant `K` with `D(L) ∩ K` dense in `K`, some
   `ξ₀ ∈ D(L) ∩ K` leaves `K` at some `t ∈ [0, T]`, and the residuals `dist(ξₕ(t), K)` of the
   discrete solutions with `ξₕ(0) = Pₕ ξ₀` tend to `dist(e^{tL} ξ₀, K) > 0`;
5. (**discrete cohomology**) where the projections are bounded in the graph norm, `H` has closed
   range and finite-dimensional harmonic forms, `πₕ` eventually induces isomorphisms
   `Hⁱ(H) ≅ Hⁱ(Vₕ)`.

Items 1–4 are read off the verdict of `approxFEEC` for `toApprox` with the core `toCore` of the
wave Ritz projection (data `D(L²)`, dense); the cohomology field is
`SubcomplexFamily.eventually_bijective_cohomologyMap`. The bridges are `toApprox_sol` (the
semi-discrete solutions of (4.10) from `Pₕ ξ₀` are the discrete orbits from `Rₕ ξ₀`),
`exists_eq_sol` (every semi-discrete solution is a discrete orbit), the density of the core
(`mem_toCore_closure`), `tendsto_incl_ellipticProj`, and `constrainedFEEC_rate`.

[QuennevilleBelair2015], Thms 4.6, 4.7, 4.14, Prop. 4.17; [AFW2010], §3.3, Thm 3.4;
[Arnold2018], Ch. 5 -/
theorem _root_.Feec.HilbertComplex.constrainedFEEC : F.Verdict := by
  have V := approxFEEC F.toApprox F.toCore
  have hS : ∀ t, 0 ≤ t → ∀ x, F.toApprox.S t x = H.waveGroup.S t x := fun t ht x => by
    rw [F.toApprox.S_eq_waveGroup ht]
  have V1 : ∀ x ∈ H.wave.domain, ∀ T : ℝ,
      Evolution.IsClassicalSolution H.wave (Icc 0 T) 0 (fun t => H.waveGroup.S t x) ∧
      (∀ U, U 0 = x → Evolution.IsStrongSolution H.wave (Icc 0 T) 0 U →
        EqOn U (fun t => H.waveGroup.S t x) (Icc 0 T)) ∧
      (∀ U, U 0 = x → HodgeWave.IsWeakSolution H (Icc 0 T) 0 U →
        EqOn U (fun t => H.waveGroup.S t x) (Icc 0 T)) ∧
      ∀ t, ‖H.waveGroup.S t x‖ = ‖x‖ := fun x hx T => by
    have e : EqOn (fun t => F.toApprox.S t x) (fun t => H.waveGroup.S t x) (Icc 0 T) :=
      fun t ht => hS t ht.1 x
    exact ⟨(V.isClassicalSolution ⟨x, hx⟩ T).congr e fun _ _ => rfl,
      fun U hU0 hU => (V.unique ⟨x, hx⟩ T U hU0 hU).trans e,
      fun U hU0 hU => (V.unique_weak ⟨x, hx⟩ T U hU0 hU).trans e, fun t => V.norm_U t x⟩
  have V3 : ∀ T : ℝ, ∀ x ∈ F.toCore.Data.topologicalClosure,
      Tendsto (fun h => F.toApprox.incl h (F.toApprox.proj h x)) F.l (𝓝 x) ∧
      ∀ v : ∀ h, F.toApprox.X h, Tendsto (fun h => F.toApprox.incl h (v h)) F.l (𝓝 x) →
        TendstoUniformlyOn (fun h t => F.toApprox.sol h (v h) t)
          (fun t => H.waveGroup.S t x) F.l (Icc 0 T) := fun T x hx =>
    ⟨V.tendsto_incl_proj hx, fun v hv =>
      (V.converges hx hv T).congr_right fun t ht => hS t ht.1 x⟩
  have hconv : ∀ (T : ℝ) (x : H.wave.domain), TendstoUniformlyOn
      (fun h t => H.totalD.graphFst (F.discrete h (waveLift H x) t))
      (fun t => H.waveGroup.S t x) F.l (Icc 0 T) := fun T x =>
    ((V3 T x (F.mem_toCore_closure x)).2 _ (F.tendsto_incl_ellipticProj x)).congr
      (Eventually.of_forall fun h t _ => F.toApprox_sol h _ t)
  have horb : ∀ {T : ℝ}, 0 ≤ T → ∀ ξh ξh' : κ → ℝ → H.totalD.GraphSpace,
      (∀ h, IsSemidiscreteSolution (F.Kh h) (Icc 0 T) (ξh h) (ξh' h)) →
      ∃ v : ∀ h, F.toApprox.X h, (∀ h, F.toApprox.incl h (v h) = H.totalD.graphFst (ξh h 0)) ∧
        ∀ h, ∀ t ∈ Icc 0 T, H.totalD.graphFst (ξh h t) = F.toApprox.sol h (v h) t :=
    fun hT ξh ξh' hξh => by
      choose v hv0 hv using fun h => F.exists_eq_sol hT (hξh h)
      exact ⟨v, hv0, hv⟩
  have hfam : ∀ (T : ℝ) (x : PiLp 2 W) (ξh ξh' : κ → ℝ → H.totalD.GraphSpace),
      (∀ h, IsSemidiscreteSolution (F.Kh h) (Icc 0 T) (ξh h) (ξh' h)) →
      Tendsto (fun h => H.totalD.graphFst (ξh h 0)) F.l (𝓝 x) →
      TendstoUniformlyOn (fun h t => H.totalD.graphFst (ξh h t))
        (fun t => H.waveGroup.S t x) F.l (Icc 0 T) := by
    intro T x ξh ξh' hξh h0
    rcases lt_or_ge T 0 with hT | hT
    · rw [Icc_eq_empty (by linarith)]; exact tendstoUniformlyOn_empty
    obtain ⟨v, hv0, hv⟩ := horb hT ξh ξh' hξh
    exact ((V3 T x (F.mem_toCore_closure x)).2 v (h0.congr fun h => (hv0 h).symm)).congr
      (Eventually.of_forall fun h t ht => (hv h t ht).symm)
  refine
    { wellPosed := fun hx T => V1 _ hx T
      propagates_iff := V.isReducing_iff_invariant
      converges := fun x T => hconv T x
      converges_of_tendsto := fun x _ ξh ξh' hξh h0 => hfam _ x ξh ξh' hξh h0
      exists_tendsto := fun x T => ?_
      rate := fun R _ hxR h _ ht => constrainedFEEC_rate F R hxR h ht
      residual_le := fun hK x hxK h t => ?_
      residual_tendsto := fun hK x hxK T => ?_
      leaves := fun hK _ hT => ?_
      leaves_symm := fun hK hd _ hT => ?_
      leaves_graded := fun hp hRK hdense hK _ hT => ?_
      cohomology := fun hb _ hi =>
        SubcomplexFamily.eventually_bijective_cohomologyMap hb (F.approximates _) hi }
  · -- existence of a convergent family: the solutions from `Qₕ ξ₀`
    refine ⟨fun h => F.discrete h (F.liftXh h (F.orthProj h x)),
      fun h => F.discreteDeriv h (F.liftXh h (F.orthProj h x)),
      fun h => F.isSemidiscreteSolution_discrete h _ _, ?_⟩
    refine (V3 T x (F.mem_toCore_closure x)).1.congr fun h => ?_
    change ((F.orthProj h x : F.Xh h) : PiLp 2 W) =
      H.totalD.graphFst (F.discrete h (F.liftXh h (F.orthProj h x)) 0)
    rw [F.discrete_zero, ellipticProjection_of_mem _ (F.liftXh_mem _ _), graphFst_liftXh]
  · -- reducing constraint: the residual bound
    rw [← F.toApprox_sol, norm_sub_rev, ← dist_eq_norm]
    exact infDist_le_dist_of_mem (V.isReducing_iff_invariant.1 hK t x hxK)
  · -- reducing constraint: the residual tends to `0`
    exact (V.residual_tendsto (V.isReducing_iff.1 hK).1 hxK (F.mem_toCore_closure x)
      (F.tendsto_incl_ellipticProj x) T).congr
      (Eventually.of_forall fun h t _ =>
        congrArg (infDist · (F.K : Set (PiLp 2 W))) (F.toApprox_sol h _ t))
  · -- non-reducing constraint, data of `K` or `Kᗮ`
    obtain ⟨Q, hQ, x, hx, t, ht, hout⟩ :=
      dissipFEEC_leaves_of_not_isReducing F.toApprox.toDissipFEEC hK hT
    have hQc : IsClosed (Q : Set (PiLp 2 W)) := by
      rcases hQ with rfl | rfl
      exacts [F.isClosed_K, Submodule.isClosed_orthogonal _]
    obtain ⟨hp, hdet⟩ := V.detects hQc ⟨0, Q.zero_mem⟩ ht.1 hout
    rw [F.toApprox.S_eq_waveGroup ht.1] at hout hp hdet
    refine ⟨Q, hQ, x, hx, t, ht, hout, hp, fun ξh ξh' hξh h0 => ?_⟩
    obtain ⟨v, hv0, hv⟩ := horb hT.le ξh ξh' hξh
    exact (hdet (F.mem_toCore_closure x) v (h0.congr fun h => (hv0 h).symm)).1.congr fun h => by
      rw [hv h t ht]
  · -- non-reducing constraint, `D(L) ∩ K` dense in `K`: both time directions
    obtain ⟨x, ⟨hxD, hxK⟩, t, ht, hout⟩ := V.leaves_smooth_symm F.isClosed_K
      (fun h => hK (V.isReducing_iff_invariant.2 h)) hd hT
    exact ⟨⟨x, hxD⟩, hxK, t, ht, hout,
      (F.isClosed_K.notMem_iff_infDist_pos ⟨0, F.K.zero_mem⟩).1 hout⟩
  · -- graded complex
    obtain ⟨x, ⟨hxD, hxK⟩, t, ht, hout⟩ := V.leaves_smooth F.isClosed_K
      (fun h => hK ((V.isReducing_iff_keeps hp hRK hdense).2 h)) hdense hT
    obtain ⟨hp0, hdet⟩ := V.detects F.isClosed_K ⟨0, F.K.zero_mem⟩ ht.1 hout
    obtain ⟨hl, hev⟩ := hdet (F.mem_toCore_closure x) _ (F.tendsto_incl_ellipticProj ⟨x, hxD⟩)
    rw [F.toApprox.S_eq_waveGroup ht.1] at hout hp0 hl hev
    simp only [F.toApprox_sol] at hl hev
    exact ⟨⟨x, hxD⟩, hxK, t, ht, hout, hp0, hl, hev⟩

/-- The constrained FEEC theorem as the special case of `approxFEEC` (`constrainedFEEC`). -/
alias constrainedFEEC_of_approxFEEC := constrainedFEEC

/-- **The residuals vanish in the limit exactly along the data that keep the constraint** (a
corollary of the verdict of `approxFEEC` with the dense core, for every closed `K`, reducing or
not): for every `x ∈ W` and every family `ιₕ vₕ → x`, the residuals `dist(ιₕ e^{tLₕ} vₕ, K)` tend to
`0` at every `t ≥ 0` iff `e^{tL} x ∈ K` for every `t ≥ 0`
(`DissipFEEC.Verdict.tendsto_infDist_zero_iff`). -/
theorem tendsto_infDist_zero_iff [F.l.NeBot] {x : PiLp 2 W} {v : ∀ h, F.toApprox.X h}
    (hv : F.toApprox.Converges v x) :
    (∀ t, 0 ≤ t → Tendsto (fun h => infDist (F.toApprox.sol h (v h) t) (F.K : Set (PiLp 2 W)))
      F.l (𝓝 0)) ↔ ∀ t, 0 ≤ t → H.waveGroup.S t x ∈ F.K := by
  have : F.toApprox.l.NeBot := ‹F.l.NeBot›
  refine ((approxFEEC F.toApprox F.toCore).tendsto_infDist_zero_iff F.isClosed_K
    ⟨0, F.K.zero_mem⟩ (F.mem_toCore_closure x) hv).trans ?_
  exact forall₂_congr fun t ht => by rw [F.toApprox.S_eq_waveGroup ht]; rfl

/-- **The rate class of degreewise regular data**, from degreewise best-approximation estimates:
the data of the trajectory scale (`DissipFEEC.RegScale.trajectory`, class norm `Λ`) of the states
whose components and those of `L y` satisfy the degreewise regularity `Reg`, for data in
`D(L²)`, when every `Reg`-regular `x ∈ Wⁱ` has some `v ∈ Vₕⁱ` with `‖x - v‖, ‖d (x - v)‖ ≤ Bᵢ Λ r_h`
(`RateClass.exists_mem_Kh_le_of_degreewise`). The constant is `(m + m²) Σᵢ Bᵢ` (`m` the number of
degrees), the order `1` in `r_h`, the class norm `Λ`; interpolation estimates of order `hˢ` enter
with `r_h = hˢ`. Its rate class of `toApprox` (`RateClass.toApprox`) is the wave Ritz projection
on these data. [AFW2010], §3.3; [QuennevilleBelair2015], Thm 4.14 -/
def RateClass.ofDegreewise (T : ℝ) (Reg : ∀ i, W i → Prop) (B : ι → ℝ) (r : κ → ℝ) (Λ : ℝ)
    (happ : ∀ h i (x : W i), Reg i x → ∃ v, ∃ hv : v ∈ (F.V h).V i,
      ‖x - v‖ ≤ B i * Λ * r h ∧ ∀ j (hxj : x ∈ (H.d i j).domain),
        ‖H.d i j ⟨x - v, Submodule.sub_mem _ hxj ((F.V h).le_domain i j hv)⟩‖ ≤ B i * Λ * r h)
    (hB : ∀ i, 0 ≤ B i) (hΛ : 0 ≤ Λ) (hr : ∀ h, 0 ≤ r h) : F.RateClass T where
  Data := (DissipFEEC.RegScale.trajectory F.toApprox.toDissipFEEC T H.wave.domainSq
    {y | (∀ i, Reg i (y i)) ∧ ∀ i, Reg i (waveExt H y i)} (fun _ => Λ) (fun _ => Λ)).Data
  classNorm _ := Λ
  meshSize := r
  α := 1
  C := ((Fintype.card ι : ℝ) + (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ)) * ∑ i, B i
  mem_domain _ hx := domainSq_le_domain hx.1
  mem_domain_sq _ _ hx := (mem_domainSq.1 hx.1).2
  approx x hx h t ht v hv := by
    have hreg := (hx.2 t ht).1.1
    rw [F.toApprox.S_eq_waveGroup ht.1] at hreg
    exact RateClass.exists_mem_Kh_le_of_degreewise F happ hB hΛ hr h hreg v hv
  approx_deriv x hx1 hx h t ht v hv := by
    have hreg := (hx.2 t ht).1.2
    rw [F.toApprox.S_eq_waveGroup ht.1, waveExt_waveGroup H hx1, waveExt_of_mem hx1] at hreg
    exact RateClass.exists_mem_Kh_le_of_degreewise F happ hB hΛ hr h hreg v hv

/-- **Non-vacuity of `RateClass.ofDegreewise`**: the zero datum lies in the class whenever the
zero form is regular in every degree. -/
theorem RateClass.zero_mem_ofDegreewise {F : ConstrainedFEEC H κ} {T : ℝ}
    {Reg : ∀ i, W i → Prop} {B : ι → ℝ} {r : κ → ℝ} {Λ : ℝ} {happ hB hΛ hr} (h0 : ∀ i, Reg i 0) :
    (0 : PiLp 2 W) ∈ (RateClass.ofDegreewise F T Reg B r Λ happ hB hΛ hr).Data := by
  have e : waveExt H 0 = 0 := by
    rw [waveExt_of_mem H.wave.domain.zero_mem]; exact H.wave.toFun.map_zero
  refine ⟨H.wave.domainSq.zero_mem, fun s _ => ⟨⟨fun i => ?_, fun i => ?_⟩, le_rfl⟩⟩
  · rw [_root_.map_zero]; exact h0 _
  · rw [_root_.map_zero, e]; exact h0 _

/-- **The rate class of a Jackson estimate** (`SubcomplexFamily.Jackson`) of the conforming
family: `RateClass.ofDegreewise` for the `s`-regular forms with bound `L`, so the data are the
`ξ₀ ∈ D(L²)` whose trajectory and that of `L ξ₀` stay `s`-regular with bound `L` on `[0, T]`, the
constant is `(m + m²) Σᵢ B_{s,i}`, the order `hₕ^{ord s}` and the class norm `L`.
[AFW2010], §3.4; [QuennevilleBelair2015], Thm 4.14 -/
def RateClass.ofJackson {ρ : Type*} (J : F.Jackson ρ) (T : ℝ) (s : ρ) {L : ℝ} (hL : 0 ≤ L) :
    F.RateClass T :=
  RateClass.ofDegreewise F T (fun i => J.Reg s i L) (J.B s) (fun h => J.meshSize h ^ J.ord s) L
    (fun h i x hx => by
      obtain ⟨v, hv, h1, h2⟩ := J.jackson s h i x hL hx
      exact ⟨v, hv, h1.trans_eq (by ring), fun j hxj => (h2 j hxj).trans_eq (by ring)⟩)
    (J.B_nonneg s) hL fun h => Real.rpow_nonneg (J.meshSize_nonneg h) _

open ShortHilbertComplex in
/-- **Non-vacuity of the constrained FEEC theorem**: on `𝕜 --id--> 𝕜 → 0` with `Vₕ = W` and
`πₕ = id` (all hypotheses of `ConstrainedFEEC` hold), both branches of item 4 occur. The constraint
`K = W` reduces `L`; the constraint `K = 𝕜 × 0 × 0` is closed, invariant under the grading, with
`D(L) ∩ K = K`, and does not reduce `L`; so for every `T > 0` some datum of `D(L) ∩ K` leaves `K`
at some `t ∈ [0, T]` and the discrete residuals tend to a positive limit. For every horizon `T`,
a rate class with `α = 1`, `h = 1/(N+1)`, contains all of `D(L²) = W`. -/
theorem _root_.Feec.HilbertComplex.constrainedFEEC_nonvacuous :
    (idComplex 𝕜).wave.IsReducing (idFEEC 𝕜 ⊤ (by rw [Submodule.top_coe]; exact isClosed_univ)).K ∧
    ¬ (idComplex 𝕜).wave.IsReducing (idFEEC 𝕜 (firstSub 𝕜) isClosed_totalSub).K ∧
    (∀ T : ℝ, 0 < T → ∃ x : (idComplex 𝕜).wave.domain, (x : PiLp 2 (W3 𝕜 𝕜 PUnit)) ∈ firstSub 𝕜 ∧
      ∃ t ∈ Icc 0 T, (idComplex 𝕜).waveGroup.S t x ∉ firstSub 𝕜 ∧
        0 < infDist ((idComplex 𝕜).waveGroup.S t x) (firstSub 𝕜 : Set (PiLp 2 (W3 𝕜 𝕜 PUnit))) ∧
        Tendsto (fun N => infDist ((idComplex 𝕜).totalD.graphFst
            ((idFEEC 𝕜 (firstSub 𝕜) isClosed_totalSub).discrete N (waveLift _ x) t))
            (firstSub 𝕜 : Set (PiLp 2 (W3 𝕜 𝕜 PUnit)))) atTop
          (𝓝 (infDist ((idComplex 𝕜).waveGroup.S t x)
            (firstSub 𝕜 : Set (PiLp 2 (W3 𝕜 𝕜 PUnit)))))) ∧
    ∀ T : ℝ, ∃ R : (idFEEC 𝕜 (firstSub 𝕜) isClosed_totalSub).RateClass T,
      R.Data = univ ∧ R.α = 1 ∧ ∀ N, R.meshSize N = 1 / ((N : ℝ) + 1) := by
  set F := idFEEC 𝕜 (firstSub 𝕜) isClosed_totalSub
  refine ⟨(constrainedFEEC_propagates_iff _).2 fun _ _ _ => Submodule.mem_top,
    not_isReducing_firstSub, fun T hT => ?_, ?_⟩
  · obtain ⟨x, hxK, t, ht, hout, hpos, hlim, -⟩ :=
      (constrainedFEEC F).leaves_graded (p := fun i : Fin 3 => decide (Odd i.val))
        (fun _ _ h => ComplexShape.window_parity h)
        (fun x hx => reversal_mem_totalSub hx)
        (fun k hk => subset_closure ⟨mem_idComplex_wave_domain k, hk⟩) not_isReducing_firstSub hT
    exact ⟨x, hxK, t, ht, hout, hpos, hlim⟩
  · exact fun T => ⟨idRate T, rfl, rfl, fun _ => rfl⟩


end ConstrainedFEEC

end Feec.HilbertComplex
