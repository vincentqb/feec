module

public import Feec.HilbertComplex.Approximation.ApproxFEEC

/-!
# Conforming special cases of the approximating FEEC theorem

Two families of discretizations without variational crimes are approximating FEEC
discretizations (`Feec.HilbertComplex.ApproxFEEC`), with `ιₕ` the inclusion of a subspace of `W`:

* **Constrained FEEC discretizations** (`Feec.HilbertComplex.ConstrainedFEEC`, finite-dimensional
  subcomplexes with bounded commuting cochain projections): `ConstrainedFEEC.toApprox` has
  `Xₕ = ∏ Vₕⁱ ⊆ W` with the `W` inner product, the discrete wave operator `Lₕ` of (4.10)
  (`ConstrainedFEEC.discreteWave`, `⟪Lₕ x, ψ⟫ = ⟪𝐝 x, ψ⟫ - ⟪x, 𝐝 ψ⟫`), `ιₕ` the inclusion and
  `πₕ = Πₕ`. Its core `ConstrainedFEEC.toCore` (data `D(L²)`, dense) is the Trotter–Kato bridge
  with `Rₕ` the elliptic projection (4.11) and the defect identity
  `Rₕ (L y) - Lₕ Rₕ y = Qₕ (Pₕ - 1)(L y) - Qₕ (Pₕ - 1) y` (`Qₕ` the orthogonal projection onto
  `Xₕ`; `ConstrainedFEEC.ellipticProj_defect`). The discrete solutions are those of (4.10)
  (`ConstrainedFEEC.toApprox_sol`, `ConstrainedFEEC.exists_eq_sol`), and rate classes transfer
  (`ConstrainedFEEC.RateClass.toApprox`), giving the improved rate
  `(1 + C_P)(1 + 2t) C hᵅ ‖ξ₀‖_class` (`ConstrainedFEEC.rate_le`), which implies
  `constrainedFEEC_rate` since `1 + 2t ≤ (1 + t)²` (`ConstrainedFEEC.rate_le_constrainedFEEC`).
  The full verdict of `constrainedFEEC` (`ConstrainedFEEC.Verdict`) is re-derived from `approxFEEC`
  (`ConstrainedFEEC.constrainedFEEC_of_approxFEEC`, from the verdict of `ConstrainedFEEC.toApprox`):
  it is the special case `ιₕ` = inclusion, `πₕ = Πₕ`. The consistency defect of this special case
  is in general not zero: by `ConstrainedFEEC.ellipticProj_defect` it is `Δₕ(L y) - Δₕ(y)` along
  the orbit,
  which tends to `0` (the conforming discretization commits no variational crime, but `Rₕ` does not
  commute with `L`). `constrainedFEEC` itself keeps its direct proof.
* **Reducing families** (`Feec.HilbertComplex.ReducingFamily`): closed reducing subspaces
  `B_N ⊆ D(L)` (not necessarily finite-dimensional) on which `L` is bounded, with projections
  converging strongly to `1`: spectral Galerkin methods, exact on the bands
  (`ReducingFamily.toApprox_sol`); the core is all of `W`, with zero defect, and truncation rates
  give rate classes with `C' = 0` (`ReducingFamily.rateClass`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.6 ((4.10), (4.11), Prop. 4.13, Thm 4.14), §4.12–4.13
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3

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

/-- The total cochain projection `Πₕ` as a bounded map `W → Xₕ`. -/
def piProjL (h : κ) : PiLp 2 W →L[𝕜] F.Xh h :=
  (LinearMap.mkContinuous (F.piProj h) F.projConst (F.norm_piProj_le h)).codRestrict
    (totalSub (F.V h).V) (F.piProj_mem h)

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

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- **Every constrained FEEC discretization is an approximating one**: `Xₕ = ∏ Vₕⁱ`, `ιₕ` the
inclusion, `πₕ = Πₕ`, `Lₕ` the discrete wave operator of (4.10). -/
def toApprox : ApproxFEEC H κ where
  K := F.K
  isClosed_K := F.isClosed_K
  l := F.l
  X := F.Xh
  L := F.discreteWave
  isSkewAdjoint := H.isSkewAdjoint_wave
  skew := F.discreteWave_skew
  incl h := (totalSub (F.V h).V).subtypeL
  proj := F.piProjL
  proj_incl h x := Subtype.ext (F.piProj_of_mem h x.2)
  bound := ⟨max 1 F.projConst, fun h =>
    ⟨(ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      rw [one_mul]; exact le_rfl).trans
      (le_max_left _ _),
    (ContinuousLinearMap.opNorm_le_bound _ F.projConst_nonneg fun x =>
      F.norm_piProj_le h x).trans (le_max_right _ _)⟩⟩

theorem norm_toApprox_incl_le (h : κ) : ‖F.toApprox.incl h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [one_mul]; exact le_rfl

/-- Its core: the Trotter–Kato bridge with `Rₕ = ellipticProj`, `Δₕ = Qₕ graphFst (Pₕ - 1)`,
`Δₕ' = -Δₕ`; data `D(L²)`. -/
def toCore : F.toApprox.Core :=
  ApproxFEEC.Core.ofOperator F.toApprox F.ellipticProj ⟨_, F.norm_ellipticProj_le⟩
    (fun ζ => H.totalD.graphFst.continuous.continuousAt.tendsto.comp
      ((F.isApproximating.tendstoUniformlyOn_ellipticProjection isCompact_singleton).tendsto_at
        (mem_singleton ζ)))
    F.ellipticDefect (fun h => -F.ellipticDefect h)
    ⟨_, fun h => ⟨F.norm_ellipticDefect_le h,
      (norm_neg (F.ellipticDefect h)).trans_le (F.norm_ellipticDefect_le h)⟩⟩
    F.ellipticProj_defect
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
  · have hd := (C0Group.hasDerivAt_exp_ofReal_smul_apply (F.discreteWave h) w
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
/-- **Rate classes transfer**, with `C ↦ (1 + C_P) C`, `C' ↦ 2 (1 + C_P) C`. -/
def RateClass.toApprox {T : ℝ} (R : F.RateClass T) : F.toApprox.RateClass T where
  toComparison := (ApproxFEEC.Comparison.ofOperator F.toApprox F.ellipticProj T).restrict R.Data
    fun x hx => mem_domainSq.2 ⟨R.mem_domain x hx, R.mem_domain_sq x _ hx⟩
  classNorm := R.classNorm
  meshSize := R.meshSize
  α := R.α
  C := (1 + ellipticConst H) * R.C
  C' := 2 * ((1 + ellipticConst H) * R.C)
  approx x hx h t ht := by
    have hx1 := R.mem_domain x hx
    rw [F.toApprox.S_eq_waveGroup ht.1]
    change ‖H.waveGroup.S t x - ((F.ellipticProj h (waveOrbit H x t) : F.Xh h) : PiLp 2 W)‖ ≤ _
    obtain ⟨w, hw, hwb⟩ := R.approx x hx h t ht (waveOrbit H x t) (graphFst_waveOrbit H hx1 t)
    rw [coe_ellipticProj, ← graphFst_waveOrbit H hx1 t, ← H.totalD.graphFst.map_sub]
    refine (norm_graphFst_le _).trans ((F.norm_sub_ellipticProjection_le h _ hw).trans ?_)
    calc (1 + ellipticConst H) * ‖waveOrbit H x t - w‖ ≤
        (1 + ellipticConst H) * (R.C * R.meshSize h ^ R.α * R.classNorm x) :=
          mul_le_mul_of_nonneg_left hwb (by linarith [ellipticConst_nonneg H])
      _ = _ := by ring
  consistency x hx h t ht := by
    have hx1 := R.mem_domain x hx
    have hx2 := R.mem_domain_sq x hx1 hx
    have hxs : x ∈ H.wave.domainSq := mem_domainSq.2 ⟨hx1, hx2⟩
    have hy := waveGroup_mem_domain H hx1 t
    have hLy : H.wave ⟨_, hy⟩ ∈ H.wave.domain := by
      rw [wave_waveGroup hx1 t]; exact waveGroup_mem_domain H hx2 t
    change ‖F.ellipticProj h (waveOrbit H (waveExt H x) t) -
      F.discreteWave h (F.ellipticProj h (waveOrbit H x t))‖ ≤ _
    rw [waveOrbit_waveExt H hxs, waveOrbit_of_mem H hx1, F.ellipticProj_defect h ⟨_, hy⟩ hLy,
      _root_.neg_apply]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]
    have hb : ∀ v : H.totalD.GraphSpace, (H.totalD.graphFst v = H.waveGroup.S t x ∨
        H.totalD.graphFst v = H.waveGroup.S t (H.wave ⟨x, hx1⟩)) →
        ‖F.ellipticDefect h v‖ ≤ (1 + ellipticConst H) * (R.C * R.meshSize h ^ R.α *
          R.classNorm x) := fun v hv => by
      obtain ⟨w, hw, hwb⟩ : ∃ w ∈ F.Kh h, ‖v - w‖ ≤ R.C * R.meshSize h ^ R.α * R.classNorm x := by
        rcases hv with hv | hv
        exacts [R.approx x hx h t ht v hv, R.approx_deriv x hx1 hx h t ht v hv]
      refine (F.norm_ellipticDefect_apply_le h v).trans ?_
      rw [norm_sub_rev]
      exact (F.norm_sub_ellipticProjection_le h v hw).trans
        (mul_le_mul_of_nonneg_left hwb (by linarith [ellipticConst_nonneg H]))
    have h1 := hb (waveLift H ⟨_, hLy⟩) (Or.inr (wave_waveGroup hx1 t))
    have h2 := hb (waveLift H ⟨_, hy⟩) (Or.inl rfl)
    calc _ ≤ (1 + ellipticConst H) * (R.C * R.meshSize h ^ R.α * R.classNorm x) +
          (1 + ellipticConst H) * (R.C * R.meshSize h ^ R.α * R.classNorm x) := add_le_add h1 h2
      _ = _ := by ring

variable {F} in
theorem RateClass.toApprox_p {T : ℝ} (R : F.RateClass T) {x : PiLp 2 W} (hx : x ∈ R.Data)
    (h : κ) :
    R.toApprox.p x h 0 = F.ellipticProj h (waveLift H ⟨x, R.mem_domain x hx⟩) := by
  change F.ellipticProj h (waveOrbit H x 0) = _
  rw [waveOrbit_of_mem H (R.mem_domain x hx)]
  congr 2
  exact Subtype.ext (C0Group.S_zero_apply _ x)

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
    simp only [RateClass.toApprox]; ring
  rw [e]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by linarith)) hδ
  nlinarith [ht.1]

/-- The improved rate implies the rate `(1 + C_P)(1 + t)²` of `constrainedFEEC_rate`. -/
theorem rate_le_constrainedFEEC {T : ℝ} (R : F.RateClass T) {x : PiLp 2 W} (hxR : x ∈ R.Data)
    (h : κ) {t : ℝ} (ht : t ∈ Icc 0 T) :
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

/-- **The constrained FEEC theorem, re-derived from the approximating one**: the verdict
`ConstrainedFEEC.Verdict` of `constrainedFEEC`, proved from the verdict of `approxFEEC` for
`toApprox` (the special
case `ιₕ` = inclusion, `πₕ = Πₕ`, core `D(L²)`). The bridges are `toApprox_sol` (the semi-discrete
solutions of (4.10) from `Pₕ ξ₀` are the discrete orbits from `Rₕ ξ₀`), `exists_eq_sol` (every
semi-discrete solution is a discrete orbit), the density of the core (`mem_toCore_closure`),
`tendsto_incl_ellipticProj`, and the rate comparison `rate_le_constrainedFEEC`. -/
theorem constrainedFEEC_of_approxFEEC : F.Verdict := by
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
      rate := fun R _ hxR h _ ht => F.rate_le_constrainedFEEC R hxR h ht
      residual_le := fun hK x hxK h t => ?_
      residual_tendsto := fun hK x hxK T => ?_
      leaves := fun hK _ hT => ?_
      leaves_symm := fun hK hd _ hT => ?_
      leaves_graded := fun hp hRK hdense hK _ hT => ?_
      cohomology := fun hi hfd => haveI := hfd; F.eventually_bijective_cohomologyMap hi }
  · -- existence of a convergent family: the solutions from `Πₕ ξ₀`
    refine ⟨fun h => F.discrete h (F.liftXh h (F.piProjL h x)),
      fun h => F.discreteDeriv h (F.liftXh h (F.piProjL h x)),
      fun h => F.isSemidiscreteSolution_discrete h _ _, ?_⟩
    refine (V3 T x (F.mem_toCore_closure x)).1.congr fun h => ?_
    change ((F.piProjL h x : F.Xh h) : PiLp 2 W) =
      H.totalD.graphFst (F.discrete h (F.liftXh h (F.piProjL h x)) 0)
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

end ConstrainedFEEC

/-! ### Reducing families -/

/-- A **reducing family**: closed reducing subspaces `B_N ⊆ D(L)` on which `L` is bounded, with
orthogonal projections converging strongly to `1` (spectral families, also infinite-dimensional
bands). -/
structure ReducingFamily (H : HilbertComplex 𝕜 c W) (κ : Type*) where
  /-- the bands -/
  B : κ → Submodule 𝕜 (PiLp 2 W)
  [completeSpace : ∀ N, CompleteSpace (B N)]
  /-- the filter along which the bands exhaust `W` -/
  l : Filter κ
  isReducing : ∀ N, H.wave.IsReducing (B N)
  le_domain : ∀ N, B N ≤ H.wave.domain
  bounded : ∀ N, ∃ C, ∀ x (hx : x ∈ H.wave.domain), x ∈ B N → ‖H.wave ⟨x, hx⟩‖ ≤ C * ‖x‖
  tendsto : ∀ x, Tendsto (fun N => (B N).starProjection x) l (𝓝 x)

attribute [instance] ReducingFamily.completeSpace

namespace ReducingFamily

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (S : ReducingFamily H κ)

/-- `L` restricted to `B_N` (bounded). -/
def restrictWave (N : κ) : S.B N →L[𝕜] S.B N :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨H.wave ⟨x, S.le_domain N x.2⟩,
        (S.isReducing N).mapsTo ⟨x, S.le_domain N x.2⟩ x.2⟩
      map_add' := fun x y => Subtype.ext (by
        change H.wave (⟨x, S.le_domain N x.2⟩ + ⟨y, S.le_domain N y.2⟩) = _
        rw [LinearPMap.map_add]; rfl)
      map_smul' := fun a x => Subtype.ext (by
        change H.wave (a • ⟨x, S.le_domain N x.2⟩) = _
        rw [LinearPMap.map_smul]; rfl) }
    (S.bounded N).choose fun x => (S.bounded N).choose_spec x (S.le_domain N x.2) x.2

theorem coe_restrictWave (N : κ) (x : S.B N) :
    (S.restrictWave N x : PiLp 2 W) = H.wave ⟨x, S.le_domain N x.2⟩ := rfl

theorem restrictWave_skew (N : κ) (x y : S.B N) :
    ⟪S.restrictWave N x, y⟫_𝕜 = -⟪x, S.restrictWave N y⟫_𝕜 := by
  rw [Submodule.coe_inner, Submodule.coe_inner, coe_restrictWave, coe_restrictWave]
  exact H.isSkewAdjoint_wave.isSkewSymmetric ⟨x, S.le_domain N x.2⟩ ⟨y, S.le_domain N y.2⟩

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- The spectral Galerkin method: `X_N = B_N`, `ι_N` the inclusion, `π_N` the orthogonal
projection, `L_N = L|_{B_N}`. -/
def toApprox (K : Submodule 𝕜 (PiLp 2 W)) (hK : IsClosed (K : Set (PiLp 2 W))) :
    ApproxFEEC H κ where
  K := K
  isClosed_K := hK
  l := S.l
  X N := S.B N
  L := S.restrictWave
  isSkewAdjoint := H.isSkewAdjoint_wave
  skew := S.restrictWave_skew
  incl N := (S.B N).subtypeL
  proj N := (S.B N).orthogonalProjectionOnto
  proj_incl N x := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x
  bound := ⟨1, fun N => ⟨ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp,
    Submodule.orthogonalProjectionOnto_norm_le _⟩⟩

theorem waveGroup_mem (N : κ) (t : ℝ) {y : PiLp 2 W} (hy : y ∈ S.B N) :
    H.waveGroup.S t y ∈ S.B N :=
  C0Group.map_le_iff_forall.1 ((H.isReducing_iff_waveGroup_invariant (S.B N)).1
    (S.isReducing N)) t y hy

theorem waveGroup_starProjection (N : κ) (t : ℝ) (x : PiLp 2 W) :
    H.waveGroup.S t ((S.B N).starProjection x) = (S.B N).starProjection (H.waveGroup.S t x) :=
  H.isIsometric_waveGroup.S_starProjection (fun s _ hy => S.waveGroup_mem N s hy) t x

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
private theorem hasDerivAt_of_isometry {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E →ₗ[ℝ] F) (hg : ∀ x, ‖g x‖ = ‖x‖)
    {f : ℝ → E} {f' : E} {t : ℝ} (h : HasDerivAt (fun r => g (f r)) (g f') t) :
    HasDerivAt f f' t := by
  rw [hasDerivAt_iff_isLittleO] at h ⊢
  rw [← Asymptotics.isLittleO_norm_left] at h ⊢
  have e : (fun r => ‖f r - f t - (r - t) • f'‖) =
      fun r => ‖g (f r) - g (f t) - (r - t) • g f'‖ :=
    funext fun r => by rw [← _root_.map_smul, ← _root_.map_sub, ← _root_.map_sub, hg]
  rw [e]; exact h

/-- The projected orbit `t ↦ P_N e^{tL} x = e^{tL} P_N x` is differentiable in `B_N`, with
derivative `L_N` of it. -/
theorem hasDerivAt_proj_orbit (N : κ) (x : PiLp 2 W) (t : ℝ) :
    HasDerivAt (fun s => (S.B N).orthogonalProjectionOnto (H.waveGroup.S s x))
      (S.restrictWave N ((S.B N).orthogonalProjectionOnto (H.waveGroup.S t x))) t := by
  set y := (S.B N).starProjection x
  have hy : y ∈ H.wave.domain := S.le_domain N ((S.B N).starProjection_apply_mem x)
  refine hasDerivAt_of_isometry ((S.B N).subtype.restrictScalars ℝ) (fun _ => rfl) ?_
  have e : (fun s => ((S.B N).subtype.restrictScalars ℝ)
      ((S.B N).orthogonalProjectionOnto (H.waveGroup.S s x))) = fun s => H.waveGroup.S s y := by
    funext s
    change (S.B N).starProjection (H.waveGroup.S s x) = _
    rw [S.waveGroup_starProjection]
  rw [e]
  have hd := hasDerivAt_waveGroup H hy t
  convert hd using 1
  change H.wave ⟨(S.B N).starProjection (H.waveGroup.S t x), _⟩ = _
  rw [← wave_waveGroup hy t]
  congr 2
  exact (S.waveGroup_starProjection N t x).symm

/-- **The spectral Galerkin method is exact on the band**: `ι_N e^{tL_N} P_N x = P_N e^{tL} x`. -/
theorem toApprox_sol (K : Submodule 𝕜 (PiLp 2 W)) (hK : IsClosed (K : Set (PiLp 2 W))) (N : κ)
    (x : PiLp 2 W) (t : ℝ) :
    (S.toApprox K hK).sol N ((S.B N).orthogonalProjectionOnto x) t =
      (S.B N).starProjection (H.waveGroup.S t x) := by
  have e := eq_ofBounded_of_hasDerivAt (S.restrictWave N) (S.restrictWave_skew N)
    (S.hasDerivAt_proj_orbit N x) t
  rw [C0Group.S_zero_apply] at e
  change (((C0Group.ofBounded (S.restrictWave N)).S t ((S.B N).orthogonalProjectionOnto x) :
    S.B N) : PiLp 2 W) = _
  rw [← e]
  rfl

/-- The comparison of the spectral Galerkin method: `p_N(t) = P_N e^{tL} x` for all data. -/
def comparison (K : Submodule 𝕜 (PiLp 2 W)) (hK : IsClosed (K : Set (PiLp 2 W))) (T : ℝ) :
    (S.toApprox K hK).Comparison T where
  Data := univ
  p x N t := (S.B N).orthogonalProjectionOnto (H.waveGroup.S t x)
  p' x N t := S.restrictWave N ((S.B N).orthogonalProjectionOnto (H.waveGroup.S t x))
  continuousOn x _ N := ((S.B N).orthogonalProjectionOnto.continuous.comp
    (H.waveGroup.strongCont x)).continuousOn
  continuousOn' x _ N := ((S.restrictWave N).continuous.comp
    ((S.B N).orthogonalProjectionOnto.continuous.comp (H.waveGroup.strongCont x))).continuousOn
  hasDerivWithinAt x _ N t _ := (S.hasDerivAt_proj_orbit N x t).hasDerivWithinAt

theorem comparison_defect (K hK) (T : ℝ) (x : PiLp 2 W) (N : κ) (t : ℝ) :
    (S.comparison K hK T).defect x N t = 0 := sub_self _

/-- The core of the spectral Galerkin method: all of `W`, with zero consistency defect. -/
def toCore (K : Submodule 𝕜 (PiLp 2 W)) (hK : IsClosed (K : Set (PiLp 2 W))) :
    (S.toApprox K hK).Core where
  Data := ⊤
  cmp T := S.comparison K hK T
  data_eq _ := Submodule.top_coe.symm
  tendsto_approx T x _ := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(Metric.tendsto_nhds.1 (S.tendsto x)) ε hε] with N hN t ht
    rw [dist_eq_norm, (S.toApprox K hK).S_eq_waveGroup ht.1]
    change ‖H.waveGroup.S t x - (S.B N).starProjection (H.waveGroup.S t x)‖ < ε
    rw [← S.waveGroup_starProjection, ← _root_.map_sub, H.isIsometric_waveGroup t,
      ← dist_eq_norm, dist_comm]
    exact hN
  tendsto_defect T x _ := by
    simp only [comparison_defect, norm_zero]
    exact Metric.tendstoUniformlyOn_iff.2 fun ε hε =>
      Eventually.of_forall fun _ _ _ => by rw [dist_self]; exact hε

/-- **Rate classes from truncation rates** (`C' = 0`): a truncation estimate
`‖x - P_N x‖ ≤ C hᵅ ‖x‖_c` gives the rate on every horizon (the truncation error is conserved by
the wave group). -/
def rateClass (K : Submodule 𝕜 (PiLp 2 W)) (hK : IsClosed (K : Set (PiLp 2 W))) (T : ℝ)
    (Data : Set (PiLp 2 W)) (classNorm : PiLp 2 W → ℝ) (meshSize : κ → ℝ) (α C : ℝ)
    (hrate : ∀ x ∈ Data, ∀ N, ‖x - (S.B N).starProjection x‖ ≤ C * meshSize N ^ α * classNorm x) :
    (S.toApprox K hK).RateClass T where
  toComparison := (S.comparison K hK T).restrict Data (subset_univ _)
  classNorm := classNorm
  meshSize := meshSize
  α := α
  C := C
  C' := 0
  approx x hx N t ht := by
    rw [(S.toApprox K hK).S_eq_waveGroup ht.1]
    change ‖H.waveGroup.S t x - (S.B N).starProjection (H.waveGroup.S t x)‖ ≤ _
    rw [← S.waveGroup_starProjection, ← _root_.map_sub, H.isIsometric_waveGroup t]
    exact hrate x hx N
  consistency x _ N t _ := by
    change ‖(S.comparison K hK T).defect x N t‖ ≤ _
    rw [comparison_defect, norm_zero]; simp

end ReducingFamily

end Feec.HilbertComplex
