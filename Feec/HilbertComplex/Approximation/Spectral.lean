module

public import Feec.HilbertComplex.Approximation.ApproxConforming
public import Feec.HilbertComplex.Transport

/-!
# Spectral methods: reducing families and spectral families

A **reducing family** (`Feec.HilbertComplex.ReducingFamily`) of a Hilbert complex `H` is a family
of closed subspaces `B_N ⊆ D(L)` of `W = ⊕ Wⁱ` that reduce the wave operator `L = 𝐝 - 𝐝*`, on
which `L` is bounded, and whose orthogonal projections `P_N` converge strongly to `1` (not
necessarily finite-dimensional: frequency balls on `ℝᵈ`). Its **spectral Galerkin method**
`ReducingFamily.toApprox` (`X_N = B_N` with the inner product of `W`, `ι_N` the inclusion,
`π_N = P_N`, `L_N = L|_{B_N}`) is an approximating FEEC discretization
(`Feec.HilbertComplex.ApproxFEEC`) without variational crime: it is exact on the bands
(`ReducingFamily.toApprox_sol`: `ι_N e^{tL_N} π_N x = P_N e^{tL} x`), its core is all of `W`
with zero consistency defect (`ReducingFamily.toCore`), and truncation estimates give rate
classes with `C' = 0` (`ReducingFamily.rateClass`).

**The FEEC theorem for reducing families** (`ReducingFamily.feec`, statement
`ReducingFamily.Verdict`): for every closed constraint `K`, the verdict of the approximating FEEC
theorem `approxFEEC` holds on all data, the error is the truncation error of the datum at every
time, `‖e^{tL} x - ι_N e^{tL_N} π_N x‖ = ‖x - P_N x‖` (so a truncation estimate
`‖x - P_N x‖ ≤ C hᵅ ‖x‖_c` is a time-uniform rate), and a constraint that reduces `L` and that the
truncations preserve is preserved exactly (identically zero residual).

A **spectral family** (`Feec.HilbertComplex.SpectralFamily`) is an increasing sequence of
finite-dimensional reducing subcomplexes `B_N` of `H` whose orthogonal projections converge
strongly to `1` (the Fourier bands of a symbol complex on a torus). It has two readings:

* a reducing family (`ReducingFamily.ofSpectral`: a finite-dimensional reducing subspace lies in
  the domain, `LinearPMap.IsReducingPair.le_domain`, and `L` is bounded on it), so the FEEC
  theorem for reducing families applies;
* a conforming family (`ConformingFamily.ofSpectral`: `V_N = B_N`, `π_N` the orthogonal
  projections, commuting with `d` and of norm `1`), so the constrained FEEC theorem applies
  (`SpectralFamily.toFEEC`), and on complexes over `ℕ` or `ℤ` the FEEC theorem
  (`Feec.HilbertComplex.ConformingFamily.feec`); there `P_N` commutes with `L` and `e^{tL}`, so the graph-norm
  truncation errors of the orbit are those of the datum (`SpectralFamily.exists_mem_graphSub_le`),
  and the data whose truncation errors of `x`, `L x`, `L² x` decay like `(N + 1)^{-α}` form rate
  classes on every horizon (`SpectralFamily.rateClass`), containing every band-limited datum
  (`SpectralFamily.mem_rateData_of_mem`).

Spectral families pull back along scaled embeddings whose range the projections preserve
(`SpectralFamily.comap`).

## Main definitions

* `ReducingFamily`, `ReducingFamily.toApprox`, `ReducingFamily.toCore`,
  `ReducingFamily.rateClass`, `ReducingFamily.Verdict`.
* `SpectralFamily`, `ReducingFamily.ofSpectral`, `ConformingFamily.ofSpectral`,
  `SpectralFamily.toFEEC`, `SpectralFamily.rateClass`, `SpectralFamily.comap`.

## Main results

* **`ReducingFamily.feec`**; `ReducingFamily.toApprox_sol`, `ReducingFamily.norm_sub_toApprox_sol`,
  `ReducingFamily.toApprox_sol_mem`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.6 (subcomplexes), §4.12–4.13 (Galerkin approximation of the Hodge wave equation)
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3 (approximation property, bounded cochain projections)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace Topology
open Set Filter LinearPMap Metric

@[expose] public noncomputable section

namespace Feec.HilbertComplex

open _root_.Feec.HodgeWave

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

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


/-- **The error is the truncation error of the datum**, at every time:
`‖e^{tL} x - ι_N e^{tL_N} π_N x‖ = ‖x - P_N x‖` (`P_N` commutes with the unitary group `e^{tL}`). -/
theorem norm_sub_toApprox_sol (K : Submodule 𝕜 (PiLp 2 W)) (hK : IsClosed (K : Set (PiLp 2 W)))
    (N : κ) (x : PiLp 2 W) (t : ℝ) :
    ‖H.waveGroup.S t x - (S.toApprox K hK).sol N ((S.toApprox K hK).proj N x) t‖ =
      ‖x - (S.B N).starProjection x‖ := by
  change ‖_ - (S.toApprox K hK).sol N ((S.B N).orthogonalProjectionOnto x) t‖ = _
  rw [S.toApprox_sol, ← S.waveGroup_starProjection, ← _root_.map_sub, H.isIsometric_waveGroup t]

/-- **Exact constraint preservation**: if `K` reduces `L` and the truncations `P_N` map `K` into
itself, the discrete solutions of data in `K` stay in `K` for every `N` and every `t ∈ ℝ`. -/
theorem toApprox_sol_mem {K : Submodule 𝕜 (PiLp 2 W)} (hK : IsClosed (K : Set (PiLp 2 W)))
    (hKr : H.wave.IsReducing K) (hP : ∀ N, ∀ x ∈ K, (S.B N).starProjection x ∈ K)
    {x : PiLp 2 W} (hx : x ∈ K) (N : κ) (t : ℝ) :
    (S.toApprox K hK).sol N ((S.toApprox K hK).proj N x) t ∈ K := by
  change (S.toApprox K hK).sol N ((S.B N).orthogonalProjectionOnto x) t ∈ K
  rw [S.toApprox_sol]
  exact hP N _ (C0Group.map_le_iff_forall.1
    ((H.isReducing_iff_waveGroup_invariant K).1 hKr) t x hx)

/-- **The conclusions of the FEEC theorem for a reducing family** (`ReducingFamily.feec`) with a
closed constraint `K`: those of the approximating FEEC theorem for the spectral Galerkin method
`toApprox` with the core `toCore` (all data, zero consistency defect), and the exactness of the
method on the bands. -/
structure Verdict (K : Submodule 𝕜 (PiLp 2 W)) (hK : IsClosed (K : Set (PiLp 2 W))) : Prop
    extends toApprox : (S.toApprox K hK).Verdict (S.toCore K hK) where
  /-- the method is exact on the bands: `ι_N e^{tL_N} π_N x = P_N e^{tL} x` -/
  sol_eq (N : κ) (x : PiLp 2 W) (t : ℝ) :
    (S.toApprox K hK).sol N ((S.toApprox K hK).proj N x) t =
      (S.B N).starProjection (H.waveGroup.S t x)
  /-- the error is the truncation error of the datum, at every time:
  `‖e^{tL} x - ι_N e^{tL_N} π_N x‖ = ‖x - P_N x‖` -/
  norm_sub_sol (N : κ) (x : PiLp 2 W) (t : ℝ) :
    ‖H.waveGroup.S t x - (S.toApprox K hK).sol N ((S.toApprox K hK).proj N x) t‖ =
      ‖x - (S.B N).starProjection x‖
  /-- a constraint that reduces `L` and that the truncations map into itself is preserved
  exactly: the residual vanishes identically -/
  sol_mem (hKr : H.wave.IsReducing K) (hP : ∀ N, ∀ x ∈ K, (S.B N).starProjection x ∈ K)
    {x : PiLp 2 W} (hx : x ∈ K) (N : κ) (t : ℝ) :
    (S.toApprox K hK).sol N ((S.toApprox K hK).proj N x) t ∈ K

/-- **The FEEC theorem for reducing families.** For a reducing family `S` (closed reducing
subspaces `B_N ⊆ D(L)` on which `L` is bounded, with projections converging strongly to `1`) and
a closed constraint `K`, the spectral Galerkin method `X_N = B_N`, `π_N = P_N`, `L_N = L|_{B_N}`
satisfies the approximating FEEC theorem on all data (core `W`, zero consistency defect), is exact
on the bands (`ι_N e^{tL_N} π_N x = P_N e^{tL} x`), so its error is the truncation error
`‖x - P_N x‖` of the datum at every time, and it preserves exactly every reducing constraint that
the truncations preserve. [QuennevilleBelair2015], §4.12–4.13 -/
theorem feec (K : Submodule 𝕜 (PiLp 2 W)) (hK : IsClosed (K : Set (PiLp 2 W))) :
    S.Verdict K hK :=
  ⟨approxFEEC _ _, S.toApprox_sol K hK, S.norm_sub_toApprox_sol K hK, S.toApprox_sol_mem hK⟩

end ReducingFamily

/-! ### Spectral families -/

/-- A **spectral family** of a Hilbert complex `H`: finite-dimensional reducing subcomplexes `B_N`
whose orthogonal projections converge strongly to the identity (e.g. Fourier bands of a symbol
complex). See [QuennevilleBelair2015], §4.12–4.13. -/
structure SpectralFamily (H : HilbertComplex 𝕜 c W) where
  /-- the spaces of the family -/
  B : ℕ → ∀ i, Submodule 𝕜 (W i)
  [hasOrthogonalProjection : ∀ N i, (B N i).HasOrthogonalProjection]
  [finiteDimensional : ∀ N i, FiniteDimensional 𝕜 (B N i)]
  mono : ∀ ⦃N M⦄, N ≤ M → ∀ i, B N i ≤ B M i
  reducing : ∀ N, H.ReducingSubcomplex (B N)
  tendsto : ∀ i (x : W i), Tendsto (fun N => (B N i).starProjection x) atTop (𝓝 x)

attribute [instance] SpectralFamily.hasOrthogonalProjection SpectralFamily.finiteDimensional

namespace SpectralFamily

variable {H : HilbertComplex 𝕜 c W} (S : SpectralFamily H)

/-- The subcomplex `B_N`. -/
def sub (N : ℕ) : H.Subcomplex where
  V := S.B N
  le_domain i j := ((S.reducing N).reduces i j).le_domain (H.dense i j)
  mapsTo _ _ x hx := (S.reducing N).mapsTo ⟨x, _⟩ hx

instance (N : ℕ) (i : ι) : ((S.sub N).V i).HasOrthogonalProjection :=
  inferInstanceAs ((S.B N i).HasOrthogonalProjection)

/-- The bands `∏ B_N` are finite-dimensional. -/
instance finiteDimensional_totalSub (N : ℕ) : FiniteDimensional 𝕜 (totalSub (S.B N)) := by
  let f : totalSub (S.B N) →ₗ[𝕜] ∀ i, S.B N i :=
    { toFun := fun x i => ⟨(x : PiLp 2 W) i, x.2 i⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective f fun x y hxy => Subtype.ext (PiLp.ext fun i => ?_)
  exact congrArg Subtype.val (congrFun hxy i)

/-- The orthogonal projection onto `B_N`, a cochain projection. -/
def proj (N : ℕ) : (S.sub N).CochainProjection where
  π i := ((S.B N i).starProjection : W i →ₗ[𝕜] W i)
  mem i x := Submodule.starProjection_apply_mem (S.B N i) x
  proj i _ hx := (Submodule.starProjection_eq_self_iff (K := S.B N i)).2 hx
  comm i j x := ((S.reducing N).reduces i j).comm x

omit [Fintype ι] in
theorem tendsto_totalProj (x : PiLp 2 W) :
    Tendsto (fun N => totalProj (S.B N) x) atTop (𝓝 x) := by
  rw [show x = WithLp.toLp 2 (WithLp.ofLp x) from rfl]
  exact ((PiLp.continuous_toLp 2 _).tendsto _).comp
    (tendsto_pi_nhds.2 fun i => S.tendsto i (x i))

/-- **A spectral family is a conforming family**: `V_N = B_N`, `π_N` the orthogonal projections
(norm `1`), along `N → ∞`; `dist(x, B_N) ≤ ‖x - P_N x‖ → 0`. -/
def _root_.Feec.HilbertComplex.ConformingFamily.ofSpectral : ConformingFamily H ℕ where
  l := atTop
  V := S.sub
  finiteDimensional N i := inferInstanceAs (FiniteDimensional 𝕜 (S.B N i))
  π := S.proj
  bound_π := ⟨1, fun N i x => by
    rw [one_mul]; exact Submodule.norm_starProjection_apply_le (S.B N i) x⟩
  approx i y := (tendsto_infDist_submodule_iff _ y).2 fun ε hε => by
    filter_upwards [Metric.tendsto_nhds.1 (S.tendsto i y) ε hε] with N hN
    exact ⟨_, Submodule.starProjection_apply_mem (S.B N i) y,
      by rwa [dist_comm, dist_eq_norm] at hN⟩

/-- **The constrained FEEC discretization of a spectral family** with a closed constraint `K`:
`V_N = B_N`, `π_N` the orthogonal projections (norm `1`), along `N → ∞`. -/
def toFEEC (K : Submodule 𝕜 (PiLp 2 W)) (hK : IsClosed (K : Set (PiLp 2 W))) :
    ConstrainedFEEC H ℕ :=
  (ConformingFamily.ofSpectral S).withConstraint K hK

/-! ### Rates: data with algebraically decaying truncation errors -/

section Rate

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- The total truncation `P_N = P_{∏ B_N}`. -/
abbrev P (N : ℕ) : PiLp 2 W →L[𝕜] PiLp 2 W := (totalSub (S.B N)).starProjection

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem P_mem (N : ℕ) (x : PiLp 2 W) : S.P N x ∈ totalSub (S.B N) :=
  Submodule.starProjection_apply_mem _ x

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem P_mem_domain (N : ℕ) (x : PiLp 2 W) : S.P N x ∈ H.totalD.domain :=
  fun i j => (S.sub N).le_domain i j (S.P_mem N x i)

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem isReducing_wave (N : ℕ) : H.wave.IsReducing (totalSub (S.B N)) :=
  (S.reducing N).isReducing_wave

/-- `P_N` commutes with the wave group. -/
theorem waveGroup_P (N : ℕ) (t : ℝ) (x : PiLp 2 W) :
    H.waveGroup.S t (S.P N x) = S.P N (H.waveGroup.S t x) :=
  H.isIsometric_waveGroup.S_starProjection (fun s _ hy => (S.reducing N).waveGroup_mem s hy) t x

/-- The truncation error is conserved by the wave group. -/
theorem norm_waveGroup_sub_P (N : ℕ) (t : ℝ) (x : PiLp 2 W) :
    ‖H.waveGroup.S t x - S.P N (H.waveGroup.S t x)‖ = ‖x - S.P N x‖ := by
  rw [← S.waveGroup_P, ← _root_.map_sub]
  exact H.isIsometric_waveGroup t _

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
/-- **The graph-norm truncation error** of `y ∈ D(L)`: for every `v ∈ Γ(𝐝)` over `y` there is
`w ∈ B_N` with `‖v - w‖ ≤ ‖y - P_N y‖ + ‖L y - P_N L y‖` (`‖𝐝 z‖ ≤ ‖L z‖`, and `P_N` commutes
with `𝐝` and `L`). -/
theorem exists_mem_graphSub_le (N : ℕ) {y : PiLp 2 W} (hy : y ∈ H.wave.domain)
    (v : H.totalD.GraphSpace) (hv : H.totalD.graphFst v = y) :
    ∃ w ∈ (S.sub N).graphSub, ‖v - w‖ ≤
      ‖y - S.P N y‖ + ‖H.wave ⟨y, hy⟩ - S.P N (H.wave ⟨y, hy⟩)‖ := by
  obtain ⟨z, rfl, -, -⟩ := H.totalD.exists_toGraphSpace_eq v
  have hzy : (z : PiLp 2 W) = y := hv
  subst hzy
  set w : H.totalD.GraphSpace := H.totalD.toGraphSpace ⟨S.P N z, S.P_mem_domain N z⟩
  refine ⟨w, fun i => S.P_mem N z i, ?_⟩
  have hR := S.isReducing_wave N
  have hPy : S.P N z ∈ H.wave.domain := hR.proj_mem ⟨z, hy⟩
  have hu : (z : PiLp 2 W) - S.P N z ∈ H.wave.domain := H.wave.domain.sub_mem hy hPy
  have hLu : H.wave ⟨_, hu⟩ = H.wave ⟨z, hy⟩ - S.P N (H.wave ⟨z, hy⟩) := by
    rw [← hR.comm ⟨z, hy⟩, ← LinearPMap.map_sub]; rfl
  have e1 : H.totalD.graphFst (H.totalD.toGraphSpace z - w) = (z : PiLp 2 W) - S.P N z := by
    rw [H.totalD.graphFst.map_sub]; rfl
  have e2 : H.totalD.graphSnd (H.totalD.toGraphSpace z - w) =
      H.totalD ⟨_, (hu : _ ∈ H.wave.domain).1⟩ := by
    rw [H.totalD.graphSnd.map_sub, graphSnd_toGraphSpace, graphSnd_toGraphSpace,
      ← LinearPMap.map_sub]; rfl
  have hsq := Feec.HodgeWave.norm_sq_graphSpace (H.totalD.toGraphSpace z - w)
  rw [e1, e2] at hsq
  have hw := H.norm_wave_sq ⟨_, hu⟩
  rw [hLu] at hw
  set a := ‖(z : PiLp 2 W) - S.P N z‖
  set b := ‖H.wave ⟨z, hy⟩ - S.P N (H.wave ⟨z, hy⟩)‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hd : ‖H.totalD ⟨_, (hu : _ ∈ H.wave.domain).1⟩‖ ^ 2 ≤ b ^ 2 := by
    rw [hw]; nlinarith [norm_nonneg (H.dual.totalD ⟨_, (hu : _ ∈ H.wave.domain).2⟩)]
  have hn := norm_nonneg (H.totalD.toGraphSpace z - w)
  nlinarith

/-- The **truncation error** of `x`, `L x` and `L² x` at level `N`. -/
def tail (N : ℕ) (x : PiLp 2 W) : ℝ :=
  ‖x - S.P N x‖ + ‖H.waveExt x - S.P N (H.waveExt x)‖ +
    ‖H.waveExt (H.waveExt x) - S.P N (H.waveExt (H.waveExt x))‖

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem tail_eq (N : ℕ) {x : PiLp 2 W} (hx : x ∈ H.wave.domain)
    (hLx : H.wave ⟨x, hx⟩ ∈ H.wave.domain) :
    S.tail N x = ‖x - S.P N x‖ + ‖H.wave ⟨x, hx⟩ - S.P N (H.wave ⟨x, hx⟩)‖ +
      ‖H.wave ⟨_, hLx⟩ - S.P N (H.wave ⟨_, hLx⟩)‖ := by
  rw [tail, waveExt_of_mem hx, waveExt_of_mem hLx]

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem tail_nonneg (N : ℕ) (x : PiLp 2 W) : 0 ≤ S.tail N x := by
  unfold tail; positivity

/-- **The approximation class of order `α`**: data `x ∈ D(L²)` whose truncation errors of `x`,
`L x`, `L² x` are `O((N + 1)^{-α})`. -/
def rateData (α : ℝ) : Set (PiLp 2 W) :=
  {x | x ∈ H.wave.domain ∧ H.waveExt x ∈ H.wave.domain ∧
    BddAbove (range fun N : ℕ => ((N : ℝ) + 1) ^ α * S.tail N x)}

/-- The norm of the approximation class: `sup_N (N + 1)^α (‖(1 - P_N) x‖ + ‖(1 - P_N) L x‖ +
‖(1 - P_N) L² x‖)`. -/
def rateNorm (α : ℝ) (x : PiLp 2 W) : ℝ := ⨆ N : ℕ, ((N : ℝ) + 1) ^ α * S.tail N x

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem tail_le_rateNorm {α : ℝ} {x : PiLp 2 W} (hx : x ∈ S.rateData α) (N : ℕ) :
    S.tail N x ≤ 1 * (1 / ((N : ℝ) + 1)) ^ α * S.rateNorm α x := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hle : ((N : ℝ) + 1) ^ α * S.tail N x ≤ S.rateNorm α x := le_ciSup hx.2.2 N
  have hp : 0 < ((N : ℝ) + 1) ^ α := Real.rpow_pos_of_pos hN α
  rw [one_mul, Real.div_rpow zero_le_one hN.le, Real.one_rpow, one_div, inv_mul_eq_div,
    le_div_iff₀ hp, mul_comm]
  exact hle

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
/-- **Membership in the approximation class from a tail bound**: if `x ∈ D(L²)` and
`tail_N(x) ≤ (N + 1)^{-α} B` for all `N`, then `x` lies in the class of order `α` with norm
`≤ B`. -/
theorem mem_rateData_of_tail_le {α B : ℝ} {x : PiLp 2 W} (hx : x ∈ H.wave.domain)
    (hLx : H.waveExt x ∈ H.wave.domain)
    (h : ∀ N : ℕ, S.tail N x ≤ (1 / ((N : ℝ) + 1)) ^ α * B) :
    x ∈ S.rateData α ∧ S.rateNorm α x ≤ B := by
  have htail : ∀ N : ℕ, ((N : ℝ) + 1) ^ α * S.tail N x ≤ B := fun N => by
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hp : ((N : ℝ) + 1) ^ α * (1 / ((N : ℝ) + 1)) ^ α = 1 := by
      rw [← Real.mul_rpow hN.le (by positivity), mul_one_div_cancel hN.ne', Real.one_rpow]
    calc ((N : ℝ) + 1) ^ α * S.tail N x
        ≤ ((N : ℝ) + 1) ^ α * ((1 / ((N : ℝ) + 1)) ^ α * B) :=
          mul_le_mul_of_nonneg_left (h N) (Real.rpow_pos_of_pos hN α).le
      _ = B := by rw [← mul_assoc, hp, one_mul]
  exact ⟨⟨hx, hLx, ⟨B, by rintro _ ⟨N, rfl⟩; exact htail N⟩⟩, ciSup_le htail⟩

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
/-- The truncation error of `x` is bounded by its class norm: `‖x - P_N x‖ ≤ (N + 1)^{-α} ‖x‖_α`. -/
theorem norm_sub_P_le_rateNorm {α : ℝ} {x : PiLp 2 W} (hx : x ∈ S.rateData α) (N : ℕ) :
    ‖x - S.P N x‖ ≤ 1 * (1 / ((N : ℝ) + 1)) ^ α * S.rateNorm α x := by
  have h1 : ‖x - S.P N x‖ ≤ S.tail N x := by
    unfold tail
    linarith [norm_nonneg (H.waveExt x - S.P N (H.waveExt x)),
      norm_nonneg (H.waveExt (H.waveExt x) - S.P N (H.waveExt (H.waveExt x)))]
  exact h1.trans (S.tail_le_rateNorm hx N)

/-- **The rate class of a spectral discretization** on the horizon `[0, T]`: the approximation
class of order `α`, with `h_N = 1/(N + 1)`, `C = 1` and the norm `rateNorm α`. -/
def rateClass (K : Submodule 𝕜 (PiLp 2 W)) (hK : IsClosed (K : Set (PiLp 2 W))) (α T : ℝ) :
    (S.toFEEC K hK).RateClass T where
  Data := S.rateData α
  classNorm := S.rateNorm α
  meshSize N := 1 / ((N : ℝ) + 1)
  α := α
  C := 1
  mem_domain _ hx := hx.1
  mem_domain_sq x hx hxD := by rw [← waveExt_of_mem hx]; exact hxD.2.1
  approx x hxD N t _ v hv := by
    have hLx : H.wave ⟨x, hxD.1⟩ ∈ H.wave.domain := by
      rw [← waveExt_of_mem hxD.1]; exact hxD.2.1
    obtain ⟨w, hw, hle⟩ := S.exists_mem_graphSub_le N (waveGroup_mem_domain H hxD.1 t) v hv
    refine ⟨w, hw, hle.trans (le_trans ?_ (S.tail_le_rateNorm hxD N))⟩
    rw [wave_waveGroup hxD.1 t, S.norm_waveGroup_sub_P, S.norm_waveGroup_sub_P,
      S.tail_eq N hxD.1 hLx]
    have := norm_nonneg (H.wave ⟨_, hLx⟩ - S.P N (H.wave ⟨_, hLx⟩))
    linarith
  approx_deriv x hx hxD N t _ v hv := by
    have hLx : H.wave ⟨x, hx⟩ ∈ H.wave.domain := by
      rw [← waveExt_of_mem hx]; exact hxD.2.1
    obtain ⟨w, hw, hle⟩ := S.exists_mem_graphSub_le N (waveGroup_mem_domain H hLx t) v hv
    refine ⟨w, hw, hle.trans (le_trans ?_ (S.tail_le_rateNorm hxD N))⟩
    rw [wave_waveGroup hLx t, S.norm_waveGroup_sub_P, S.norm_waveGroup_sub_P,
      S.tail_eq N hx hLx]
    have := norm_nonneg (x - S.P N x)
    linarith

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
/-- A finite-dimensional reducing subspace of the wave operator lies in `D(L)`. -/
theorem totalSub_le_domain (M : ℕ) : totalSub (S.B M) ≤ H.wave.domain := by
  exact (S.isReducing_wave M).le_domain H.isSkewAdjoint_wave.dense_domain

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
/-- **Band-limited data are in every approximation class**: if `x ∈ ∏ B_M`, then `x ∈ D(L²)` and
the truncation errors vanish for `N ≥ M`. -/
theorem mem_rateData_of_mem {M : ℕ} {x : PiLp 2 W} (hx : x ∈ totalSub (S.B M)) (α : ℝ) :
    x ∈ S.rateData α := by
  have hR := S.isReducing_wave M
  have hxD := S.totalSub_le_domain M hx
  have hLx : H.waveExt x ∈ totalSub (S.B M) := by
    rw [waveExt_of_mem hxD]; exact hR.mapsTo ⟨x, hxD⟩ hx
  have hLxD := S.totalSub_le_domain M hLx
  have hLLx : H.waveExt (H.waveExt x) ∈ totalSub (S.B M) := by
    rw [waveExt_of_mem hLxD]; exact hR.mapsTo ⟨_, hLxD⟩ hLx
  refine ⟨hxD, hLxD, ?_⟩
  have h0 : ∀ N, M ≤ N → S.tail N x = 0 := fun N hN => by
    have hmono : totalSub (S.B M) ≤ totalSub (S.B N) := totalSub_mono (S.mono hN)
    simp only [tail, P, Submodule.starProjection_eq_self_iff.2 (hmono hx),
      Submodule.starProjection_eq_self_iff.2 (hmono hLx),
      Submodule.starProjection_eq_self_iff.2 (hmono hLLx), sub_self, norm_zero, add_zero]
  refine ⟨∑ n ∈ Finset.range M, ((n : ℝ) + 1) ^ α * S.tail n x, ?_⟩
  rintro _ ⟨N, rfl⟩
  have hnn : ∀ n ∈ Finset.range M, 0 ≤ ((n : ℝ) + 1) ^ α * S.tail n x := fun n _ =>
    mul_nonneg (Real.rpow_nonneg (by positivity) α) (S.tail_nonneg n x)
  by_cases hN : N < M
  · exact Finset.single_le_sum (f := fun n : ℕ => ((n : ℝ) + 1) ^ α * S.tail n x) hnn
      (Finset.mem_range.2 hN)
  · dsimp only
    rw [h0 N (not_lt.1 hN), mul_zero]
    exact Finset.sum_nonneg hnn

end Rate

/-! ### Spectral families are reducing families -/

section Reducing

/-- `L` on the band `∏ B_N`, a bounded operator (the band is finite-dimensional). -/
def waveBand (N : ℕ) : totalSub (S.B N) →L[𝕜] PiLp 2 W :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => H.wave ⟨x, S.totalSub_le_domain N x.2⟩
      map_add' := fun x y => by
        change H.wave (⟨x, S.totalSub_le_domain N x.2⟩ + ⟨y, S.totalSub_le_domain N y.2⟩) = _
        rw [LinearPMap.map_add]
      map_smul' := fun a x => by
        change H.wave (a • ⟨x, S.totalSub_le_domain N x.2⟩) = _
        rw [LinearPMap.map_smul]; rfl }

/-- The orthogonal projections onto the bands `∏ B_N` converge strongly to `1`. -/
theorem tendsto_starProjection (x : PiLp 2 W) :
    Tendsto (fun N => (totalSub (S.B N)).starProjection x) atTop (𝓝 x) :=
  (S.tendsto_totalProj x).congr fun N => PiLp.ext fun i => by
    rw [totalSub_starProjection_apply, totalProj_apply]

/-- **A spectral family is a reducing family**: the bands `∏ B_N` are finite-dimensional reducing
subspaces in `D(L)` on which `L` is bounded, and their projections converge strongly to `1`. -/
def _root_.Feec.HilbertComplex.ReducingFamily.ofSpectral : ReducingFamily H ℕ where
  B N := totalSub (S.B N)
  l := atTop
  isReducing := S.isReducing_wave
  le_domain := S.totalSub_le_domain
  bounded N := ⟨‖S.waveBand N‖, fun x _ hxB => (S.waveBand N).le_opNorm ⟨x, hxB⟩⟩
  tendsto := S.tendsto_starProjection

end Reducing

/-! ### Pull-back along scaled embeddings -/

section Comap

variable {W' : ι → Type*} [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace 𝕜 (W' i)]
  [∀ i, CompleteSpace (W' i)] {H' : HilbertComplex 𝕜 c W'}

omit [Fintype ι] in
/-- A scaled embedding scales norms by `√(scale i)`. -/
theorem norm_scaledEmbedding_J (E : ScaledEmbedding H H') (i : ι) (x : W i) :
    ‖E.J i x‖ = √(E.scale i) * ‖x‖ := by
  have h := E.inner_J i x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖E.J i x‖ ^ 2 = E.scale i * ‖x‖ ^ 2 := by exact_mod_cast h
  rw [← Real.sqrt_sq (norm_nonneg (E.J i x)), h', Real.sqrt_mul (E.scale_pos i).le,
    Real.sqrt_sq (norm_nonneg x)]

/-- **Spectral families pull back along scaled embeddings** whose range the projections
preserve: `J⁻¹ B'_N`. -/
def comap (E : ScaledEmbedding H H') (S : SpectralFamily H')
    (hS : ∀ N i x, ∃ y, E.J i y = (S.B N i).starProjection (E.J i x)) : SpectralFamily H where
  B N i := (S.B N i).comap (E.J i : W i →ₗ[𝕜] W' i)
  hasOrthogonalProjection N i := E.comap_hasOrthogonalProjection i _
  finiteDimensional N i := by
    let f : (S.B N i).comap (E.J i : W i →ₗ[𝕜] W' i) →ₗ[𝕜] S.B N i :=
      (E.J i : W i →ₗ[𝕜] W' i).restrict fun _ hx => hx
    refine Module.Finite.of_injective f fun x y hxy => Subtype.ext (E.J_injective i ?_)
    exact congrArg Subtype.val hxy
  mono _ _ h i := Submodule.comap_mono (S.mono h i)
  reducing N := E.reducingSubcomplex_comap (S.reducing N) (hS N)
  tendsto i x := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h := (tendsto_iff_norm_sub_tendsto_zero.1 (S.tendsto i (E.J i x))).const_mul
      (√(E.scale i))⁻¹
    rw [mul_zero] at h
    refine h.congr fun N => ?_
    have hs : 0 < √(E.scale i) := Real.sqrt_pos.2 (E.scale_pos i)
    rw [← E.starProjection_comap _ (hS N i), ← _root_.map_sub, norm_scaledEmbedding_J, ← mul_assoc,
      inv_mul_cancel₀ hs.ne', one_mul]

end Comap

end SpectralFamily

end Feec.HilbertComplex
