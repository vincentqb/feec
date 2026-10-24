module

public import Feec.HilbertComplex.Approximation.ApproxConforming
public import Feec.HilbertComplex.Approximation.ConstrainedFEEC
public import Feec.Models.Torus.DeRhamGalerkin
public import Feec.Models.Torus.BGG
public import Feec.Models.Cube.MirrorBGG

/-!
# Spectral discretizations of the Einstein–Bianchi BGG complex

A **spectral family** of a Hilbert complex `H` (`Feec.Instances.SpectralFamily`) is a
sequence of finite-dimensional **reducing** subcomplexes `B_N` whose orthogonal projections
converge strongly to the identity. Each `B_N` is a subcomplex (a finite-dimensional reducing
subspace lies in the domains, `Feec.Models.Torus.DeRham.le_domain_of_isReducingPair`), its
orthogonal projection is a cochain projection of norm `1` (it commutes with `d`), and the
approximation property in `W` is the strong convergence. So every spectral family, together with a
closed constraint `K`, is a constrained FEEC discretization (`SpectralFamily.toFEEC`), and the
constrained FEEC theorem applies to it. Spectral families pull back along scaled embeddings whose
range the projections preserve (`SpectralFamily.comap`).

**Through the approximating FEEC theorem.** A spectral family is also a reducing family
(`SpectralFamily.toReducingFamily`: the bands `∏ B_N ⊆ D(L)` are reducing, `L` is bounded on
them, `SpectralFamily.waveBand`), so the spectral method is an approximating FEEC discretization
(`Feec.HilbertComplex.ReducingFamily.toApprox`, exact on the bands, core `W`, zero consistency
defect) and the verdict of `Feec.HilbertComplex.approxFEEC` applies. A truncation estimate
`‖x - P_N x‖ ≤ C hᵅ ‖x‖_c` gives, through `dissipFEEC_rate` (`C' = 0`), the **time-uniform** rate
`‖e^{tL} x - ι_N e^{tL_N} π_N x‖ ≤ C hᵅ ‖x‖_c` for all `t ≥ 0`
(`norm_sub_sol_le_of_truncation`, residual `infDist_sol_le_of_truncation`). The constrained FEEC
discretization `SpectralFamily.toFEEC` is the other reading, the special case `ιₕ` = inclusion
(`ConstrainedFEEC.toApprox`), with the rate `(1 + C_P)(1 + 2t)` of `ConstrainedFEEC.rate_le`.

**Rates.** For a spectral family the projection `P_N` commutes with `L` and with `e^{tL}`, so the
graph-norm error of the truncation of the orbit `e^{tL} ξ₀` is controlled by the truncation errors
of `ξ₀` and `L ξ₀` (`SpectralFamily.exists_mem_graphSub_le`). The data whose truncation errors of
`ξ₀`, `L ξ₀`, `L² ξ₀` decay like `(N + 1)^{-α}` form a rate class of the constrained FEEC theorem
on every time horizon (`SpectralFamily.rateClass`), which contains every band-limited datum of `D(L²)` for every `α`
(`SpectralFamily.mem_rateData_of_mem`); a tail bound `tail_N ≤ (N + 1)^{-α} B` gives membership
with norm `≤ B` (`SpectralFamily.mem_rateData_of_tail_le`).

**Instances** (namespace `Feec.Instances.EinsteinBianchi`).

* `bandFamily`: the Fourier bands `|n|_∞ ≤ N` of the periodic BGG complex (5.1) on `𝕋³` (the
  Fourier spectral method); `torusApprox`, `torusCore` and the headlines
  `einsteinBianchi_torus_approxFEEC` (`approxFEEC`; the discretization `torusFEEC` of
  `Feec.Instances.EinsteinBianchi` is `bandFamily.toFEEC (totalSub constraint) isClosed_totalSub`);
* `bandFamilyQ`: their pull-back to the BGG complex on the cube `Q = (0, ½)³` with mirror boundary
  conditions (cosine–sine bands, through the mirror extensions: the mirror action preserves the
  bands, `act_mem_band`); `mirrorApprox`, `mirrorCore`, `einsteinBianchi_mirror_approxFEEC`
  (`mirrorFEEC`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §4.6 (subcomplexes), §4.12–4.13 (Galerkin approximation of the Hodge wave equation), Ch. 6
* [D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to numerical stability*][AFW2010],
  §3.3 (approximation property, bounded cochain projections)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace Topology
open Set Filter MeasureTheory LinearPMap Metric

@[expose] public noncomputable section

namespace Feec.Instances

open Feec.HilbertComplex

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι} {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)] [∀ i, CompleteSpace (W i)]

/-! ### Truncation rates of reducing families through the approximating FEEC theorem -/

section Truncation

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] {H : HilbertComplex 𝕜 c W}
  {κ : Type*} (S : ReducingFamily H κ) (K : Submodule 𝕜 (PiLp 2 W))
  (hK : IsClosed (K : Set (PiLp 2 W)))

/-- **The time-uniform rate of a spectral Galerkin method**, read off the rate of the
approximating FEEC theorem (`dissipFEEC_rate` for `ReducingFamily.rateClass`, `C' = 0`, from
`v_N = π_N ξ₀`): a truncation estimate `‖x - P_N x‖ ≤ C hᵅ ‖x‖_c` on a set of data gives
`‖e^{tL} x - ι_N e^{tL_N} π_N x‖ ≤ C hᵅ ‖x‖_c` for every `t ≥ 0`. -/
theorem norm_sub_sol_le_of_truncation {Data : Set (PiLp 2 W)} {classNorm : PiLp 2 W → ℝ}
    {meshSize : κ → ℝ} {α C : ℝ}
    (hrate : ∀ x ∈ Data, ∀ N, ‖x - (S.B N).starProjection x‖ ≤ C * meshSize N ^ α * classNorm x)
    {x : PiLp 2 W} (hx : x ∈ Data) (N : κ) {t : ℝ} (ht : 0 ≤ t) :
    ‖H.waveGroup.S t x - (S.toApprox K hK).sol N ((S.B N).orthogonalProjectionOnto x) t‖ ≤
      C * meshSize N ^ α * classNorm x := by
  set R := S.rateClass K hK t Data classNorm meshSize α C hrate
  have h := dissipFEEC_rate _ R hx N (R.p x N 0) ⟨ht, le_rfl⟩
  rw [ApproxFEEC.S_apply _ ht, sub_self, norm_zero, mul_zero, add_zero] at h
  have hp : R.p x N 0 = (S.B N).orthogonalProjectionOnto x := by
    change (S.B N).orthogonalProjectionOnto (H.waveGroup.S 0 x) = _
    rw [C0Group.S_zero_apply]
  rw [hp] at h
  refine h.trans_eq ?_
  change (C + ‖(S.toApprox K hK).incl N‖ * 0 * t) * (meshSize N ^ α * classNorm x) = _
  ring

/-- **The time-uniform rate of the constraint residual** of a spectral Galerkin method (reducing
`K`, datum in `K`), from `dissipFEEC_residual_le`. -/
theorem infDist_sol_le_of_truncation (hKr : H.wave.IsReducing K) {Data : Set (PiLp 2 W)}
    {classNorm : PiLp 2 W → ℝ} {meshSize : κ → ℝ} {α C : ℝ}
    (hrate : ∀ x ∈ Data, ∀ N, ‖x - (S.B N).starProjection x‖ ≤ C * meshSize N ^ α * classNorm x)
    {x : PiLp 2 W} (hx : x ∈ Data) (hxK : x ∈ K) (N : κ) {t : ℝ} (ht : 0 ≤ t) :
    infDist ((S.toApprox K hK).sol N ((S.B N).orthogonalProjectionOnto x) t)
        (K : Set (PiLp 2 W)) ≤ C * meshSize N ^ α * classNorm x :=
  (dissipFEEC_residual_le _ ((dissipFEEC_propagates_iff _).2.2.1 hKr).1 hxK N _ ht).trans
    (by rw [ApproxFEEC.S_apply _ ht]; exact norm_sub_sol_le_of_truncation S K hK hrate hx N ht)

end Truncation

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
  le_domain i j :=
    Models.Torus.DeRham.le_domain_of_isReducingPair ((S.reducing N).reduces i j) (H.dense i j)
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

/-- **The constrained FEEC discretization of a spectral family** with a closed constraint `K`:
`V_N = B_N`, `π_N` the orthogonal projections (norm `1`), along `N → ∞`. -/
def toFEEC (K : Submodule 𝕜 (PiLp 2 W)) (hK : IsClosed (K : Set (PiLp 2 W))) :
    ConstrainedFEEC H ℕ where
  K := K
  isClosed_K := hK
  l := atTop
  V := S.sub
  finiteDimensional N i := inferInstanceAs (FiniteDimensional 𝕜 (S.B N i))
  π := S.proj
  bound_π := ⟨1, fun N i x => by
    rw [one_mul]; exact Submodule.norm_starProjection_apply_le (S.B N i) x⟩
  dense x δ hδ := by
    filter_upwards [Metric.tendsto_nhds.1 (S.tendsto_totalProj x) δ hδ] with N hN
    refine ⟨totalProj (S.B N) x, totalProj_mem x, ?_⟩
    rwa [dist_comm, dist_eq_norm] at hN

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
  exact Models.Torus.DeRham.le_domain_of_isReducingPair (S.isReducing_wave M)
    H.isSkewAdjoint_wave.dense_domain

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

open Feec.HodgeWave Feec.Variational

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

/-- **A spectral family is a reducing family** (`Feec.HilbertComplex.ReducingFamily`): the bands
`∏ B_N` are finite-dimensional reducing subspaces in `D(L)` on which `L` is bounded, and their
projections converge strongly to `1`. -/
def toReducingFamily : ReducingFamily H ℕ where
  B N := totalSub (S.B N)
  l := atTop
  isReducing := S.isReducing_wave
  le_domain := S.totalSub_le_domain
  bounded N := ⟨‖S.waveBand N‖, fun x _ hxB => (S.waveBand N).le_opNorm ⟨x, hxB⟩⟩
  tendsto := S.tendsto_starProjection

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- **The time-uniform spectral rate**, read off the rate of the approximating FEEC theorem
(`dissipFEEC_rate`, with `C' = 0` and `vₙ = πₙ ξ₀`): for data in the approximation class of
order `α`, `‖e^{tL} ξ₀ - ιₙ e^{tLₙ} πₙ ξ₀‖ ≤ (N + 1)^{-α} ‖ξ₀‖_α` for all `t ≥ 0`. -/
theorem norm_sub_sol_le (K : Submodule 𝕜 (PiLp 2 W)) (hK : IsClosed (K : Set (PiLp 2 W)))
    {α : ℝ} {x : PiLp 2 W} (hx : x ∈ S.rateData α) (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖H.waveGroup.S t x - (S.toReducingFamily.toApprox K hK).sol N
        ((S.toReducingFamily.B N).orthogonalProjectionOnto x) t‖ ≤
      (1 / ((N : ℝ) + 1)) ^ α * S.rateNorm α x := by
  have h := norm_sub_sol_le_of_truncation S.toReducingFamily K hK
    (fun _ hx N => S.norm_sub_P_le_rateNorm hx N) hx N ht
  rwa [one_mul] at h

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

end Feec.Instances

namespace Feec.Instances.EinsteinBianchi

open Feec.HilbertComplex

/-! ### The Fourier bands of the periodic BGG complex -/

section Torus

open Feec.Fourier Feec.Fourier.BGG Feec.Models.Torus.BGG

/-- The band-limited fields `|n|_∞ ≤ N` of the periodic BGG complex. -/
abbrev band (N : ℕ) (i : Fin 3) : Submodule ℂ (Space i) :=
  (Fourier.Torus.symbolComplex bggFamily).band (Fourier.Torus.bandN N) i

instance (N : ℕ) (i : Fin 3) : (band N i).HasOrthogonalProjection :=
  Fourier.hasOrthogonalProjection_band _ (Fourier.Torus.finite_bandN N).measurableSet i

/-- **The Fourier spectral family of the periodic BGG complex** (5.1): the bands `|n|_∞ ≤ N`. -/
def bandFamily : SpectralFamily complex where
  B := band
  finiteDimensional N i := Fourier.finiteDimensional_band _ (Fourier.Torus.finite_bandN N) i
  mono N M h i u hu := by
    rw [Fourier.mem_band_iff] at hu ⊢
    filter_upwards [hu] with a ha hM
    exact ha fun hN => hM (Fourier.Torus.bandN_mono h hN)
  reducing N := Fourier.reducingSubcomplex_band _ (Fourier.Torus.finite_bandN N).measurableSet
  tendsto i x := Fourier.tendsto_starProjection_band _
    (fun N => (Fourier.Torus.finite_bandN N).measurableSet) Fourier.Torus.bandN_mono
    Fourier.Torus.exists_mem_bandN i x

end Torus

/-! ### The cosine–sine bands of the mirror BGG complex on the cube -/

section Mirror

open Feec.Fourier Feec.Fourier.GradCurl Feec.Fourier.BGG Feec.Models.Cube.MirrorBGG

theorem flipAt_mem_bandN {k : Fin 3} {n : Fin 3 → ℤ} {N : ℕ} :
    Models.Cube.MirrorExt.flipAt k n ∈ Fourier.Torus.bandN N ↔ n ∈ Fourier.Torus.bandN N := by
  simp only [Fourier.Torus.bandN, mem_ofPred_eq, Models.Cube.MirrorExt.flipAt_apply]
  refine forall_congr' fun j => ?_
  split_ifs <;> simp

/-- **The mirror action preserves the Fourier bands** (`|flip_k n|_∞ = |n|_∞`). -/
theorem act_mem_band (N : ℕ) (g : Multiplicative (Fin 3 → ZMod 2)) (i : Fin 3)
    {x : Feec.Models.Torus.BGG.Space i} (hx : x ∈ band N i) : action.act g i x ∈ band N i := by
  refine symmetries.act_mem_fibreSub
    (K := fun i n => bandFibre (𝕜 := ℂ) (E := ShortHilbertComplex.W3 ℂ Mat VM)
      (Fourier.Torus.bandN N) i n) (fun k i n v hv => ?_) g i hx
  change v ∈ bandFibre _ i (Models.Cube.MirrorExt.flipAt k n) at hv
  by_cases hn : n ∈ Fourier.Torus.bandN N
  · simp [bandFibre, hn]
  · have hn' : Models.Cube.MirrorExt.flipAt k n ∉ Fourier.Torus.bandN N := flipAt_mem_bandN.not.2 hn
    have hv0 : v = 0 := by simpa [bandFibre, hn'] using hv
    simp [bandFibre, hn, hv0]

/-- The band projections preserve the range of the mirror extensions (the fixed fields). -/
theorem exists_J_eq_starProjection_band (N : ℕ) (i : Fin 3) (x : SpaceQ i) :
    ∃ y, embeddingQ.J i y = (band N i).starProjection (embeddingQ.J i x) := by
  have hx : J i x ∈ action.fixed i := range_J i ▸ LinearMap.mem_range_self _ x
  have h := action.starProjection_mem_fixed (fun g y hy => act_mem_band N g i hy) hx
  rw [← range_J] at h
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy⟩

/-- **The cosine–sine spectral family of the mirror BGG complex on `Q`**: the pull-back of the
Fourier bands along the mirror extensions. -/
def bandFamilyQ : SpectralFamily complexQ :=
  bandFamily.comap embeddingQ exists_J_eq_starProjection_band

end Mirror

/-! ### The spectral EB discretizations through the approximating FEEC theorem -/

section TorusApprox

open Feec.Models.Torus.BGG

/-- The Fourier bands `|n|_∞ ≤ N` of the periodic BGG complex as a reducing family. -/
abbrev torusBands : ReducingFamily complex ℕ := bandFamily.toReducingFamily

/-- **The Fourier spectral method for the EB system on `𝕋³` as an approximating FEEC
discretization**: `X_N` the band `∏ B_N`, `ι_N` its inclusion, `π_N` the orthogonal projection,
`L_N = L|_{B_N}`, with the TSD constraint. -/
def torusApprox : ApproxFEEC complex ℕ :=
  torusBands.toApprox (totalSub constraint) isClosed_totalSub

/-- Its core: all of `W`, with zero consistency defect. -/
def torusCore : torusApprox.Core := torusBands.toCore (totalSub constraint) isClosed_totalSub

theorem torusApprox_isReducing : complex.wave.IsReducing (totalSub constraint) :=
  reducingSubcomplex.isReducing_wave

/-- **The approximating FEEC theorem for the EB system on `𝕋³`** (Fourier spectral method): the
verdict of `approxFEEC` (well-posedness, propagation iff reducing, convergence from every
convergent family of initial values, rates, constraint residuals). [QuennevilleBelair2015],
Thm 4.14, Prop 4.17, Ch. 6 -/
theorem einsteinBianchi_torus_approxFEEC : torusApprox.Verdict torusCore := approxFEEC _ _

end TorusApprox

section MirrorApprox

open Feec.Models.Cube.MirrorBGG

/-- The cosine–sine bands of the mirror BGG complex on `Q` as a reducing family. -/
abbrev mirrorBands : ReducingFamily complexQ ℕ := bandFamilyQ.toReducingFamily

/-- **The cosine–sine spectral method for the EB system on the cube with mirror boundary
conditions as an approximating FEEC discretization**, with the TSD constraint `tsdQ`. -/
def mirrorApprox : ApproxFEEC complexQ ℕ :=
  mirrorBands.toApprox (totalSub tsdQ) isClosed_totalSub

/-- Its core: all of `W`, with zero consistency defect. -/
def mirrorCore : mirrorApprox.Core := mirrorBands.toCore (totalSub tsdQ) isClosed_totalSub

theorem mirrorApprox_isReducing : complexQ.wave.IsReducing (totalSub tsdQ) :=
  reducingSubcomplexQ.isReducing_wave

/-- **The approximating FEEC theorem for the EB system on the cube with mirror boundary
conditions** (cosine–sine spectral method). [QuennevilleBelair2015], Thm 4.14, Prop 4.17
(corrected), Ch. 6 -/
theorem einsteinBianchi_mirror_approxFEEC : mirrorApprox.Verdict mirrorCore := approxFEEC _ _

end MirrorApprox

end Feec.Instances.EinsteinBianchi
