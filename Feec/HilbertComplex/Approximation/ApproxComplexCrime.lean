module

public import Feec.HilbertComplex.Approximation.ApproxComplex
public import Feec.HilbertComplex.Approximation.ApproxOrthogonal
public import Feec.HilbertComplex.Approximation.RitzResolvent

/-!
# Approximating families of discrete differential spaces with a cochain defect

Generalizations of the Holst–Stern discretizations ([HolstStern2012], §3) in which the reading
maps need not be cochain maps: discrete differentials independent of `𝐝`, with the inner-product
defect in the graph norm and a cochain defect. With consistent approximation, each is an
approximating FEEC discretization of the Hodge wave equation, with rates from complex-level
estimates.

## Main results

* `ApproxComplexCrime.Family.norm_sub_incl_load_le`: the Strang lemma.
* `ApproxComplexCrime.Family.inner_residual_eq`: the splitting of the residual.
* `approxFEEC_ofComplexCrime`: the approximating FEEC theorem for `ofComplexCrime`.
* `ApproxFEEC.ofComplexCrime_toCrime`: `ofComplex` is the cochain special case.
* `ApproxComplexCrime.error_le_of_split`: the error at order `min(α, β, γ)`.

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap Metric

@[expose] public noncomputable section

universe u

namespace Feec.HilbertComplex

open _root_.Feec.HodgeWave

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Uniform convergence on compact sets -/

theorem eventually_forall_lt_of_tendsto_on {κ F : Type*} [SeminormedAddCommGroup F]
    {l : Filter κ} {f : κ → F → ℝ} {M : ℝ} (hf : ∀ h ζ ζ', f h ζ ≤ f h ζ' + M * ‖ζ - ζ'‖)
    {S : Set F} (hlim : ∀ ζ ∈ S, Tendsto (fun h => f h ζ) l (𝓝 0)) (hS : IsCompact S) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ h in l, ∀ ζ ∈ S, f h ζ < ε := by
  set M' := max M 0
  have hM' : 0 ≤ M' := le_max_right _ _
  set δ := ε / (2 * (M' + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨t, hts, htf, hcov⟩ := hS.finite_cover_balls hδ
  have hev : ∀ᶠ h in l, ∀ z ∈ t, f h z < ε / 2 :=
    (htf.eventually_all).2 fun z hz => (tendsto_order.1 (hlim z (hts hz))).2 _ (half_pos hε)
  filter_upwards [hev] with h hh ζ hζ
  obtain ⟨z, hz, hζz⟩ := mem_iUnion₂.1 (hcov hζ)
  rw [Metric.mem_ball, dist_eq_norm] at hζz
  have h1 := hf h ζ z
  have h2 : M * ‖ζ - z‖ ≤ M' * δ :=
    (mul_le_mul_of_nonneg_right (le_max_left M 0) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hζz.le hM')
  have h3 : M' * δ < ε / 2 := by
    have e : M' * δ = ε / 2 * (M' / (M' + 1)) := by
      simp only [δ]; field_simp
    rw [e]
    have : M' / (M' + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
    nlinarith
  linarith [hh z hz]

/-! ### Differential spaces -/

section DiffSpace

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]
  (D : X →L[𝕜] X)

/-- The **Hodge wave operator** `D - D*` of an operator `D`. -/
def diffWave : X →L[𝕜] X := D - D.adjoint

theorem diffWave_apply (v : X) : diffWave D v = D v - D.adjoint v := rfl

theorem inner_diffWave (v w : X) : ⟪diffWave D v, w⟫_𝕜 = ⟪D v, w⟫_𝕜 - ⟪v, D w⟫_𝕜 := by
  rw [diffWave_apply, inner_sub_left, ContinuousLinearMap.adjoint_inner_left]

theorem diffWave_skew (v w : X) : ⟪diffWave D v, w⟫_𝕜 = -⟪v, diffWave D w⟫_𝕜 := by
  rw [inner_diffWave, diffWave_apply, inner_sub_right, ContinuousLinearMap.adjoint_inner_right]
  ring

theorem re_inner_sub_diffWave_self (v : X) :
    RCLike.re ⟪v - diffWave D v, v⟫_𝕜 = ‖v‖ ^ 2 := by
  have hs : RCLike.re ⟪diffWave D v, v⟫_𝕜 = 0 := by
    have h := diffWave_skew D v v
    have : RCLike.re ⟪diffWave D v, v⟫_𝕜 = - RCLike.re ⟪diffWave D v, v⟫_𝕜 := by
      conv_rhs => rw [h, _root_.map_neg, ← inner_conj_symm, RCLike.conj_re]
      simp
    linarith
  rw [inner_sub_left, _root_.map_sub, hs, sub_zero, inner_self_eq_norm_sq]

theorem norm_le_norm_sub_diffWave (v : X) : ‖v‖ ≤ ‖v - diffWave D v‖ := by
  have h := re_inner_sub_diffWave_self D v
  have h1 : RCLike.re ⟪v - diffWave D v, v⟫_𝕜 ≤ ‖v - diffWave D v‖ * ‖v‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  rw [h] at h1
  rcases (norm_nonneg v).eq_or_lt with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

theorem injective_one_sub_diffWave :
    Function.Injective ((1 - diffWave D : X →L[𝕜] X) : X →ₗ[𝕜] X) := fun a b hab => by
  have h0 : (a - b) - diffWave D (a - b) = 0 := by
    have : ((1 - diffWave D : X →L[𝕜] X)) (a - b) = 0 := by
      rw [_root_.map_sub]; exact sub_eq_zero.2 hab
    simpa using this
  have h1 := norm_le_norm_sub_diffWave D (a - b)
  rw [h0, norm_zero] at h1
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h1)

variable [FiniteDimensional 𝕜 X]

/-- `1 - (D - D*)` as a continuous linear equivalence. -/
def diffResolvent : X ≃L[𝕜] X :=
  (LinearEquiv.ofInjectiveEndo _ (injective_one_sub_diffWave D)).toContinuousLinearEquiv

theorem diffResolvent_apply (v : X) : diffResolvent D v = v - diffWave D v := rfl

theorem norm_diffResolvent_symm_apply_le (v : X) : ‖(diffResolvent D).symm v‖ ≤ ‖v‖ := by
  have h := norm_le_norm_sub_diffWave D ((diffResolvent D).symm v)
  rwa [← diffResolvent_apply, ContinuousLinearEquiv.apply_symm_apply] at h

omit [FiniteDimensional 𝕜 X] in
theorem norm_add_norm_le_of_inner_diff (hDD : ∀ v, D (D v) = 0) (r : X) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ v, ‖⟪r - diffWave D r, v⟫_𝕜‖ ≤ M * (‖v‖ + ‖D v‖)) :
    ‖r‖ + ‖D r‖ ≤ 8 * M := by
  have hDv : D (r - D r) = D r := by rw [_root_.map_sub, hDD, sub_zero]
  have hv := h (r - D r)
  rw [hDv] at hv
  have e1 : r - diffWave D r = (r - D r) + D.adjoint r := by rw [diffWave_apply]; abel
  have e2 : ⟪D.adjoint r, r - D r⟫_𝕜 = ⟪r, D r⟫_𝕜 := by
    rw [ContinuousLinearMap.adjoint_inner_left, hDv]
  have hre : RCLike.re ⟪r - diffWave D r, r - D r⟫_𝕜 =
      ‖r‖ ^ 2 + ‖D r‖ ^ 2 - RCLike.re ⟪r, D r⟫_𝕜 := by
    rw [e1, inner_add_left, _root_.map_add, e2, inner_self_eq_norm_sq, @norm_sub_sq 𝕜]
    ring
  have hle : RCLike.re ⟪r - diffWave D r, r - D r⟫_𝕜 ≤ ‖⟪r - diffWave D r, r - D r⟫_𝕜‖ :=
    RCLike.re_le_norm _
  have hab : RCLike.re ⟪r, D r⟫_𝕜 ≤ ‖r‖ * ‖D r‖ := re_inner_le_norm _ _
  have hs : ‖r - D r‖ ≤ ‖r‖ + ‖D r‖ := norm_sub_le _ _
  have ha := norm_nonneg r
  have hb := norm_nonneg (D r)
  have hsq : (‖r‖ + ‖D r‖) ^ 2 ≤ 8 * M * (‖r‖ + ‖D r‖) := by
    have : M * (‖r - D r‖ + ‖D r‖) ≤ M * (2 * (‖r‖ + ‖D r‖)) :=
      mul_le_mul_of_nonneg_left (by linarith) hM
    nlinarith [sq_nonneg (‖r‖ - ‖D r‖)]
  nlinarith

theorem mem_of_invariant [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] (L : X →L[𝕜] X)
    (hL : ∀ x y, ⟪L x, y⟫_𝕜 = -⟪x, L y⟫_𝕜) (K : Submodule 𝕜 X) (hK : ∀ v ∈ K, L v ∈ K)
    {v : X} (hv : v ∈ K) (t : ℝ) : (C0Group.ofBounded L).S t v ∈ K := by
  have : CompleteSpace K := FiniteDimensional.complete 𝕜 K
  set LK : K →L[𝕜] K := LinearMap.toContinuousLinearMap (L.toLinearMap.restrict hK)
  set u : ℝ → X := fun s => (K.subtypeL ((C0Group.ofBounded LK).S s ⟨v, hv⟩))
  have hu : ∀ s, HasDerivAt u (L (u s)) s := fun s => by
    have hd := ContinuousLinearMap.hasDerivAt_exp_ofReal_smul_apply LK ⟨v, hv⟩ s
    exact (K.subtypeL.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hd
  have e := eq_ofBounded_of_hasDerivAt L hL hu t
  have e0 : u 0 = v := by simp only [u, C0Group.S_zero_apply]; rfl
  rw [e0] at e
  rw [← e]
  exact ((C0Group.ofBounded LK).S t ⟨v, hv⟩).2

end DiffSpace

variable {ι : Type*} [Fintype ι] {c : ComplexShape ι}
  {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)]
  [∀ i, CompleteSpace (W i)]

/-! ### `D(L)`: the two halves of the wave operator -/

section WaveDomain

variable (H : HilbertComplex 𝕜 c W)

theorem wave_eq_sub (y : H.wave.domain) :
    H.wave y = H.totalD ⟨y, y.2.1⟩ - H.dual.totalD ⟨y, y.2.2⟩ := rfl

theorem norm_wave_sq' (y : H.wave.domain) :
    ‖H.wave y‖ ^ 2 = ‖H.totalD ⟨y, y.2.1⟩‖ ^ 2 + ‖H.dual.totalD ⟨y, y.2.2⟩‖ ^ 2 := by
  have h0 : ⟪H.totalD ⟨y, y.2.1⟩, H.dual.totalD ⟨y, y.2.2⟩⟫_𝕜 = 0 := by
    rw [← H.inner_totalD_dual ⟨_, H.totalD_mapsTo ⟨y, y.2.1⟩⟩ ⟨y, y.2.2⟩,
      H.totalD_comp_totalD, inner_zero_left]
  rw [wave_eq_sub, @norm_sub_sq 𝕜, h0, _root_.map_zero, mul_zero, sub_zero]

theorem norm_totalD_le_norm_wave (y : H.wave.domain) : ‖H.totalD ⟨y, y.2.1⟩‖ ≤ ‖H.wave y‖ := by
  have h := norm_wave_sq' H y
  nlinarith [norm_nonneg (H.totalD ⟨y, y.2.1⟩), norm_nonneg (H.wave y),
    norm_nonneg (H.dual.totalD ⟨y, y.2.2⟩)]

end WaveDomain

/-! ### Approximating families of discrete differential spaces -/

/-- A **family of discrete differential spaces** with uniformly bounded reading maps `iₕ`. -/
structure ApproxComplexCrime.Family (H : HilbertComplex 𝕜 c W) (κ : Type*) where
  /-- the discrete spaces -/
  X : κ → Type u
  [normedAddCommGroup : ∀ h, NormedAddCommGroup (X h)]
  [innerProductSpace : ∀ h, InnerProductSpace 𝕜 (X h)]
  [completeSpace : ∀ h, CompleteSpace (X h)]
  [finiteDimensional : ∀ h, FiniteDimensional 𝕜 (X h)]
  [normedSpaceReal : ∀ h, NormedSpace ℝ (X h)]
  [isScalarTower : ∀ h, IsScalarTower ℝ 𝕜 (X h)]
  /-- the discrete differentials -/
  D : ∀ h, X h →L[𝕜] X h
  D_D : ∀ h v, D h (D h v) = 0
  /-- the reading maps `iₕ` -/
  incl : ∀ h, X h →L[𝕜] PiLp 2 W
  /-- the left inverses `πₕ` -/
  proj : ∀ h, PiLp 2 W →L[𝕜] X h
  proj_incl : ∀ h v, proj h (incl h v) = v
  bound : ∃ C, ∀ h, ‖incl h‖ ≤ C ∧ ‖proj h‖ ≤ C

attribute [instance] ApproxComplexCrime.Family.normedAddCommGroup
  ApproxComplexCrime.Family.innerProductSpace ApproxComplexCrime.Family.completeSpace
  ApproxComplexCrime.Family.finiteDimensional ApproxComplexCrime.Family.normedSpaceReal
  ApproxComplexCrime.Family.isScalarTower

namespace ApproxComplexCrime.Family

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (S : ApproxComplexCrime.Family.{u} H κ)

/-- A nonnegative uniform bound of `‖iₕ‖`, `‖πₕ‖`. -/
def boundConst : ℝ := max S.bound.choose 0

theorem boundConst_nonneg : 0 ≤ S.boundConst := le_max_right _ _

theorem norm_incl_le (h : κ) : ‖S.incl h‖ ≤ S.boundConst :=
  (S.bound.choose_spec h).1.trans (le_max_left _ _)

theorem norm_proj_le (h : κ) : ‖S.proj h‖ ≤ S.boundConst :=
  (S.bound.choose_spec h).2.trans (le_max_left _ _)

theorem norm_incl_apply_le (h : κ) (v : S.X h) : ‖S.incl h v‖ ≤ S.boundConst * ‖v‖ :=
  ((S.incl h).le_opNorm v).trans (mul_le_mul_of_nonneg_right (S.norm_incl_le h) (norm_nonneg _))

theorem norm_adjoint_incl_apply_le (h : κ) (z : PiLp 2 W) :
    ‖(S.incl h).adjoint z‖ ≤ S.boundConst * ‖z‖ :=
  ((S.incl h).adjoint.le_opNorm z).trans (mul_le_mul_of_nonneg_right
    ((ContinuousLinearMap.adjoint.norm_map (S.incl h)).trans_le (S.norm_incl_le h))
    (norm_nonneg _))

theorem norm_le_norm_incl (h : κ) (v : S.X h) : ‖v‖ ≤ S.boundConst * ‖S.incl h v‖ :=
  calc ‖v‖ = ‖S.proj h (S.incl h v)‖ := by rw [S.proj_incl]
    _ ≤ ‖S.proj h‖ * ‖S.incl h v‖ := (S.proj h).le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_right (S.norm_proj_le h) (norm_nonneg _)

/-- The discrete Hodge wave operator `Lₕ = 𝐝ₕ - 𝐝ₕ*`. -/
abbrev L (h : κ) : S.X h →L[𝕜] S.X h := diffWave (S.D h)

/-- The **inner-product operator** `Jₕ = iₕ* iₕ`. -/
def J (h : κ) : S.X h →L[𝕜] S.X h := (S.incl h).adjoint ∘L S.incl h

theorem inner_J (h : κ) (v w : S.X h) : ⟪S.J h v, w⟫_𝕜 = ⟪S.incl h v, S.incl h w⟫_𝕜 := by
  rw [J, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]

theorem norm_one_sub_J_le (h : κ) : ‖1 - S.J h‖ ≤ 1 + S.boundConst ^ 2 := by
  refine (norm_sub_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le ?_)
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [ContinuousLinearMap.adjoint.norm_map, pow_two]
  exact mul_le_mul (S.norm_incl_le h) (S.norm_incl_le h) (norm_nonneg _) S.boundConst_nonneg

/-- **The inner-product defect** `graphDefect`: the norm of `1 - Jₕ` on the graph space of `𝐝ₕ`. -/
def graphDefect (h : κ) : ℝ := (S.D h).graphOpNorm (1 - S.J h)

theorem graphDefect_nonneg (h : κ) : 0 ≤ S.graphDefect h := (S.D h).graphOpNorm_nonneg _

theorem graphDefect_le (h : κ) : S.graphDefect h ≤ ‖1 - S.J h‖ := (S.D h).graphOpNorm_le _

theorem graphDefect_eq_zero_iff (h : κ) : S.graphDefect h = 0 ↔ S.J h = 1 :=
  ((S.D h).graphOpNorm_eq_zero_iff _).trans (sub_eq_zero.trans eq_comm)

theorem norm_one_sub_J_graphFst_le (h : κ)
    (v : ((S.D h : S.X h →ₗ[𝕜] S.X h).toPMap ⊤).GraphSpace) :
    ‖(1 - S.J h) (((S.D h : S.X h →ₗ[𝕜] S.X h).toPMap ⊤).graphFst v)‖ ≤ S.graphDefect h * ‖v‖ :=
  (S.D h).norm_graphFst_le_graphOpNorm _ v

theorem norm_one_sub_J_apply_le (h : κ) (v : S.X h) :
    ‖(1 - S.J h) v‖ ≤ S.graphDefect h * (‖v‖ + ‖S.D h v‖) :=
  (S.D h).norm_apply_le_graphOpNorm _ v

theorem norm_one_sub_J_apply_le_of_D_eq_zero (h : κ) {v : S.X h} (hv : S.D h v = 0) :
    ‖(1 - S.J h) v‖ ≤ S.graphDefect h * ‖v‖ :=
  (S.D h).norm_apply_le_graphOpNorm_of_eq_zero _ hv

theorem norm_one_sub_J_add_le (h : κ) (w : S.X h) :
    ‖(1 - S.J h) w‖ + ‖(1 - S.J h) (S.D h w)‖ ≤ S.graphDefect h * (‖w‖ + 2 * ‖S.D h w‖) :=
  (add_le_add (S.norm_one_sub_J_apply_le h w)
    (S.norm_one_sub_J_apply_le_of_D_eq_zero h (S.D_D h w))).trans_eq (by ring)

theorem norm_one_sub_J_add_le_opNorm (h : κ) (w : S.X h) :
    ‖(1 - S.J h) w‖ + ‖(1 - S.J h) (S.D h w)‖ ≤ ‖1 - S.J h‖ * (‖w‖ + ‖S.D h w‖) :=
  (add_le_add ((1 - S.J h).le_opNorm w) ((1 - S.J h).le_opNorm _)).trans_eq (by ring)

theorem graphDefect_le_of_forall (h : κ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ v, ‖(1 - S.J h) v‖ ≤ δ * (‖v‖ + ‖S.D h v‖)) : S.graphDefect h ≤ √2 * δ :=
  (S.D h).graphOpNorm_le_of_forall _ hδ hb

theorem tendsto_graphDefect_of_tendsto {l : Filter κ}
    (hJ : Tendsto (fun h => ‖1 - S.J h‖) l (𝓝 0)) : Tendsto S.graphDefect l (𝓝 0) :=
  squeeze_zero S.graphDefect_nonneg S.graphDefect_le hJ

/-! #### The exact-load elliptic projection -/

/-- The **load map** `Bₕ = (1 - Lₕ)⁻¹ iₕ*`, with `Rₕ y = Bₕ (y - L y)` the exact-load projection. -/
def load (h : κ) : PiLp 2 W →L[𝕜] S.X h :=
  ((diffResolvent (S.D h)).symm : S.X h →L[𝕜] S.X h) ∘L (S.incl h).adjoint

theorem load_sub (h : κ) (z : PiLp 2 W) :
    S.load h z - S.L h (S.load h z) = (S.incl h).adjoint z :=
  (diffResolvent (S.D h)).apply_symm_apply ((S.incl h).adjoint z)

theorem inner_load_sub (h : κ) (z : PiLp 2 W) (v : S.X h) :
    ⟪S.load h z - S.L h (S.load h z), v⟫_𝕜 = ⟪z, S.incl h v⟫_𝕜 := by
  rw [S.load_sub, ContinuousLinearMap.adjoint_inner_left]

theorem eq_load (h : κ) {z : PiLp 2 W} {r : S.X h} (hr : r - S.L h r = (S.incl h).adjoint z) :
    r = S.load h z :=
  (diffResolvent (S.D h)).injective (by
    rw [diffResolvent_apply, diffResolvent_apply, hr, S.load_sub])

theorem norm_load_apply_le (h : κ) (z : PiLp 2 W) : ‖S.load h z‖ ≤ S.boundConst * ‖z‖ :=
  (norm_diffResolvent_symm_apply_le (S.D h) _).trans (S.norm_adjoint_incl_apply_le h z)

theorem norm_load_add_le (h : κ) (z : PiLp 2 W) :
    ‖S.load h z‖ + ‖S.D h (S.load h z)‖ ≤ 8 * S.boundConst * ‖z‖ := by
  have hC := S.boundConst_nonneg
  refine (norm_add_norm_le_of_inner_diff (S.D h) (S.D_D h) (S.load h z)
    (M := S.boundConst * ‖z‖) (by positivity) fun v => ?_).trans_eq (by ring)
  rw [S.inner_load_sub h z v]
  calc ‖⟪z, S.incl h v⟫_𝕜‖ ≤ ‖z‖ * (S.boundConst * ‖v‖) :=
        (norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (S.norm_incl_apply_le h v) (norm_nonneg _))
    _ = S.boundConst * ‖z‖ * ‖v‖ := by ring
    _ ≤ S.boundConst * ‖z‖ * (‖v‖ + ‖S.D h v‖) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _)) (by positivity)

theorem norm_one_sub_J_load_le (h : κ) (z : PiLp 2 W) :
    ‖(1 - S.J h) (S.load h z)‖ ≤ S.graphDefect h * (8 * S.boundConst * ‖z‖) :=
  (S.norm_one_sub_J_apply_le h _).trans
    (mul_le_mul_of_nonneg_left (S.norm_load_add_le h z) (S.graphDefect_nonneg h))

/-! #### The Strang lemma -/

theorem norm_sub_load_add_le (h : κ) (z : PiLp 2 W) (w : S.X h) {ε : ℝ} (hε : 0 ≤ ε)
    (hres : ∀ v, ‖⟪w - S.L h w, v⟫_𝕜 - ⟪z, S.incl h v⟫_𝕜‖ ≤ ε * (‖v‖ + ‖S.D h v‖)) :
    ‖w - S.load h z‖ + ‖S.D h (w - S.load h z)‖ ≤ 8 * ε := by
  refine norm_add_norm_le_of_inner_diff (S.D h) (S.D_D h) _ hε fun v => ?_
  have e : ⟪(w - S.load h z) - S.L h (w - S.load h z), v⟫_𝕜 =
      ⟪w - S.L h w, v⟫_𝕜 - ⟪z, S.incl h v⟫_𝕜 := by
    rw [← S.inner_load_sub h z v, ← inner_sub_left, _root_.map_sub]
    congr 1; abel
  rw [e]; exact hres v

/-- **The Strang lemma**: `‖y - iₕ Bₕ z‖ ≤ ‖y - iₕ w‖ + 8 C ε` for an approximant `w` whose
residual against `z` is at most `ε`. -/
theorem norm_sub_incl_load_le (h : κ) (y z : PiLp 2 W) (w : S.X h) {ε : ℝ} (hε : 0 ≤ ε)
    (hres : ∀ v, ‖⟪w - S.L h w, v⟫_𝕜 - ⟪z, S.incl h v⟫_𝕜‖ ≤ ε * (‖v‖ + ‖S.D h v‖)) :
    ‖y - S.incl h (S.load h z)‖ ≤ ‖y - S.incl h w‖ + 8 * S.boundConst * ε := by
  have h1 := S.norm_sub_load_add_le h z w hε hres
  have h2 : ‖w - S.load h z‖ ≤ 8 * ε := by linarith [norm_nonneg (S.D h (w - S.load h z))]
  have e : y - S.incl h (S.load h z) = (y - S.incl h w) + S.incl h (w - S.load h z) := by
    rw [_root_.map_sub]; abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (S.norm_incl_apply_le h _).trans ?_
  have := S.boundConst_nonneg
  nlinarith

/-! #### The consistency defect -/

theorem norm_load_sub_adjoint_le (h : κ) (y z : PiLp 2 W) :
    ‖S.load h z - (S.incl h).adjoint y‖ ≤
      ‖(1 - S.J h) (S.load h z)‖ + S.boundConst * ‖y - S.incl h (S.load h z)‖ := by
  have e : S.load h z - (S.incl h).adjoint y =
      (1 - S.J h) (S.load h z) - (S.incl h).adjoint (y - S.incl h (S.load h z)) := by
    simp only [J, _root_.sub_apply, one_apply_eq_self,
      ContinuousLinearMap.comp_apply, _root_.map_sub]
    abel
  rw [e]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl (S.norm_adjoint_incl_apply_le h _))

theorem load_defect (h : κ) (a b b' : PiLp 2 W) :
    S.load h (b - b') - S.L h (S.load h (a - b)) =
      (S.load h (b - b') - (S.incl h).adjoint b) - (S.load h (a - b) - (S.incl h).adjoint a) := by
  have e := S.load_sub h (a - b)
  have e' : S.L h (S.load h (a - b)) = S.load h (a - b) - (S.incl h).adjoint (a - b) := by
    rw [← e]; abel
  rw [e']
  simp only [_root_.map_sub]
  abel

/-! #### The cochain defect and the splitting of the residual -/

/-- The **cochain defect** `κₕ(y) = 𝐝ₕ* iₕ* y - iₕ* 𝐝* y` of `y ∈ D(L)`. -/
def cochainDefect (h : κ) (y : H.wave.domain) : S.X h :=
  (S.D h).adjoint ((S.incl h).adjoint y) - (S.incl h).adjoint (H.dual.totalD ⟨y, y.2.2⟩)

theorem inner_cochainDefect (h : κ) (y : H.wave.domain) (v : S.X h) :
    ⟪S.cochainDefect h y, v⟫_𝕜 =
      ⟪(y : PiLp 2 W), S.incl h (S.D h v)⟫_𝕜 - ⟪H.dual.totalD ⟨y, y.2.2⟩, S.incl h v⟫_𝕜 := by
  rw [cochainDefect, inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]

theorem inner_cochainDefect_of_mem (h : κ) (y : H.wave.domain) (v : S.X h)
    (hv : S.incl h v ∈ H.totalD.domain) :
    ⟪S.cochainDefect h y, v⟫_𝕜 =
      ⟪(y : PiLp 2 W), S.incl h (S.D h v) - H.totalD ⟨_, hv⟩⟫_𝕜 := by
  rw [inner_cochainDefect, inner_sub_right]
  congr 1
  rw [← inner_conj_symm, ← H.inner_totalD_dual ⟨_, hv⟩ ⟨y, y.2.2⟩, inner_conj_symm]

theorem cochainDefect_eq_zero (h : κ) (hmem : ∀ v, S.incl h v ∈ H.totalD.domain)
    (hcomm : ∀ v, H.totalD ⟨_, hmem v⟩ = S.incl h (S.D h v)) (y : H.wave.domain) :
    S.cochainDefect h y = 0 :=
  ext_inner_right 𝕜 fun v => by
    rw [S.inner_cochainDefect_of_mem h y v (hmem v), hcomm, sub_self, inner_zero_right,
      inner_zero_left]

/-- **The residual splits** into the inner-product defect at `w` and `𝐝ₕ w`, the graph-norm
approximation error and the cochain defect. -/
theorem inner_residual_eq (h : κ) (y : H.wave.domain) (w v : S.X h) :
    ⟪w - S.L h w, v⟫_𝕜 - ⟪(y : PiLp 2 W) - H.wave y, S.incl h v⟫_𝕜 =
      ⟪(1 - S.J h) w, v⟫_𝕜 - ⟪(1 - S.J h) (S.D h w), v⟫_𝕜 + ⟪(1 - S.J h) w, S.D h v⟫_𝕜 +
        ⟪S.incl h w - y, S.incl h v⟫_𝕜 -
        ⟪S.incl h (S.D h w) - H.totalD ⟨y, y.2.1⟩, S.incl h v⟫_𝕜 +
        ⟪S.incl h w - y, S.incl h (S.D h v)⟫_𝕜 + ⟪S.cochainDefect h y, v⟫_𝕜 := by
  rw [S.inner_cochainDefect, wave_eq_sub]
  simp only [_root_.sub_apply, one_apply_eq_self, inner_sub_left, inner_diffWave, S.inner_J]
  ring

theorem norm_residual_le (h : κ) (y : H.wave.domain) (w : S.X h) {δ : ℝ}
    (hδ : ∀ v, ‖⟪S.cochainDefect h y, v⟫_𝕜‖ ≤ δ * (‖v‖ + ‖S.D h v‖)) (v : S.X h) :
    ‖⟪w - S.L h w, v⟫_𝕜 - ⟪(y : PiLp 2 W) - H.wave y, S.incl h v⟫_𝕜‖ ≤
      (‖(1 - S.J h) w‖ + ‖(1 - S.J h) (S.D h w)‖ + S.boundConst *
        (‖(y : PiLp 2 W) - S.incl h w‖ + ‖H.totalD ⟨y, y.2.1⟩ - S.incl h (S.D h w)‖) + δ) *
        (‖v‖ + ‖S.D h v‖) := by
  rw [S.inner_residual_eq]
  set C := S.boundConst
  set p := ‖(1 - S.J h) w‖
  set q := ‖(1 - S.J h) (S.D h w)‖
  set a := ‖(y : PiLp 2 W) - S.incl h w‖
  set b := ‖H.totalD ⟨y, y.2.1⟩ - S.incl h (S.D h w)‖
  have hC := S.boundConst_nonneg
  have hp : 0 ≤ p := norm_nonneg _
  have hq : 0 ≤ q := norm_nonneg _
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hv := norm_nonneg v
  have hDv := norm_nonneg (S.D h v)
  have b1 : ‖⟪(1 - S.J h) w, v⟫_𝕜‖ ≤ p * ‖v‖ := norm_inner_le_norm _ _
  have b2 : ‖⟪(1 - S.J h) (S.D h w), v⟫_𝕜‖ ≤ q * ‖v‖ := norm_inner_le_norm _ _
  have b3 : ‖⟪(1 - S.J h) w, S.D h v⟫_𝕜‖ ≤ p * ‖S.D h v‖ := norm_inner_le_norm _ _
  have b4 : ‖⟪S.incl h w - y, S.incl h v⟫_𝕜‖ ≤ a * (C * ‖v‖) := by
    refine (norm_inner_le_norm _ _).trans (mul_le_mul (le_of_eq ?_) (S.norm_incl_apply_le h v)
      (norm_nonneg _) ha)
    rw [norm_sub_rev]
  have b5 : ‖⟪S.incl h (S.D h w) - H.totalD ⟨y, y.2.1⟩, S.incl h v⟫_𝕜‖ ≤ b * (C * ‖v‖) := by
    refine (norm_inner_le_norm _ _).trans (mul_le_mul (le_of_eq ?_) (S.norm_incl_apply_le h v)
      (norm_nonneg _) hb)
    rw [norm_sub_rev]
  have b6 : ‖⟪S.incl h w - y, S.incl h (S.D h v)⟫_𝕜‖ ≤ a * (C * ‖S.D h v‖) := by
    refine (norm_inner_le_norm _ _).trans (mul_le_mul (le_of_eq ?_) (S.norm_incl_apply_le h _)
      (norm_nonneg _) ha)
    rw [norm_sub_rev]
  have b7 := hδ v
  calc _ ≤ ‖⟪(1 - S.J h) w, v⟫_𝕜‖ + ‖⟪(1 - S.J h) (S.D h w), v⟫_𝕜‖ +
        ‖⟪(1 - S.J h) w, S.D h v⟫_𝕜‖ + ‖⟪S.incl h w - y, S.incl h v⟫_𝕜‖ +
        ‖⟪S.incl h (S.D h w) - H.totalD ⟨y, y.2.1⟩, S.incl h v⟫_𝕜‖ +
        ‖⟪S.incl h w - y, S.incl h (S.D h v)⟫_𝕜‖ + ‖⟪S.cochainDefect h y, v⟫_𝕜‖ := by
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_sub_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        exact norm_sub_le _ _
    _ ≤ _ := by nlinarith [mul_nonneg hq hDv, mul_nonneg (mul_nonneg hC hb) hDv]

theorem reading_le (h : κ)
    (ζ ζ' : PiLp 2 W × PiLp 2 W) :
    ‖ζ.1 - S.incl h (S.load h (ζ.1 - ζ.2))‖ ≤ ‖ζ'.1 - S.incl h (S.load h (ζ'.1 - ζ'.2))‖ +
      (1 + 2 * S.boundConst ^ 2) * ‖ζ - ζ'‖ := by
  set C := S.boundConst
  have hC := S.boundConst_nonneg
  have e : ζ.1 - S.incl h (S.load h (ζ.1 - ζ.2)) =
      (ζ'.1 - S.incl h (S.load h (ζ'.1 - ζ'.2))) +
        ((ζ - ζ').1 - S.incl h (S.load h ((ζ - ζ').1 - (ζ - ζ').2))) := by
    simp only [Prod.fst_sub, Prod.snd_sub, _root_.map_sub]; abel
  have h1 := norm_fst_le (ζ - ζ')
  have h2 := norm_snd_le (ζ - ζ')
  have h3 : ‖S.incl h (S.load h ((ζ - ζ').1 - (ζ - ζ').2))‖ ≤
      C * (C * (‖(ζ - ζ').1‖ + ‖(ζ - ζ').2‖)) :=
    (S.norm_incl_apply_le h _).trans (mul_le_mul_of_nonneg_left
      ((S.norm_load_apply_le h _).trans (mul_le_mul_of_nonneg_left (norm_sub_le _ _) hC)) hC)
  have h4 : C * (C * (‖(ζ - ζ').1‖ + ‖(ζ - ζ').2‖)) ≤ 2 * C ^ 2 * ‖ζ - ζ'‖ := by
    have : ‖(ζ - ζ').1‖ + ‖(ζ - ζ').2‖ ≤ 2 * ‖ζ - ζ'‖ := by linarith
    have := mul_le_mul_of_nonneg_left this (mul_nonneg hC hC)
    nlinarith
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ((norm_sub_le _ _).trans ?_))
  nlinarith

theorem defect_le (h : κ)
    (ζ ζ' : PiLp 2 W × PiLp 2 W) :
    ‖S.load h (ζ.1 - ζ.2) - (S.incl h).adjoint ζ.1‖ ≤
      ‖S.load h (ζ'.1 - ζ'.2) - (S.incl h).adjoint ζ'.1‖ + (3 * S.boundConst) * ‖ζ - ζ'‖ := by
  set C := S.boundConst
  have hC := S.boundConst_nonneg
  have e : S.load h (ζ.1 - ζ.2) - (S.incl h).adjoint ζ.1 =
      (S.load h (ζ'.1 - ζ'.2) - (S.incl h).adjoint ζ'.1) +
        (S.load h ((ζ - ζ').1 - (ζ - ζ').2) - (S.incl h).adjoint (ζ - ζ').1) := by
    simp only [Prod.fst_sub, Prod.snd_sub, _root_.map_sub]; abel
  have h1 := norm_fst_le (ζ - ζ')
  have h2 := norm_snd_le (ζ - ζ')
  have h3 : ‖S.load h ((ζ - ζ').1 - (ζ - ζ').2)‖ ≤ C * (‖(ζ - ζ').1‖ + ‖(ζ - ζ').2‖) :=
    (S.norm_load_apply_le h _).trans (mul_le_mul_of_nonneg_left (norm_sub_le _ _) hC)
  have h4 := S.norm_adjoint_incl_apply_le h (ζ - ζ').1
  have h5 : C * (‖(ζ - ζ').1‖ + ‖(ζ - ζ').2‖) + C * ‖(ζ - ζ').1‖ ≤ 3 * C * ‖ζ - ζ'‖ := by
    have a := mul_le_mul_of_nonneg_left h1 hC
    have b := mul_le_mul_of_nonneg_left h2 hC
    nlinarith
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ((norm_sub_le _ _).trans ?_))
  linarith

end ApproxComplexCrime.Family

/-! ### Approximating families -/

section Families

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- A **family for the heat equation**: a constraint, a filter, and `graphDefect → 0`. -/
structure ApproxComplexCrime.HeatFamily (H : HilbertComplex 𝕜 c W) (κ : Type*) where
  /-- the discrete differential spaces and reading maps -/
  toFamily : ApproxComplexCrime.Family.{u} H κ
  /-- the constraint subspace -/
  K : Submodule 𝕜 (PiLp 2 W)
  isClosed_K : IsClosed (K : Set (PiLp 2 W))
  /-- the filter of refinement -/
  l : Filter κ
  tendsto_graphDefect : Tendsto toFamily.graphDefect l (𝓝 0)

/-- An **approximating family**: admissible states, a core, and consistent approximation on them. -/
structure ApproxComplexCrime (H : HilbertComplex 𝕜 c W) (κ : Type*) extends
    ApproxComplexCrime.HeatFamily.{u} H κ where
  /-- the admissible states -/
  A : Set (PiLp 2 W)
  A_sub : A ⊆ H.wave.domain
  /-- the core -/
  Z : Submodule 𝕜 (PiLp 2 W)
  Z_le : Z ≤ H.wave.domainSq
  orbit_mem : ∀ x ∈ Z, ∀ t : ℝ, 0 ≤ t →
    H.waveGroup.S t x ∈ A ∧ H.waveGroup.S t (waveExt H x) ∈ A
  consistent : ∀ y ∈ A, ∀ ε > 0, ∀ᶠ h in l, ∃ w : toFamily.X h,
    ‖y - toFamily.incl h w‖ ≤ ε ∧ ∀ v, ‖⟪w - toFamily.L h w, v⟫_𝕜 -
      ⟪y - waveExt H y, toFamily.incl h v⟫_𝕜‖ ≤ ε * (‖v‖ + ‖toFamily.D h v‖)

namespace ApproxComplexCrime

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxComplexCrime.{u} H κ)

theorem consistent_iff_tendsto_incl_load (y : PiLp 2 W) :
    (∀ ε > 0, ∀ᶠ h in F.l, ∃ w : F.toFamily.X h,
      ‖y - F.toFamily.incl h w‖ ≤ ε ∧ ∀ v, ‖⟪w - F.toFamily.L h w, v⟫_𝕜 -
        ⟪y - waveExt H y, F.toFamily.incl h v⟫_𝕜‖ ≤ ε * (‖v‖ + ‖F.toFamily.D h v‖)) ↔
      Tendsto (fun h => ‖y - F.toFamily.incl h (F.toFamily.load h (y - waveExt H y))‖) F.l
        (𝓝 0) := by
  set S := F.toFamily
  constructor
  · intro hc
    rw [Metric.tendsto_nhds]
    intro ε hε
    set B := 1 + 8 * S.boundConst
    have hB : 0 < B := by have := S.boundConst_nonneg; positivity
    filter_upwards [hc (ε / (2 * B)) (by positivity)] with h ⟨w, hw, hres⟩
    rw [dist_eq_norm, sub_zero, Real.norm_of_nonneg (norm_nonneg _)]
    have h1 := S.norm_sub_incl_load_le h y _ w (by positivity) hres
    have : ‖y - S.incl h w‖ + 8 * S.boundConst * (ε / (2 * B)) ≤ ε / 2 := by
      have e : ε / (2 * B) + 8 * S.boundConst * (ε / (2 * B)) = ε / 2 := by
        have e1 : ε / (2 * B) + 8 * S.boundConst * (ε / (2 * B)) = ε / (2 * B) * B := by
          simp only [B]; ring
        rw [e1]; field_simp
      linarith
    linarith
  · intro ht ε hε
    have hev := (Metric.tendsto_nhds.1 ht) ε hε
    filter_upwards [hev] with h hh
    rw [dist_eq_norm, sub_zero, Real.norm_of_nonneg (norm_nonneg _)] at hh
    refine ⟨S.load h (y - waveExt H y), hh.le, fun v => ?_⟩
    rw [S.inner_load_sub, sub_self, norm_zero]
    exact mul_nonneg hε.le (by positivity)

theorem tendsto_incl_load {y : PiLp 2 W} (hy : y ∈ F.A) :
    Tendsto (fun h => ‖y - F.toFamily.incl h (F.toFamily.load h (y - waveExt H y))‖) F.l
      (𝓝 0) :=
  (F.consistent_iff_tendsto_incl_load y).1 (F.consistent y hy)

theorem tendsto_defect {y : PiLp 2 W} (hy : y ∈ F.A) :
    Tendsto (fun h => ‖F.toFamily.load h (y - waveExt H y) - (F.toFamily.incl h).adjoint y‖)
      F.l (𝓝 0) := by
  set S := F.toFamily
  have h1 := F.tendsto_graphDefect
  have h2 := F.tendsto_incl_load hy
  have hb : Tendsto (fun h => S.graphDefect h * (8 * S.boundConst * ‖y - waveExt H y‖) +
      S.boundConst * ‖y - S.incl h (S.load h (y - waveExt H y))‖) F.l (𝓝 0) := by
    have := (h1.mul_const (8 * S.boundConst * ‖y - waveExt H y‖)).add (h2.const_mul S.boundConst)
    simpa using this
  exact squeeze_zero (fun _ => norm_nonneg _) (fun h => (S.norm_load_sub_adjoint_le h y _).trans
    (add_le_add (S.norm_one_sub_J_load_le h _) le_rfl)) hb

end ApproxComplexCrime

/-! ### The approximating FEEC discretization -/

section OfComplexCrime

namespace ApproxFEEC

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxComplexCrime.{u} H κ)

/-- **The approximating FEEC discretization** of `F`: `Xₕ`, `Lₕ = 𝐝ₕ - 𝐝ₕ*`, `ιₕ = iₕ`, `πₕ`. -/
def ofComplexCrime : ApproxFEEC H κ where
  K := F.K
  isClosed_K := F.isClosed_K
  l := F.l
  X := F.toFamily.X
  L h := F.toFamily.L h
  isSkewAdjoint := H.isSkewAdjoint_wave
  skew h := diffWave_skew (F.toFamily.D h)
  incl := F.toFamily.incl
  proj := F.toFamily.proj
  proj_incl := F.toFamily.proj_incl
  bound := F.toFamily.bound

theorem ofComplexCrime_L (h : κ) :
    (ofComplexCrime F).L h = F.toFamily.D h - (F.toFamily.D h).adjoint :=
  rfl

/-- The defect `Δₕ = Bₕ - iₕ* (1 - L)⁻¹` of the exact-load elliptic projection. -/
def loadDefect (h : κ) : PiLp 2 W →L[𝕜] F.toFamily.X h :=
  F.toFamily.load h - (F.toFamily.incl h).adjoint ∘L Operator.resolvent H.wave 1

theorem loadDefect_apply (h : κ) {y : PiLp 2 W} (hy : y ∈ H.wave.domain) :
    loadDefect F h (y - waveExt H y) =
      F.toFamily.load h (y - waveExt H y) - (F.toFamily.incl h).adjoint y := by
  have e : Operator.resolvent H.wave (1 : 𝕜) (y - waveExt H y) = y := by
    rw [waveExt_of_mem hy]
    exact resolvent_one_apply_sub (ofComplexCrime F).isMDissipative ⟨y, hy⟩
  change F.toFamily.load h _ - (F.toFamily.incl h).adjoint
    (Operator.resolvent H.wave (1 : 𝕜) (y - waveExt H y)) = _
  rw [e]

/-- **The load Ritz projection**: `Rₕ = Bₕ` on the resolvent lift `ℓ = 1 - L`. -/
def loadRitz : DissipFEEC.Ritz (DissipFEEC.Lift.resolvent (ofComplexCrime F).toDissipFEEC) where
  R := F.toFamily.load
  Δ := loadDefect F
  Δ' h := -loadDefect F h
  defect_eq h y hy := by
    have hA := (ofComplexCrime F).isMDissipative
    have hy1 := DissipFEEC.mem_domain_of_mem_resData hA hy
    have hy2 := DissipFEEC.genExt_mem_domain_of_mem_resData hy hA
    change F.toFamily.load h (DissipFEEC.genExt H.wave y -
        DissipFEEC.genExt H.wave (DissipFEEC.genExt H.wave y)) -
      F.toFamily.L h (F.toFamily.load h (y - DissipFEEC.genExt H.wave y)) =
      loadDefect F h (DissipFEEC.genExt H.wave y -
        DissipFEEC.genExt H.wave (DissipFEEC.genExt H.wave y)) +
      -loadDefect F h (y - DissipFEEC.genExt H.wave y)
    rw [← waveExt_eq_genExt] at hy2 ⊢
    rw [loadDefect_apply F h hy1, loadDefect_apply F h hy2, F.toFamily.load_defect]
    abel
  bound := by
    set C := F.toFamily.boundConst
    have hC := F.toFamily.boundConst_nonneg
    have hD : ∀ h, ‖loadDefect F h‖ ≤ 2 * C := fun h =>
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => by
        have h1 := F.toFamily.norm_load_apply_le h y
        have h2 := F.toFamily.norm_adjoint_incl_apply_le h (Operator.resolvent H.wave (1 : 𝕜) y)
        have h3 : ‖Operator.resolvent H.wave (1 : 𝕜) y‖ ≤ ‖y‖ := by
          simpa using (ofComplexCrime F).isMDissipative.norm_resolvent_apply_le one_pos y
        have e : loadDefect F h y = F.toFamily.load h y -
            (F.toFamily.incl h).adjoint (Operator.resolvent H.wave (1 : 𝕜) y) := rfl
        rw [e]
        refine (norm_sub_le _ _).trans ?_
        nlinarith [mul_le_mul_of_nonneg_left h3 hC]
    exact ⟨2 * C, fun h => ⟨(ContinuousLinearMap.opNorm_le_bound _ hC
      (F.toFamily.norm_load_apply_le h)).trans (by linarith), hD h,
      (norm_neg (loadDefect F h)).trans_le (hD h)⟩⟩

/-- **The comparison of `ofComplexCrime`** on `[0, T]`: `pₕ(t) = Rₕ (e^{tL} x)` on the core. -/
def crimeCmp (T : ℝ) : (ofComplexCrime F).Comparison T :=
  ((loadRitz F).cmp T).restrict F.Z fun _ hx =>
    DissipFEEC.domainSq_le_resData (ofComplexCrime F).isMDissipative (F.Z_le hx)

theorem loadRitz_cmp_p (T : ℝ) {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (h : κ) {t : ℝ}
    (ht : 0 ≤ t) :
    ((loadRitz F).cmp T).p x h t =
      F.toFamily.load h (H.waveGroup.S t x - H.waveGroup.S t (waveExt H x)) := by
  change F.toFamily.load h ((ofComplexCrime F).S t x -
    DissipFEEC.genExt H.wave ((ofComplexCrime F).S t x)) = _
  rw [(ofComplexCrime F).S_eq_waveGroup ht, ← waveExt_eq_genExt, waveExt_waveGroup H hx]

theorem crimeCmp_p (T : ℝ) {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (h : κ) {t : ℝ}
    (ht : 0 ≤ t) :
    (crimeCmp F T).p x h t =
      F.toFamily.load h (H.waveGroup.S t x - H.waveGroup.S t (waveExt H x)) :=
  loadRitz_cmp_p F T hx h ht

theorem crimeCmp_p_eq (T : ℝ) {x : PiLp 2 W} (hx : x ∈ F.Z) (h : κ) {t : ℝ} (ht : 0 ≤ t) :
    (crimeCmp F T).p x h t = F.toFamily.load h (H.waveGroup.S t x -
      waveExt H (H.waveGroup.S t x)) := by
  rw [crimeCmp_p F T (domainSq_le_domain (F.Z_le hx)) h ht,
    waveExt_waveGroup H (domainSq_le_domain (F.Z_le hx))]

theorem crimeCmp_defect (T : ℝ) {x : PiLp 2 W} (hx : x ∈ F.Z) (h : κ) {t : ℝ} (ht : 0 ≤ t) :
    (crimeCmp F T).defect x h t =
      (F.toFamily.load h (H.waveGroup.S t (waveExt H x) -
          H.waveGroup.S t (waveExt H (waveExt H x))) -
        (F.toFamily.incl h).adjoint (H.waveGroup.S t (waveExt H x))) -
      (F.toFamily.load h (H.waveGroup.S t x - H.waveGroup.S t (waveExt H x)) -
        (F.toFamily.incl h).adjoint (H.waveGroup.S t x)) := by
  have hx2 := F.Z_le hx
  have hx1 := domainSq_le_domain hx2
  have hLx := waveExt_mem_domain H hx2
  change ((loadRitz F).cmp T).defect x h t = _
  rw [(loadRitz F).cmp_defect T
    (DissipFEEC.domainSq_le_resData (ofComplexCrime F).isMDissipative hx2) h ht]
  change loadDefect F h ((ofComplexCrime F).S t (DissipFEEC.genExt H.wave x) -
      DissipFEEC.genExt H.wave ((ofComplexCrime F).S t (DissipFEEC.genExt H.wave x))) +
    -loadDefect F h ((ofComplexCrime F).S t x -
      DissipFEEC.genExt H.wave ((ofComplexCrime F).S t x)) = _
  rw [(ofComplexCrime F).S_eq_waveGroup ht, ← waveExt_eq_genExt,
    loadDefect_apply F h (waveGroup_mem_domain H hLx t),
    loadDefect_apply F h (waveGroup_mem_domain H hx1 t), waveExt_waveGroup H hLx,
    waveExt_waveGroup H hx1]
  abel

theorem isCompact_orbitPair (x : PiLp 2 W) (T : ℝ) :
    IsCompact ((fun t => (H.waveGroup.S t x, H.waveGroup.S t (waveExt H x))) '' Icc 0 T) :=
  isCompact_Icc.image ((H.waveGroup.strongCont _).prodMk (H.waveGroup.strongCont _))

theorem crimeCmp_tendsto_approx (T : ℝ) {x : PiLp 2 W} (hx : x ∈ F.Z) :
    TendstoUniformlyOn (fun h t => F.toFamily.incl h
      (F.toFamily.load h (H.waveGroup.S t x - H.waveGroup.S t (waveExt H x))))
      (fun t => H.waveGroup.S t x) F.l (Icc 0 T) := by
  have hx1 := domainSq_le_domain (F.Z_le hx)
  set f : κ → PiLp 2 W × PiLp 2 W → ℝ := fun h ζ =>
    ‖ζ.1 - F.toFamily.incl h (F.toFamily.load h (ζ.1 - ζ.2))‖ with hf
  set P : Set (PiLp 2 W × PiLp 2 W) :=
    (fun t => (H.waveGroup.S t x, H.waveGroup.S t (waveExt H x))) '' Icc 0 T
  have hlim : ∀ ζ ∈ P, Tendsto (fun h => f h ζ) F.l (𝓝 0) := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 := F.tendsto_incl_load (F.orbit_mem x hx t ht.1).1
    rw [waveExt_waveGroup H hx1] at h1
    exact h1
  have hev : ∀ ε > 0, ∀ᶠ h in F.l, ∀ ζ ∈ P, f h ζ < ε := fun ε hε =>
    eventually_forall_lt_of_tendsto_on (f := f) (M := 1 + 2 * F.toFamily.boundConst ^ 2)
      (fun h ζ ζ' => F.toFamily.reading_le h ζ ζ') hlim (isCompact_orbitPair x T) hε
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hev ε hε] with h hh t ht
  rw [dist_eq_norm]
  exact hh (H.waveGroup.S t x, H.waveGroup.S t (waveExt H x)) ⟨t, ht, rfl⟩

theorem crimeCmp_tendsto_defect (T : ℝ) {x : PiLp 2 W} (hx : x ∈ F.Z) :
    TendstoUniformlyOn (fun h t => ‖(crimeCmp F T).defect x h t‖) (fun _ => 0) F.l
      (Icc 0 T) := by
  have hx2 := F.Z_le hx
  have hx1 := domainSq_le_domain hx2
  have hLx := waveExt_mem_domain H hx2
  set g : κ → PiLp 2 W × PiLp 2 W → ℝ := fun h ζ =>
    ‖F.toFamily.load h (ζ.1 - ζ.2) - (F.toFamily.incl h).adjoint ζ.1‖ with hg
  set P1 : Set (PiLp 2 W × PiLp 2 W) :=
    (fun t => (H.waveGroup.S t x, H.waveGroup.S t (waveExt H x))) '' Icc 0 T
  set P2 : Set (PiLp 2 W × PiLp 2 W) :=
    (fun t => (H.waveGroup.S t (waveExt H x), H.waveGroup.S t (waveExt H (waveExt H x)))) ''
      Icc 0 T
  have hlim1 : ∀ ζ ∈ P1, Tendsto (fun h => g h ζ) F.l (𝓝 0) := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 := F.tendsto_defect (F.orbit_mem x hx t ht.1).1
    rw [waveExt_waveGroup H hx1] at h1
    exact h1
  have hlim2 : ∀ ζ ∈ P2, Tendsto (fun h => g h ζ) F.l (𝓝 0) := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 := F.tendsto_defect (F.orbit_mem x hx t ht.1).2
    rw [waveExt_waveGroup H hLx] at h1
    exact h1
  have hev1 : ∀ ε > 0, ∀ᶠ h in F.l, ∀ ζ ∈ P1, g h ζ < ε := fun ε hε =>
    eventually_forall_lt_of_tendsto_on (f := g) (M := 3 * F.toFamily.boundConst)
      (fun h ζ ζ' => F.toFamily.defect_le h ζ ζ') hlim1 (isCompact_orbitPair x T) hε
  have hev2 : ∀ ε > 0, ∀ᶠ h in F.l, ∀ ζ ∈ P2, g h ζ < ε := fun ε hε =>
    eventually_forall_lt_of_tendsto_on (f := g) (M := 3 * F.toFamily.boundConst)
      (fun h ζ ζ' => F.toFamily.defect_le h ζ ζ') hlim2 (isCompact_orbitPair (waveExt H x) T) hε
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hev1 _ (half_pos hε), hev2 _ (half_pos hε)] with h h1 h2 t ht
  rw [dist_eq_norm, zero_sub, norm_neg, Real.norm_of_nonneg (norm_nonneg _),
    crimeCmp_defect F T hx h ht.1]
  refine (norm_sub_le _ _).trans_lt ?_
  have a1 : ‖F.toFamily.load h (H.waveGroup.S t x - H.waveGroup.S t (waveExt H x)) -
      (F.toFamily.incl h).adjoint (H.waveGroup.S t x)‖ < ε / 2 :=
    h1 (H.waveGroup.S t x, H.waveGroup.S t (waveExt H x)) ⟨t, ht, rfl⟩
  have a2 : ‖F.toFamily.load h (H.waveGroup.S t (waveExt H x) -
      H.waveGroup.S t (waveExt H (waveExt H x))) -
      (F.toFamily.incl h).adjoint (H.waveGroup.S t (waveExt H x))‖ < ε / 2 :=
    h2 (H.waveGroup.S t (waveExt H x), H.waveGroup.S t (waveExt H (waveExt H x))) ⟨t, ht, rfl⟩
  exact lt_of_lt_of_eq (add_lt_add a2 a1) (add_halves ε)

/-- **The core of `ofComplexCrime`**: data `Z`, with the comparison `crimeCmp`. -/
def ofComplexCrimeCore : (ofComplexCrime F).Core where
  Data := F.Z
  cmp T := crimeCmp F T
  data_eq _ := rfl
  tendsto_approx T _ hx := ((crimeCmp_tendsto_approx F T hx).congr
    (Eventually.of_forall fun h _ ht => congrArg (F.toFamily.incl h)
      (crimeCmp_p F T (domainSq_le_domain (F.Z_le hx)) h ht.1).symm)).congr_right
    fun _ ht => (DFunLike.congr_fun ((ofComplexCrime F).S_eq_waveGroup ht.1) _).symm
  tendsto_defect T _ hx := crimeCmp_tendsto_defect F T hx

theorem ofComplexCrimeCore_cmp (T : ℝ) : (ofComplexCrimeCore F).cmp T = crimeCmp F T := rfl

end ApproxFEEC

open ApproxFEEC in
/-- **The approximating FEEC theorem for approximating families of discrete differential
spaces**, with the discrete constraints and the Strang, residual and defect bounds. -/
theorem approxFEEC_ofComplexCrime {H : HilbertComplex 𝕜 c W} {κ : Type*}
    (F : ApproxComplexCrime.{u} H κ) :
    (ofComplexCrime F).Verdict (ofComplexCrimeCore F) ∧
    -- 2. the discrete generator
    (∀ h, (ofComplexCrime F).L h = F.toFamily.D h - (F.toFamily.D h).adjoint) ∧
    -- 3. discrete constraints
    (∀ h (Kh : Submodule 𝕜 (F.toFamily.X h)), (∀ v ∈ Kh, F.toFamily.L h v ∈ Kh) →
      ∀ v ∈ Kh, ∀ t, ((ofComplexCrime F).group h).S t v ∈ Kh) ∧
    (∀ h (Kh : Submodule 𝕜 (F.toFamily.X h)), (∀ v ∈ Kh, F.toFamily.L h v ∈ Kh) →
      Kh.map (F.toFamily.incl h : F.toFamily.X h →ₗ[𝕜] PiLp 2 W) ≤ F.K →
      ∀ v ∈ Kh, ∀ t, infDist ((ofComplexCrime F).sol h v t) (F.K : Set (PiLp 2 W)) = 0) ∧
    -- 4. the Strang estimate, the residual splitting, the defect bound, and their limits
    (∀ h (y z : PiLp 2 W) (w : F.toFamily.X h) (ε : ℝ), 0 ≤ ε →
      (∀ v, ‖⟪w - F.toFamily.L h w, v⟫_𝕜 - ⟪z, F.toFamily.incl h v⟫_𝕜‖ ≤
        ε * (‖v‖ + ‖F.toFamily.D h v‖)) →
      ‖y - F.toFamily.incl h (F.toFamily.load h z)‖ ≤
        ‖y - F.toFamily.incl h w‖ + 8 * F.toFamily.boundConst * ε) ∧
    (∀ h (y : H.wave.domain) (w : F.toFamily.X h) (δ : ℝ),
      (∀ v, ‖⟪F.toFamily.cochainDefect h y, v⟫_𝕜‖ ≤ δ * (‖v‖ + ‖F.toFamily.D h v‖)) → ∀ v,
      ‖⟪w - F.toFamily.L h w, v⟫_𝕜 - ⟪(y : PiLp 2 W) - H.wave y, F.toFamily.incl h v⟫_𝕜‖ ≤
        (‖(1 - F.toFamily.J h) w‖ + ‖(1 - F.toFamily.J h) (F.toFamily.D h w)‖ +
          F.toFamily.boundConst * (‖(y : PiLp 2 W) - F.toFamily.incl h w‖ +
            ‖H.totalD ⟨y, y.2.1⟩ - F.toFamily.incl h (F.toFamily.D h w)‖) + δ) *
          (‖v‖ + ‖F.toFamily.D h v‖)) ∧
    (∀ h (y z : PiLp 2 W), ‖F.toFamily.load h z - (F.toFamily.incl h).adjoint y‖ ≤
      ‖(1 - F.toFamily.J h) (F.toFamily.load h z)‖ +
        F.toFamily.boundConst * ‖y - F.toFamily.incl h (F.toFamily.load h z)‖) ∧
    (∀ y ∈ F.A, Tendsto (fun h => ‖y - F.toFamily.incl h
      (F.toFamily.load h (y - waveExt H y))‖) F.l (𝓝 0)) ∧
    (∀ y ∈ F.A, Tendsto (fun h => ‖F.toFamily.load h (y - waveExt H y) -
      (F.toFamily.incl h).adjoint y‖) F.l (𝓝 0)) := by
  set S := F.toFamily
  have hinv : ∀ h (Kh : Submodule 𝕜 (S.X h)), (∀ v ∈ Kh, S.L h v ∈ Kh) →
      ∀ v ∈ Kh, ∀ t, ((ofComplexCrime F).group h).S t v ∈ Kh := fun h Kh hK v hv t =>
    mem_of_invariant (S.L h) (diffWave_skew (S.D h)) Kh hK hv t
  refine ⟨approxFEEC _ _, ofComplexCrime_L F, hinv, fun h Kh hK hKK v hv t => ?_,
    fun h y z w ε hε hres => S.norm_sub_incl_load_le h y z w hε hres,
    fun h y w δ hδ v => S.norm_residual_le h y w hδ v, S.norm_load_sub_adjoint_le,
    fun y hy => F.tendsto_incl_load hy, fun y hy => F.tendsto_defect hy⟩
  exact Metric.infDist_zero_of_mem (hKK ⟨_, hinv h Kh hK v hv t, rfl⟩)

end OfComplexCrime

end Families

/-! ### From the split hypotheses -/

section Split

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

namespace ApproxComplexCrime.Family

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (S : ApproxComplexCrime.Family.{u} H κ)

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem consistent_of_cochainDefect {l : Filter κ} {y : PiLp 2 W} (hy : y ∈ H.wave.domain)
    (hJ : Tendsto S.graphDefect l (𝓝 0))
    (hgraph : ∀ ε > 0, ∀ᶠ h in l, ∃ w : S.X h,
      ‖y - S.incl h w‖ + ‖H.totalD ⟨y, hy.1⟩ - S.incl h (S.D h w)‖ < ε)
    (hcd : ∀ ε > 0, ∀ᶠ h in l, ∀ v : S.X h,
      ‖⟪S.cochainDefect h ⟨y, hy⟩, v⟫_𝕜‖ ≤ ε * (‖v‖ + ‖S.D h v‖)) :
    ∀ ε > 0, ∀ᶠ h in l, ∃ w : S.X h, ‖y - S.incl h w‖ ≤ ε ∧ ∀ v,
      ‖⟪w - S.L h w, v⟫_𝕜 - ⟪y - waveExt H y, S.incl h v⟫_𝕜‖ ≤ ε * (‖v‖ + ‖S.D h v‖) := by
  intro ε hε
  set C := S.boundConst
  have hC := S.boundConst_nonneg
  set dy := H.totalD ⟨y, hy.1⟩
  set M0 := C * (‖y‖ + ‖dy‖ + 2)
  have hM0 : 0 ≤ M0 := by positivity
  set η := min 1 (ε / (3 * (C + 1)))
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η ≤ ε / (3 * (C + 1)) := min_le_right _ _
  set θ := ε / (3 * (2 * M0 + 1))
  have hθ : 0 < θ := by positivity
  filter_upwards [hgraph η hη, Metric.tendsto_nhds.1 hJ θ hθ, hcd (ε / 3) (by positivity)]
    with h ⟨w, hw⟩ hJh hcdh
  rw [dist_eq_norm, sub_zero, Real.norm_of_nonneg (S.graphDefect_nonneg h)] at hJh
  have ha := norm_nonneg (y - S.incl h w)
  have hb := norm_nonneg (dy - S.incl h (S.D h w))
  have hCη : C * η ≤ ε / 3 := by
    have h1 : C * η ≤ C * (ε / (3 * (C + 1))) := mul_le_mul_of_nonneg_left hηε hC
    have h2 : C * (ε / (3 * (C + 1))) ≤ ε / 3 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hεη : η ≤ ε := by
    have : ε / (3 * (C + 1)) ≤ ε := div_le_self hε.le (by nlinarith)
    linarith
  refine ⟨w, by linarith, fun v => ?_⟩
  have hres := S.norm_residual_le h ⟨y, hy⟩ w hcdh v
  rw [waveExt_of_mem hy]
  refine hres.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  -- the three terms
  have hwn : ‖w‖ ≤ C * (‖y‖ + η) := by
    refine (S.norm_le_norm_incl h w).trans (mul_le_mul_of_nonneg_left ?_ hC)
    have := norm_sub_norm_le (S.incl h w) y
    rw [norm_sub_rev] at this
    linarith
  have hDwn : ‖S.D h w‖ ≤ C * (‖dy‖ + η) := by
    refine (S.norm_le_norm_incl h _).trans (mul_le_mul_of_nonneg_left ?_ hC)
    have := norm_sub_norm_le (S.incl h (S.D h w)) dy
    rw [norm_sub_rev] at this
    linarith
  have t1 : ‖(1 - S.J h) w‖ + ‖(1 - S.J h) (S.D h w)‖ ≤ ε / 3 := by
    have e1 : ‖w‖ + 2 * ‖S.D h w‖ ≤ 2 * M0 := by
      have : C * (‖y‖ + η) + 2 * (C * (‖dy‖ + η)) ≤ 2 * M0 := by
        have h1 : C * η ≤ C * 1 := mul_le_mul_of_nonneg_left hη1 hC
        have h2 : 0 ≤ C * ‖y‖ := mul_nonneg hC (norm_nonneg _)
        simp only [M0]; nlinarith
      linarith
    have e2 : S.graphDefect h * (‖w‖ + 2 * ‖S.D h w‖) ≤ θ * (2 * M0) :=
      mul_le_mul hJh.le e1 (by positivity) hθ.le
    have e3 : θ * (2 * M0) ≤ ε / 3 := by
      simp only [θ]
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith [S.norm_one_sub_J_add_le h w]
  have t2 : C * (‖(⟨y, hy⟩ : H.wave.domain).1 - S.incl h w‖ +
      ‖H.totalD ⟨(⟨y, hy⟩ : H.wave.domain), (⟨y, hy⟩ : H.wave.domain).2.1⟩ -
        S.incl h (S.D h w)‖) ≤ ε / 3 := by
    have : C * (‖y - S.incl h w‖ + ‖dy - S.incl h (S.D h w)‖) ≤ C * η :=
      mul_le_mul_of_nonneg_left hw.le hC
    exact this.trans hCη
  linarith

end ApproxComplexCrime.Family

/-- An **approximating family from graph-norm approximation and a cochain defect `→ 0`**. -/
def ApproxComplexCrime.ofCochainDefect {H : HilbertComplex 𝕜 c W} {κ : Type*}
    (S : ApproxComplexCrime.Family.{u} H κ) (K : Submodule 𝕜 (PiLp 2 W))
    (hK : IsClosed (K : Set (PiLp 2 W))) (l : Filter κ) (A : Set (PiLp 2 W))
    (hA : A ⊆ H.wave.domain) (Z : Submodule 𝕜 (PiLp 2 W)) (hZ : Z ≤ H.wave.domainSq)
    (horbit : ∀ x ∈ Z, ∀ t : ℝ, 0 ≤ t →
      H.waveGroup.S t x ∈ A ∧ H.waveGroup.S t (waveExt H x) ∈ A)
    (hJ : Tendsto S.graphDefect l (𝓝 0))
    (hgraph : ∀ y (hy : y ∈ A), ∀ ε > 0, ∀ᶠ h in l, ∃ w : S.X h,
      ‖y - S.incl h w‖ + ‖H.totalD ⟨y, (hA hy).1⟩ - S.incl h (S.D h w)‖ < ε)
    (hcd : ∀ y (hy : y ∈ A), ∀ ε > 0, ∀ᶠ h in l, ∀ v : S.X h,
      ‖⟪S.cochainDefect h ⟨y, hA hy⟩, v⟫_𝕜‖ ≤ ε * (‖v‖ + ‖S.D h v‖)) :
    ApproxComplexCrime.{u} H κ where
  toFamily := S
  K := K
  isClosed_K := hK
  l := l
  A := A
  A_sub := hA
  Z := Z
  Z_le := hZ
  orbit_mem := horbit
  tendsto_graphDefect := hJ
  consistent y hy := S.consistent_of_cochainDefect (hA hy) hJ (hgraph y hy) (hcd y hy)

end Split

/-! ### The cochain special case: `ofComplex` -/

section Cochain

namespace ApproxComplex.Family

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (S : ApproxComplex.Family.{u} H κ)

/-- A family of discrete complexes as a family of discrete differential spaces. -/
def toCrimeFamily : ApproxComplexCrime.Family H κ where
  X h := PiLp 2 (S.V h)
  D h := S.D h
  D_D h v := (S.cpx h).totalDL_totalDL v
  incl := S.inclL
  proj := S.projL
  proj_incl := S.projL_inclL
  bound := ⟨S.boundConst, fun h => ⟨S.norm_inclL_le h, S.norm_projL_le h⟩⟩

theorem graphDefect_toCrimeFamily (h : κ) : S.toCrimeFamily.graphDefect h = S.graphDefect h :=
  rfl

theorem cochainDefect_toCrimeFamily (h : κ) (y : H.wave.domain) :
    S.toCrimeFamily.cochainDefect h y = 0 :=
  S.toCrimeFamily.cochainDefect_eq_zero h (S.inclL_mem h) (fun v => (S.inclL_D h v).symm) y

theorem ellProj_waveLift_eq_load (h : κ) (y : H.wave.domain) :
    S.ellProj h (waveLift H y) = S.toCrimeFamily.load h ((y : PiLp 2 W) - H.wave y) :=
  S.toCrimeFamily.eq_load h ((S.ellProj_sub h _).trans (S.G_waveLift h y))

end ApproxComplex.Family

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

namespace ApproxComplex

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxComplex.{u} H κ)

/-- **An approximating family of discrete complexes as one of discrete differential spaces**. -/
def toCrime : ApproxComplexCrime H κ :=
  ApproxComplexCrime.ofCochainDefect F.toFamily.toCrimeFamily F.K F.isClosed_K F.l
    H.wave.domain (fun _ hy => hy) H.wave.domainSq le_rfl
    (fun x hx t _ => ⟨waveGroup_mem_domain H (domainSq_le_domain hx) t,
      waveGroup_mem_domain H (waveExt_mem_domain H hx) t⟩)
    F.tendsto_graphDefect
    (fun y hy ε hε => (F.graphApprox (waveLift H ⟨y, hy⟩) (ε / 2) (half_pos hε)).mono
      fun h ⟨w, hw⟩ => ⟨w, by
        have e1 : y - F.toFamily.inclL h w =
            H.totalD.graphFst (waveLift H ⟨y, hy⟩ - F.toFamily.graphIncl h w) := by
          rw [H.totalD.graphFst.map_sub, F.toFamily.graphFst_graphIncl]; rfl
        have e2 : H.totalD ⟨y, hy.1⟩ - F.toFamily.inclL h (F.toFamily.D h w) =
            H.totalD.graphSnd (waveLift H ⟨y, hy⟩ - F.toFamily.graphIncl h w) := by
          rw [H.totalD.graphSnd.map_sub, F.toFamily.graphSnd_graphIncl]; rfl
        have h1 := norm_graphFst_le (waveLift H ⟨y, hy⟩ - F.toFamily.graphIncl h w)
        have h2 := norm_graphSnd_le (waveLift H ⟨y, hy⟩ - F.toFamily.graphIncl h w)
        change ‖y - F.toFamily.inclL h w‖ +
          ‖H.totalD ⟨y, hy.1⟩ - F.toFamily.inclL h (F.toFamily.D h w)‖ < ε
        rw [e1, e2]
        linarith⟩)
    (fun y hy ε hε => Eventually.of_forall fun h v => by
      rw [F.toFamily.cochainDefect_toCrimeFamily, inner_zero_left, norm_zero]
      positivity)

end ApproxComplex

namespace ApproxFEEC

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxComplex.{u} H κ)

/-- **`ofComplex` is the cochain special case of `ofComplexCrime`**. -/
theorem ofComplexCrime_toCrime : ofComplexCrime F.toCrime = ofComplex F := rfl

theorem ofComplexCrimeCore_toCrime_p (T : ℝ) {x : PiLp 2 W} (hx : x ∈ H.wave.domainSq)
    (h : κ) {t : ℝ} (ht : 0 ≤ t) :
    ((ofComplexCrimeCore F.toCrime).cmp T).p x h t = ((ofComplexCore F).cmp T).p x h t := by
  have hx1 := domainSq_le_domain hx
  rw [ofComplexCrimeCore_cmp, crimeCmp_p_eq F.toCrime T hx h ht, ofComplexCore_cmp_p F T hx1 h ht,
    waveOrbit_of_mem H hx1, F.toFamily.ellProj_waveLift_eq_load,
    waveExt_of_mem (waveGroup_mem_domain H hx1 t)]
  rfl

end ApproxFEEC

namespace ConstrainedFEEC

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ConstrainedFEEC H κ)

/-- **The conforming case**: a constrained FEEC discretization as an approximating family. -/
abbrev toCrime : ApproxComplexCrime H κ := F.toComplex.toCrime

theorem toCrime_J (h : κ) : F.toCrime.toFamily.J h = 1 := F.toFamily_J h

theorem toCrime_cochainDefect (h : κ) (y : H.wave.domain) :
    F.toCrime.toFamily.cochainDefect h y = 0 :=
  F.toFamily.cochainDefect_toCrimeFamily h y

theorem toCrime_sol (h : κ) (v : PiLp 2 (F.toFamily.V h)) (t : ℝ) :
    (ApproxFEEC.ofComplexCrime F.toCrime).sol h v t = F.toApprox.sol h (F.toXh h v) t :=
  F.toComplex_sol h v t

end ConstrainedFEEC

end Cochain

/-! ### Rates from complex-level estimates -/

section Rate

namespace ApproxComplexCrime.Family

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (S : ApproxComplexCrime.Family.{u} H κ)

/-- The approximation constant `1 + 8 C` of the Strang lemma. -/
def rateConstA : ℝ := 1 + 8 * S.boundConst

/-- The consistency constant `1 + 8 (1 + C²) + C (1 + 8 C)` of the defect bound. -/
def rateConstD : ℝ := 1 + 8 * (1 + S.boundConst ^ 2) + S.boundConst * (1 + 8 * S.boundConst)

theorem norm_sub_incl_load_le_of_rate (h : κ) (y z : PiLp 2 W) (w : S.X h) {ε : ℝ}
    (hw : ‖y - S.incl h w‖ ≤ ε)
    (hres : ∀ v, ‖⟪w - S.L h w, v⟫_𝕜 - ⟪z, S.incl h v⟫_𝕜‖ ≤ ε * (‖v‖ + ‖S.D h v‖)) :
    ‖y - S.incl h (S.load h z)‖ ≤ S.rateConstA * ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hw
  have := S.norm_sub_incl_load_le h y z w hε hres
  unfold rateConstA; nlinarith

theorem norm_load_sub_adjoint_le_of_rate (h : κ) (y z : PiLp 2 W) (w : S.X h) {ε : ℝ}
    (hw : ‖y - S.incl h w‖ ≤ ε) (hJw : ‖(1 - S.J h) w‖ ≤ ε)
    (hres : ∀ v, ‖⟪w - S.L h w, v⟫_𝕜 - ⟪z, S.incl h v⟫_𝕜‖ ≤ ε * (‖v‖ + ‖S.D h v‖)) :
    ‖S.load h z - (S.incl h).adjoint y‖ ≤ S.rateConstD * ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hw
  set C := S.boundConst
  have hC := S.boundConst_nonneg
  have h1 := S.norm_sub_load_add_le h z w hε hres
  have h2 : ‖w - S.load h z‖ ≤ 8 * ε := by linarith [norm_nonneg (S.D h (w - S.load h z))]
  have h3 := S.norm_sub_incl_load_le_of_rate h y z w hw hres
  have h4 : ‖(1 - S.J h) (S.load h z)‖ ≤ ε + (1 + C ^ 2) * (8 * ε) := by
    have e : (1 - S.J h) (S.load h z) = (1 - S.J h) w - (1 - S.J h) (w - S.load h z) := by
      rw [_root_.map_sub]; abel
    rw [e]
    refine (norm_sub_le _ _).trans (add_le_add hJw ?_)
    exact ((1 - S.J h).le_opNorm _).trans (mul_le_mul (S.norm_one_sub_J_le h) h2
      (norm_nonneg _) (by positivity))
  refine (S.norm_load_sub_adjoint_le h y z).trans ?_
  have h5 := mul_le_mul_of_nonneg_left h3 hC
  unfold rateConstD
  unfold rateConstA at h5
  nlinarith

theorem rateData_of_split (h : κ) (y : H.wave.domain) (w : S.X h) {Ea Eb Eg : ℝ}
    (ha : ‖(y : PiLp 2 W) - S.incl h w‖ + ‖H.totalD ⟨y, y.2.1⟩ - S.incl h (S.D h w)‖ ≤ Ea)
    (hb : ‖(1 - S.J h) w‖ + ‖(1 - S.J h) (S.D h w)‖ ≤ Eb)
    (hcd : ∀ v, ‖⟪S.cochainDefect h y, v⟫_𝕜‖ ≤ Eg * (‖v‖ + ‖S.D h v‖)) :
    ‖(y : PiLp 2 W) - S.incl h w‖ ≤ Ea ∧ ‖(1 - S.J h) w‖ ≤ Eb ∧
      ∀ v, ‖⟪w - S.L h w, v⟫_𝕜 - ⟪(y : PiLp 2 W) - H.wave y, S.incl h v⟫_𝕜‖ ≤
        (Eb + S.boundConst * Ea + Eg) * (‖v‖ + ‖S.D h v‖) := by
  have hd := norm_nonneg (H.totalD ⟨y, y.2.1⟩ - S.incl h (S.D h w))
  refine ⟨by linarith, by linarith [norm_nonneg ((1 - S.J h) (S.D h w))], fun v => ?_⟩
  refine (S.norm_residual_le h y w hcd v).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  have e := mul_le_mul_of_nonneg_left ha S.boundConst_nonneg
  linarith

end ApproxComplexCrime.Family

theorem add_rpow_le_rpow_min {m α β γ A B G : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hG : 0 ≤ G) :
    A * m ^ α + B * m ^ β + G * m ^ γ ≤ (A + B + G) * m ^ min α (min β γ) := by
  have hμ : 0 ≤ min α (min β γ) := le_min hα (le_min hβ hγ)
  have h1 : m ^ α ≤ m ^ min α (min β γ) :=
    Real.rpow_le_rpow_of_exponent_ge' hm0 hm1 hμ (min_le_left _ _)
  have h2 : m ^ β ≤ m ^ min α (min β γ) :=
    Real.rpow_le_rpow_of_exponent_ge' hm0 hm1 hμ ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : m ^ γ ≤ m ^ min α (min β γ) :=
    Real.rpow_le_rpow_of_exponent_ge' hm0 hm1 hμ ((min_le_right _ _).trans (min_le_right _ _))
  nlinarith [mul_le_mul_of_nonneg_left h1 hA, mul_le_mul_of_nonneg_left h2 hB,
    mul_le_mul_of_nonneg_left h3 hG]

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

namespace ApproxComplexCrime

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxComplexCrime.{u} H κ)

open ApproxFEEC in
/-- **A rate class from complex-level rate data** along the trajectories. -/
def rateClass (T : ℝ) (Dc : Set (PiLp 2 W)) (hDc : Dc ⊆ (F.Z : Set (PiLp 2 W)))
    (cn : PiLp 2 W → ℝ) (m : κ → ℝ) (α Ca : ℝ)
    (hrate : ∀ x ∈ Dc, ∀ h, ∀ t ∈ Icc 0 T, ∀ y ∈ ({H.waveGroup.S t x,
      H.waveGroup.S t (waveExt H x)} : Set (PiLp 2 W)), ∃ w : F.toFamily.X h,
      ‖y - F.toFamily.incl h w‖ ≤ Ca * m h ^ α * cn x ∧
      ‖(1 - F.toFamily.J h) w‖ ≤ Ca * m h ^ α * cn x ∧
      ∀ v, ‖⟪w - F.toFamily.L h w, v⟫_𝕜 - ⟪y - waveExt H y, F.toFamily.incl h v⟫_𝕜‖ ≤
        Ca * m h ^ α * cn x * (‖v‖ + ‖F.toFamily.D h v‖)) :
    (ofComplexCrime F).RateClass T :=
  (loadRitz F).orbitRateClass Dc (fun _ hx =>
      DissipFEEC.domainSq_le_resData (ofComplexCrime F).isMDissipative (F.Z_le (hDc hx)))
    cn m α (F.toFamily.rateConstA * Ca) (2 * F.toFamily.rateConstD * Ca)
    (fun x hx h t ht => by
      obtain ⟨w, hw, -, hres⟩ := hrate x hx h t ht _ (Set.mem_insert _ _)
      change ‖(ofComplexCrime F).S t x - F.toFamily.incl h (F.toFamily.load h
        ((ofComplexCrime F).S t x - DissipFEEC.genExt H.wave ((ofComplexCrime F).S t x)))‖ ≤ _
      rw [(ofComplexCrime F).S_eq_waveGroup ht.1, ← waveExt_eq_genExt]
      calc _ ≤ _ := F.toFamily.norm_sub_incl_load_le_of_rate h _ _ w hw hres
        _ = _ := by ring)
    (fun x hx h t ht => by
      have hx2 := F.Z_le (hDc hx)
      have hx1 := domainSq_le_domain hx2
      have hLx := waveExt_mem_domain H hx2
      obtain ⟨w, hw, hJw, hres⟩ := hrate x hx h t ht _ (Set.mem_insert _ _)
      obtain ⟨w', hw', hJw', hres'⟩ := hrate x hx h t ht _
        (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      have d1 := F.toFamily.norm_load_sub_adjoint_le_of_rate h _ _ w hw hJw hres
      have d2 := F.toFamily.norm_load_sub_adjoint_le_of_rate h _ _ w' hw' hJw' hres'
      change ‖loadDefect F h ((ofComplexCrime F).S t (DissipFEEC.genExt H.wave x) -
          DissipFEEC.genExt H.wave ((ofComplexCrime F).S t (DissipFEEC.genExt H.wave x)))‖ +
        ‖-loadDefect F h ((ofComplexCrime F).S t x -
          DissipFEEC.genExt H.wave ((ofComplexCrime F).S t x))‖ ≤ _
      rw [(ofComplexCrime F).S_eq_waveGroup ht.1, ← waveExt_eq_genExt, norm_neg,
        loadDefect_apply F h (waveGroup_mem_domain H hLx t),
        loadDefect_apply F h (waveGroup_mem_domain H hx1 t)]
      calc _ ≤ F.toFamily.rateConstD * (Ca * m h ^ α * cn x) +
            F.toFamily.rateConstD * (Ca * m h ^ α * cn x) := add_le_add d2 d1
        _ = _ := by ring)

theorem error_le_of_rateClass {T : ℝ} (R : (ApproxFEEC.ofComplexCrime F).RateClass T)
    {x : PiLp 2 W} (hx : x ∈ R.Data) (h : κ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖H.waveGroup.S t x - (ApproxFEEC.ofComplexCrime F).sol h (R.p x h 0) t‖ ≤
      (R.C + F.toFamily.boundConst * R.C' * t) * (R.meshSize h ^ R.α * R.classNorm x) := by
  have hr := dissipFEEC_rate _ R hx h (R.p x h 0) ht
  rw [ApproxFEEC.S_eq_waveGroup _ ht.1, sub_self, norm_zero, mul_zero, add_zero] at hr
  refine hr.trans ?_
  have h0 : 0 ≤ R.C' * (R.meshSize h ^ R.α * R.classNorm x) := by
    have := (norm_nonneg _).trans (R.consistency x hx h t ht)
    linarith [show R.C' * R.meshSize h ^ R.α * R.classNorm x =
      R.C' * (R.meshSize h ^ R.α * R.classNorm x) by ring]
  have hI : ‖(ApproxFEEC.ofComplexCrime F).incl h‖ ≤ F.toFamily.boundConst :=
    F.toFamily.norm_incl_le h
  have hpos : 0 ≤ t * (R.C' * (R.meshSize h ^ R.α * R.classNorm x)) := mul_nonneg ht.1 h0
  have e1 : (R.C + ‖(ApproxFEEC.ofComplexCrime F).incl h‖ * R.C' * t) *
      (R.meshSize h ^ R.α * R.classNorm x) = R.C * (R.meshSize h ^ R.α * R.classNorm x) +
        ‖(ApproxFEEC.ofComplexCrime F).incl h‖ *
          (t * (R.C' * (R.meshSize h ^ R.α * R.classNorm x))) := by
    ring
  have e2 : (R.C + F.toFamily.boundConst * R.C' * t) * (R.meshSize h ^ R.α * R.classNorm x) =
      R.C * (R.meshSize h ^ R.α * R.classNorm x) +
        F.toFamily.boundConst * (t * (R.C' * (R.meshSize h ^ R.α * R.classNorm x))) := by ring
  rw [e1, e2]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hI hpos)

end ApproxComplexCrime

/-! #### The conforming case: rates through `ofComplex` -/

namespace ConstrainedFEEC

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ConstrainedFEEC H κ)

theorem exists_graphIncl_eq {h : κ} {w : H.totalD.GraphSpace} (hw : w ∈ F.Kh h) :
    ∃ u : PiLp 2 (F.toFamily.V h), F.toFamily.graphIncl h u = w :=
  ⟨WithLp.toLp 2 fun i => ⟨H.totalD.graphFst w i, hw i⟩,
    H.totalD.graphFst_injective (PiLp.ext fun _ => rfl)⟩

/-- The rate classes of a constrained FEEC discretization as rate classes of `ofComplex`. -/
def RateClass.toCrimeRate {T : ℝ} (R : F.RateClass T) :
    (ApproxFEEC.ofComplexCrime F.toComplex.toCrime).RateClass T :=
  F.toComplex.toCrime.rateClass T R.Data
    (fun x hx => mem_domainSq.2 ⟨R.mem_domain x hx, R.mem_domain_sq x _ hx⟩)
    R.classNorm R.meshSize R.α (2 * (1 + F.toFamily.toCrimeFamily.boundConst) * R.C)
    fun x hx h t ht y hy => by
      set S := F.toFamily
      have hx1 := R.mem_domain x hx
      have hC := S.toCrimeFamily.boundConst_nonneg
      have key : ∀ (y : H.wave.domain) (w : H.totalD.GraphSpace), w ∈ F.Kh h →
          ‖waveLift H y - w‖ ≤ R.C * R.meshSize h ^ R.α * R.classNorm x →
          ∃ u : F.toComplex.toCrime.toFamily.X h,
            ‖(y : PiLp 2 W) - F.toComplex.toCrime.toFamily.incl h u‖ ≤
              2 * (1 + S.toCrimeFamily.boundConst) * R.C * R.meshSize h ^ R.α * R.classNorm x ∧
            ‖(1 - F.toComplex.toCrime.toFamily.J h) u‖ ≤
              2 * (1 + S.toCrimeFamily.boundConst) * R.C * R.meshSize h ^ R.α * R.classNorm x ∧
            ∀ v, ‖⟪u - F.toComplex.toCrime.toFamily.L h u, v⟫_𝕜 -
              ⟪(y : PiLp 2 W) - waveExt H y, F.toComplex.toCrime.toFamily.incl h v⟫_𝕜‖ ≤
              2 * (1 + S.toCrimeFamily.boundConst) * R.C * R.meshSize h ^ R.α * R.classNorm x *
                (‖v‖ + ‖F.toComplex.toCrime.toFamily.D h v‖) := by
        intro y w hw hle
        obtain ⟨u, rfl⟩ := F.exists_graphIncl_eq hw
        set Rc := R.C * R.meshSize h ^ R.α * R.classNorm x
        have hRc : 0 ≤ Rc := (norm_nonneg _).trans hle
        have e1 : (y : PiLp 2 W) - S.inclL h u =
            H.totalD.graphFst (waveLift H y - S.graphIncl h u) := by
          rw [H.totalD.graphFst.map_sub, S.graphFst_graphIncl]; rfl
        have e2 : H.totalD ⟨y, y.2.1⟩ - S.inclL h (S.D h u) =
            H.totalD.graphSnd (waveLift H y - S.graphIncl h u) := by
          rw [H.totalD.graphSnd.map_sub, S.graphSnd_graphIncl]; rfl
        have ha : ‖(y : PiLp 2 W) - S.inclL h u‖ ≤ Rc := by
          rw [e1]; exact (norm_graphFst_le _).trans hle
        have hb : ‖H.totalD ⟨y, y.2.1⟩ - S.inclL h (S.D h u)‖ ≤ Rc := by
          rw [e2]; exact (norm_graphSnd_le _).trans hle
        have hJ : S.toCrimeFamily.J h = 1 := F.toFamily_J h
        have hres := fun v => (S.toCrimeFamily.norm_residual_le h y u (δ := 0) (fun v => by
          rw [S.cochainDefect_toCrimeFamily, inner_zero_left, norm_zero, zero_mul]) v).trans
          (mul_le_mul_of_nonneg_right (add_le_add_left (add_le_add_left
            (S.toCrimeFamily.norm_one_sub_J_add_le_opNorm h u) _) _) (by positivity))
        refine ⟨u, ?_, ?_, fun v => ?_⟩
        · change ‖(y : PiLp 2 W) - S.inclL h u‖ ≤ _
          nlinarith
        · change ‖(1 - S.toCrimeFamily.J h) u‖ ≤ _
          refine ((1 - S.toCrimeFamily.J h).le_opNorm u).trans ?_
          rw [hJ, sub_self, norm_zero, zero_mul]
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * (1 + S.toCrimeFamily.boundConst)) hRc]
        · have h1 := hres v
          rw [hJ, sub_self, norm_zero, zero_mul, zero_add, add_zero] at h1
          rw [waveExt_of_mem y.2]
          refine h1.trans (mul_le_mul_of_nonneg_right ?_
            (add_nonneg (norm_nonneg _) (norm_nonneg _)))
          change S.toCrimeFamily.boundConst * (‖(y : PiLp 2 W) - S.inclL h u‖ +
            ‖H.totalD ⟨y, y.2.1⟩ - S.inclL h (S.D h u)‖) ≤ _
          nlinarith
      rcases hy with rfl | hy
      · obtain ⟨w, hw, hle⟩ := R.approx x hx h t ht
          (waveLift H ⟨_, waveGroup_mem_domain H hx1 t⟩) rfl
        exact key ⟨_, waveGroup_mem_domain H hx1 t⟩ w hw hle
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        have hLx : waveExt H x ∈ H.wave.domain := by
          rw [waveExt_of_mem hx1]; exact R.mem_domain_sq x hx1 hx
        obtain ⟨w, hw, hle⟩ := R.approx_deriv x hx1 hx h t ht
          (waveLift H ⟨_, waveGroup_mem_domain H hLx t⟩) (by
            change H.waveGroup.S t (waveExt H x) = _
            rw [waveExt_of_mem hx1])
        exact key ⟨_, waveGroup_mem_domain H hLx t⟩ w hw hle

variable {F} in
theorem RateClass.norm_sub_ofComplex_le {T : ℝ} (R : F.RateClass T) {x : PiLp 2 W}
    (hx : x ∈ R.Data) (h : κ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖H.waveGroup.S t x - (ApproxFEEC.ofComplex F.toComplex).sol h
        (((ApproxFEEC.ofComplexCore F.toComplex).cmp T).p x h 0) t‖ ≤
      (R.toCrimeRate.C + F.toComplex.toCrime.toFamily.boundConst * R.toCrimeRate.C' * t) *
        (R.meshSize h ^ R.α * R.classNorm x) := by
  rw [← ApproxFEEC.ofComplexCrimeCore_toCrime_p F.toComplex T
    (mem_domainSq.2 ⟨R.mem_domain x hx, R.mem_domain_sq x _ hx⟩) h le_rfl]
  exact F.toComplex.toCrime.error_le_of_rateClass R.toCrimeRate hx h ht

end ConstrainedFEEC

end Rate

/-! ### From a Galerkin core -/

section Galerkin

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  {H : HilbertComplex 𝕜 c W} {κ : Type*}

/-- The discrete differential spaces of an approximating FEEC discretization with a differential. -/
def ApproxComplexCrime.Family.ofApproxFEEC (F : ApproxFEEC.{u} H κ)
    [hfd : ∀ h, FiniteDimensional 𝕜 (F.X h)] (D : ∀ h, F.X h →L[𝕜] F.X h)
    (hDD : ∀ h v, D h (D h v) = 0) : ApproxComplexCrime.Family.{u} H κ where
  X := F.X
  normedAddCommGroup := F.normedAddCommGroup
  innerProductSpace := F.innerProductSpace
  completeSpace := F.completeSpace
  finiteDimensional := hfd
  normedSpaceReal := F.normedSpaceReal
  isScalarTower := F.isScalarTower
  D := D
  D_D := hDD
  incl := F.incl
  proj := F.proj
  proj_incl := F.proj_incl
  bound := F.bound

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem ApproxComplexCrime.Family.ofApproxFEEC_J (F : ApproxFEEC.{u} H κ)
    [hfd : ∀ h, FiniteDimensional 𝕜 (F.X h)] (D : ∀ h, F.X h →L[𝕜] F.X h)
    (hDD : ∀ h v, D h (D h v) = 0) (hF : F.IsOrthogonal) (h : κ) :
    (ApproxComplexCrime.Family.ofApproxFEEC F D hDD).J h = 1 :=
  ContinuousLinearMap.ext fun v => ext_inner_right 𝕜 fun w => by
    rw [ApproxComplexCrime.Family.inner_J, one_apply_eq_self]
    exact hF.inner_incl h v w

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem ApproxComplexCrime.Family.tendsto_graphDefect_ofApproxFEEC (F : ApproxFEEC.{u} H κ)
    [hfd : ∀ h, FiniteDimensional 𝕜 (F.X h)] (D : ∀ h, F.X h →L[𝕜] F.X h)
    (hDD : ∀ h v, D h (D h v) = 0) (hF : F.IsOrthogonal) :
    Tendsto (ApproxComplexCrime.Family.ofApproxFEEC F D hDD).graphDefect F.l (𝓝 0) :=
  tendsto_const_nhds.congr fun h =>
    (((ApproxComplexCrime.Family.ofApproxFEEC F D hDD).graphDefect_eq_zero_iff h).2
      (ApproxComplexCrime.Family.ofApproxFEEC_J F D hDD hF h)).symm

variable (H) in
/-- The **orbit states** of a set `Z ⊆ D(L²)`: `e^{tL} x` and `e^{tL} L x`, `x ∈ Z`, `t ≥ 0`. -/
def orbitStates (Z : Set (PiLp 2 W)) : Set (PiLp 2 W) :=
  {y | ∃ x ∈ Z, ∃ t : ℝ, 0 ≤ t ∧ (y = H.waveGroup.S t x ∨ y = H.waveGroup.S t (waveExt H x))}

theorem orbitStates_sub {Z : Set (PiLp 2 W)} (hZ : Z ⊆ H.wave.domainSq) :
    orbitStates H Z ⊆ H.wave.domain := by
  rintro y ⟨x, hx, t, -, rfl | rfl⟩
  · exact waveGroup_mem_domain H (domainSq_le_domain (hZ hx)) t
  · exact waveGroup_mem_domain H (waveExt_mem_domain H (hZ hx)) t

omit [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)] in
theorem ApproxFEEC.IsOrthogonal.adjoint_incl {F : ApproxFEEC.{u} H κ} (hF : F.IsOrthogonal)
    (h : κ) : (F.incl h).adjoint = F.proj h :=
  ContinuousLinearMap.ext fun y => ext_inner_right 𝕜 fun a => by
    rw [ContinuousLinearMap.adjoint_inner_left, ← inner_conj_symm, hF.inner_incl_left,
      inner_conj_symm]

section Bridge

variable (F : ApproxFEEC.{u} H κ) [hfd : ∀ h, FiniteDimensional 𝕜 (F.X h)] (hF : F.IsOrthogonal)
  (D : ∀ h, F.X h →L[𝕜] F.X h) (hDD : ∀ h v, D h (D h v) = 0)
  (hJ : Tendsto (ApproxComplexCrime.Family.ofApproxFEEC F D hDD).graphDefect F.l (𝓝 0))
  (hL : ∀ h, F.L h = diffWave (D h)) (Z0 : F.Core) (hZ : Z0.Data ≤ H.wave.domainSq)
  (hgal : ∀ T, ∀ x ∈ Z0.Data, ∀ h, ∀ t ∈ Ico 0 T,
    (Z0.cmp T).p x h t - F.L h ((Z0.cmp T).p x h t) =
      (F.incl h).adjoint (H.waveGroup.S t x - H.waveGroup.S t (waveExt H x)))
  (hcl : ∀ x ∈ Z0.Data, ∀ t : ℝ, 0 ≤ t →
    H.waveGroup.S t (waveExt H x) ∈ Z0.Data.topologicalClosure)

include hL hgal in
theorem galerkin_p_eq {T : ℝ} {x : PiLp 2 W} (hx : x ∈ Z0.Data) (h : κ) {t : ℝ}
    (ht : t ∈ Ico 0 T) :
    (Z0.cmp T).p x h t = (ApproxComplexCrime.Family.ofApproxFEEC F D hDD).load h
      (H.waveGroup.S t x - H.waveGroup.S t (waveExt H x)) :=
  (ApproxComplexCrime.Family.ofApproxFEEC F D hDD).eq_load h (by
    have e := hgal T x hx h t ht
    rw [hL] at e
    exact e)

include hL hgal hZ in
theorem galerkin_p'_eq {T : ℝ} {x : PiLp 2 W} (hx : x ∈ Z0.Data) (h : κ) {t : ℝ}
    (ht : t ∈ Ico 0 T) :
    (Z0.cmp T).p' x h t = (ApproxComplexCrime.Family.ofApproxFEEC F D hDD).load h
      (H.waveGroup.S t (waveExt H x) - H.waveGroup.S t (waveExt H (waveExt H x))) := by
  set S := ApproxComplexCrime.Family.ofApproxFEEC F D hDD
  have hx2 := hZ hx
  have hx' : x ∈ (Z0.cmp T).Data := by rw [Z0.data_eq]; exact hx
  have hp := (Z0.cmp T).hasDerivWithinAt x hx' h t ht
  have hq : HasDerivAt (fun s => S.load h (H.waveGroup.S s x - H.waveGroup.S s (waveExt H x)))
      (S.load h (H.waveGroup.S t (waveExt H x) - H.waveGroup.S t (waveExt H (waveExt H x)))) t :=
    ((S.load h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_waveGroup_waveExt H (domainSq_le_domain hx2) t).sub
        (hasDerivAt_waveGroup_waveExt H (waveExt_mem_domain H hx2) t))
  have heq : (Z0.cmp T).p x h =ᶠ[𝓝[Ici t] t]
      fun s => S.load h (H.waveGroup.S s x - H.waveGroup.S s (waveExt H x)) := by
    filter_upwards [Ico_mem_nhdsGE ht.2] with s hs
    exact galerkin_p_eq F D hDD hL Z0 hgal hx h ⟨ht.1.trans hs.1, hs.2⟩
  have hq' := hq.hasDerivWithinAt.congr_of_eventuallyEq heq
    (galerkin_p_eq F D hDD hL Z0 hgal hx h ht)
  exact (uniqueDiffWithinAt_Ici t).eq_deriv _ hp hq'

include hJ hL hgal in
theorem tendsto_incl_adjoint_galerkin {z : PiLp 2 W} (hz : z ∈ Z0.Data.topologicalClosure) :
    Tendsto (fun h => F.incl h ((F.incl h).adjoint z)) F.l (𝓝 z) := by
  set S := ApproxComplexCrime.Family.ofApproxFEEC F D hDD
  have hC := S.boundConst_nonneg
  refine ContinuousLinearMap.tendsto_apply_of_mem_closure
    (T := fun h => S.incl h ∘L (S.incl h).adjoint) (M := S.boundConst ^ 2) (fun h => ?_)
    continuous_id' (s := Z0.Data) (fun x hx => ?_) (by rwa [← Submodule.topologicalClosure_coe])
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [ContinuousLinearMap.adjoint.norm_map, pow_two]
    exact mul_le_mul (S.norm_incl_le h) (S.norm_incl_le h) (norm_nonneg _) hC
  · have hx1 : x ∈ Z0.Data := hx
    have hv : ∀ h, (Z0.cmp 1).p x h 0 = S.load h (x - waveExt H x) := fun h => by
      simpa only [C0Group.S_zero_apply] using
        galerkin_p_eq F D hDD hL Z0 hgal hx1 h (T := 1) ⟨le_rfl, one_pos⟩
    have h1 := tendsto_iff_norm_sub_tendsto_zero.1 (Z0.tendsto_incl_p zero_le_one hx1)
    have h2 : Tendsto (fun h => (S.boundConst ^ 2 + 1) * ‖F.incl h ((Z0.cmp 1).p x h 0) - x‖ +
        S.boundConst * (S.graphDefect h * (8 * S.boundConst * ‖x - waveExt H x‖))) F.l
        (𝓝 0) := by
      simpa using (h1.const_mul (S.boundConst ^ 2 + 1)).add
        ((hJ.mul_const (8 * S.boundConst * ‖x - waveExt H x‖)).const_mul S.boundConst)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun h => ?_) h2
    set v := (Z0.cmp 1).p x h 0
    have e : F.incl h ((F.incl h).adjoint x) - x =
        F.incl h ((F.incl h).adjoint (x - F.incl h v)) -
          F.incl h (v - (F.incl h).adjoint (F.incl h v)) + (F.incl h v - x) := by
      simp only [_root_.map_sub]
      abel
    have b1 : ‖F.incl h ((F.incl h).adjoint (x - F.incl h v))‖ ≤
        S.boundConst ^ 2 * ‖F.incl h v - x‖ := by
      refine (S.norm_incl_apply_le h _).trans ?_
      rw [pow_two, mul_assoc, norm_sub_rev (F.incl h v)]
      exact mul_le_mul_of_nonneg_left (S.norm_adjoint_incl_apply_le h _) hC
    have b2 : ‖F.incl h (v - (F.incl h).adjoint (F.incl h v))‖ ≤
        S.boundConst * (S.graphDefect h * (8 * S.boundConst * ‖x - waveExt H x‖)) := by
      refine (S.norm_incl_apply_le h _).trans (mul_le_mul_of_nonneg_left ?_ hC)
      have hv' : v = S.load h (x - waveExt H x) := hv h
      calc _ = ‖(1 - S.J h) v‖ := rfl
        _ ≤ _ := by rw [hv']; exact S.norm_one_sub_J_load_le h _
    have b3 := norm_sub_le (F.incl h ((F.incl h).adjoint (x - F.incl h v)))
      (F.incl h (v - (F.incl h).adjoint (F.incl h v)))
    have b4 := norm_add_le (F.incl h ((F.incl h).adjoint (x - F.incl h v)) -
      F.incl h (v - (F.incl h).adjoint (F.incl h v))) (F.incl h v - x)
    change ‖F.incl h ((F.incl h).adjoint x) - x‖ ≤ (S.boundConst ^ 2 + 1) * ‖F.incl h v - x‖ +
      S.boundConst * (S.graphDefect h * (8 * S.boundConst * ‖x - waveExt H x‖))
    rw [e]
    nlinarith

include hJ hL hgal hZ hcl in
theorem tendsto_reading_galerkin {y : PiLp 2 W} (hy : y ∈ orbitStates H Z0.Data) :
    Tendsto (fun h => ‖y - (ApproxComplexCrime.Family.ofApproxFEEC F D hDD).incl h
      ((ApproxComplexCrime.Family.ofApproxFEEC F D hDD).load h (y - waveExt H y))‖) F.l
      (𝓝 0) := by
  set S := ApproxComplexCrime.Family.ofApproxFEEC F D hDD
  obtain ⟨x, hx, t, ht0, rfl | rfl⟩ := hy
  · have hx2 := hZ hx
    have ht : t ∈ Ico 0 (t + 1) := ⟨ht0, by linarith⟩
    have h1 := (Z0.tendsto_approx (t + 1) x hx).tendsto_at (Ico_subset_Icc_self ht)
    rw [F.S_eq_waveGroup ht0] at h1
    have h2 := tendsto_iff_norm_sub_tendsto_zero.1 h1
    refine h2.congr fun h => ?_
    rw [norm_sub_rev, waveExt_waveGroup H (domainSq_le_domain hx2),
      galerkin_p_eq F D hDD hL Z0 hgal hx h ht]
    rfl
  · have hx2 := hZ hx
    have hLx := waveExt_mem_domain H hx2
    have ht : t ∈ Ico 0 (t + 1) := ⟨ht0, by linarith⟩
    set T := t + 1
    set p := fun h => (Z0.cmp T).p x h t
    set p' := fun h => (Z0.cmp T).p' x h t
    set y := H.waveGroup.S t x
    set y' := H.waveGroup.S t (waveExt H x)
    have hda : Tendsto (fun h => ‖F.incl h (p h) - y‖) F.l (𝓝 0) := by
      have := tendsto_iff_norm_sub_tendsto_zero.1
        ((Z0.tendsto_approx T x hx).tendsto_at (Ico_subset_Icc_self ht))
      rw [F.S_eq_waveGroup ht0] at this
      exact this
    have hdd : Tendsto (fun h => ‖p' h - F.L h (p h)‖) F.l (𝓝 0) := by
      have := (Z0.tendsto_defect T x hx).tendsto_at (Ico_subset_Icc_self ht)
      exact this
    have hii := tendsto_iff_norm_sub_tendsto_zero.1
      (tendsto_incl_adjoint_galerkin F D hDD hJ hL Z0 hgal (hcl x hx t ht0))
    have hC := S.boundConst_nonneg
    have key : ∀ h, ‖y' - F.incl h (p' h)‖ ≤ ‖F.incl h ((F.incl h).adjoint y') - y'‖ +
        S.boundConst * (‖p' h - F.L h (p h)‖ + S.boundConst * ‖F.incl h (p h) - y‖ +
          ‖(1 - S.J h) (p h)‖) := fun h => by
      have hg := hgal T x hx h t ht
      have e1 : (F.incl h).adjoint y' - p' h = -(p' h - F.L h (p h)) +
          ((F.incl h).adjoint (y - F.incl h (p h)) -
            (p h - (F.incl h).adjoint (F.incl h (p h)))) := by
        have hLp : F.L h (p h) = p h - (F.incl h).adjoint (y - y') := by rw [← hg]; abel
        rw [hLp]
        simp only [_root_.map_sub]
        abel
      have e2 : y' - F.incl h (p' h) = (y' - F.incl h ((F.incl h).adjoint y')) +
          F.incl h ((F.incl h).adjoint y' - p' h) := by rw [_root_.map_sub]; abel
      have b1 : ‖F.incl h ((F.incl h).adjoint y' - p' h)‖ ≤
          S.boundConst * ‖(F.incl h).adjoint y' - p' h‖ :=
        S.norm_incl_apply_le h _
      have b2 : ‖(F.incl h).adjoint (y - F.incl h (p h))‖ ≤
          S.boundConst * ‖F.incl h (p h) - y‖ := by
        rw [norm_sub_rev (F.incl h (p h))]
        exact S.norm_adjoint_incl_apply_le h _
      have b3 : ‖(F.incl h).adjoint y' - p' h‖ ≤ ‖p' h - F.L h (p h)‖ +
          (S.boundConst * ‖F.incl h (p h) - y‖ + ‖(1 - S.J h) (p h)‖) := by
        rw [e1]
        refine (norm_add_le _ _).trans (add_le_add (norm_neg _).le ?_)
        exact (norm_sub_le _ _).trans (add_le_add b2 (le_of_eq rfl))
      rw [e2]
      refine (norm_add_le _ _).trans (add_le_add (by rw [norm_sub_rev]) ?_)
      refine b1.trans (mul_le_mul_of_nonneg_left (b3.trans_eq (by ring)) hC)
    have hb : Tendsto (fun h => ‖F.incl h ((F.incl h).adjoint y') - y'‖ +
        S.boundConst * (‖p' h - F.L h (p h)‖ + S.boundConst * ‖F.incl h (p h) - y‖ +
          S.graphDefect h * (8 * S.boundConst * ‖y - y'‖))) F.l (𝓝 0) := by
      have := hii.add (((hdd.add (hda.const_mul S.boundConst)).add
        (hJ.mul_const (8 * S.boundConst * ‖y - y'‖))).const_mul S.boundConst)
      simpa using this
    refine squeeze_zero (fun _ => norm_nonneg _) (fun h => ?_) hb
    rw [waveExt_waveGroup H hLx, ← galerkin_p'_eq F D hDD hL Z0 hZ hgal hx h ht]
    refine (key h).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl ?_) hC))
    rw [show p h = S.load h (y - y') from galerkin_p_eq F D hDD hL Z0 hgal hx h ht]
    exact S.norm_one_sub_J_load_le h _

include hJ hL hgal hZ hcl in
/-- **An approximating family from a Galerkin core** of an approximating FEEC discretization. -/
def ApproxComplexCrime.ofGalerkinCore : ApproxComplexCrime.{u} H κ where
  toFamily := ApproxComplexCrime.Family.ofApproxFEEC F D hDD
  K := F.K
  isClosed_K := F.isClosed_K
  l := F.l
  A := orbitStates H Z0.Data
  A_sub := orbitStates_sub hZ
  Z := Z0.Data
  Z_le := hZ
  orbit_mem x hx t ht := ⟨⟨x, hx, t, ht, Or.inl rfl⟩, ⟨x, hx, t, ht, Or.inr rfl⟩⟩
  tendsto_graphDefect := hJ
  consistent y hy ε hε := by
    set S := ApproxComplexCrime.Family.ofApproxFEEC F D hDD
    filter_upwards [(tendsto_order.1 (tendsto_reading_galerkin F D hDD hJ hL Z0 hZ hgal hcl
      hy)).2 ε hε] with h hh
    refine ⟨S.load h (y - waveExt H y), hh.le, fun v => ?_⟩
    rw [S.inner_load_sub, sub_self, norm_zero]
    positivity

include hL in
theorem ofComplexCrime_ofGalerkinCore_sol (h : κ) (v : F.X h) (t : ℝ) :
    (ApproxFEEC.ofComplexCrime (ApproxComplexCrime.ofGalerkinCore F D hDD hJ hL Z0 hZ hgal
      hcl)).sol h v t = F.sol h v t := by
  change F.incl h ((C0Group.ofBounded (diffWave (D h))).S t v) =
    F.incl h ((C0Group.ofBounded (F.L h)).S t v)
  rw [hL]

include hJ hL hgal hZ hcl in
/-- **The rate class of a Galerkin family** from approximation estimates of its comparison. -/
def galerkinRateClass (T : ℝ) (Dc : Set (PiLp 2 W)) (hDc : Dc ⊆ (Z0.Data : Set (PiLp 2 W)))
    (cn : PiLp 2 W → ℝ) (m : κ → ℝ) (α Ca : ℝ)
    (happ : ∀ x ∈ Dc, ∀ h, ∀ t ∈ Icc 0 T,
      ‖H.waveGroup.S t x - F.incl h ((Z0.cmp (T + 1)).p x h t)‖ ≤ Ca * m h ^ α * cn x ∧
      ‖H.waveGroup.S t (waveExt H x) - F.incl h ((Z0.cmp (T + 1)).p' x h t)‖ ≤
        Ca * m h ^ α * cn x)
    (hdef : ∀ x ∈ Dc, ∀ h, ∀ t ∈ Icc 0 T,
      ‖(1 - (ApproxComplexCrime.Family.ofApproxFEEC F D hDD).J h) ((Z0.cmp (T + 1)).p x h t)‖ ≤
        Ca * m h ^ α * cn x ∧
      ‖(1 - (ApproxComplexCrime.Family.ofApproxFEEC F D hDD).J h) ((Z0.cmp (T + 1)).p' x h t)‖ ≤
        Ca * m h ^ α * cn x) :
    (ApproxFEEC.ofComplexCrime
      (ApproxComplexCrime.ofGalerkinCore F D hDD hJ hL Z0 hZ hgal hcl)).RateClass T :=
  (ApproxComplexCrime.ofGalerkinCore F D hDD hJ hL Z0 hZ hgal hcl).rateClass T Dc hDc cn m α Ca
    fun x hx h t ht y hy => by
      set S := ApproxComplexCrime.Family.ofApproxFEEC F D hDD
      have hx2 := hZ (hDc hx)
      have hT1 : t ∈ Ico 0 (T + 1) := ⟨ht.1, by linarith [ht.2]⟩
      obtain ⟨ha, ha'⟩ := happ x hx h t ht
      obtain ⟨hd, hd'⟩ := hdef x hx h t ht
      have hε : 0 ≤ Ca * m h ^ α * cn x := (norm_nonneg _).trans ha
      refine ⟨S.load h (y - waveExt H y), ?_, ?_, fun v => ?_⟩
      · rcases hy with rfl | hy
        · rw [waveExt_waveGroup H (domainSq_le_domain hx2),
            ← galerkin_p_eq F D hDD hL Z0 hgal (hDc hx) h hT1]
          exact ha
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          rw [waveExt_waveGroup H (waveExt_mem_domain H hx2),
            ← galerkin_p'_eq F D hDD hL Z0 hZ hgal (hDc hx) h hT1]
          exact ha'
      · rcases hy with rfl | hy
        · rw [waveExt_waveGroup H (domainSq_le_domain hx2),
            ← galerkin_p_eq F D hDD hL Z0 hgal (hDc hx) h hT1]
          exact hd
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          rw [waveExt_waveGroup H (waveExt_mem_domain H hx2),
            ← galerkin_p'_eq F D hDD hL Z0 hZ hgal (hDc hx) h hT1]
          exact hd'
      · refine (le_of_eq ?_).trans (mul_nonneg hε (add_nonneg (norm_nonneg _) (norm_nonneg _)))
        exact (congrArg norm (sub_eq_zero.2 (S.inner_load_sub h (y - waveExt H y) v))).trans
          norm_zero

theorem galerkinRateClass_p (T : ℝ) (Dc : Set (PiLp 2 W)) (hDc) (cn) (m) (α Ca) (happ) (hdef)
    {x : PiLp 2 W} (hx : x ∈ Dc) (h : κ) {t : ℝ} (ht : t ∈ Ico 0 (T + 1)) :
    (galerkinRateClass F D hDD hJ hL Z0 hZ hgal hcl T Dc hDc cn m α Ca happ hdef).p x h t =
      (Z0.cmp (T + 1)).p x h t :=
  (ApproxFEEC.loadRitz_cmp_p _ T (domainSq_le_domain (hZ (hDc hx))) h ht.1).trans
    (galerkin_p_eq F D hDD hL Z0 hgal (hDc hx) h ht).symm

include hF hL hgal hZ hcl in
/-- The rate class of a Galerkin family with orthogonal reading maps. -/
def galerkinRateClass_of_isOrthogonal (T : ℝ) (Dc : Set (PiLp 2 W))
    (hDc : Dc ⊆ (Z0.Data : Set (PiLp 2 W))) (cn : PiLp 2 W → ℝ) (m : κ → ℝ) (α Ca : ℝ)
    (happ : ∀ x ∈ Dc, ∀ h, ∀ t ∈ Icc 0 T,
      ‖H.waveGroup.S t x - F.incl h ((Z0.cmp (T + 1)).p x h t)‖ ≤ Ca * m h ^ α * cn x ∧
      ‖H.waveGroup.S t (waveExt H x) - F.incl h ((Z0.cmp (T + 1)).p' x h t)‖ ≤
        Ca * m h ^ α * cn x) :
    (ApproxFEEC.ofComplexCrime (ApproxComplexCrime.ofGalerkinCore F D hDD
      (ApproxComplexCrime.Family.tendsto_graphDefect_ofApproxFEEC F D hDD hF) hL Z0 hZ hgal
        hcl)).RateClass T :=
  galerkinRateClass F D hDD (ApproxComplexCrime.Family.tendsto_graphDefect_ofApproxFEEC F D hDD hF)
    hL Z0 hZ hgal hcl T Dc hDc cn m α Ca happ fun x hx h t ht => by
    have hε : 0 ≤ Ca * m h ^ α * cn x := (norm_nonneg _).trans (happ x hx h t ht).1
    have h0 : ‖1 - (ApproxComplexCrime.Family.ofApproxFEEC F D hDD).J h‖ = 0 := by
      rw [ApproxComplexCrime.Family.ofApproxFEEC_J F D hDD hF h, sub_self, norm_zero]
    exact ⟨(ContinuousLinearMap.le_opNorm _ _).trans (by rw [h0, zero_mul]; exact hε),
      (ContinuousLinearMap.le_opNorm _ _).trans (by rw [h0, zero_mul]; exact hε)⟩

theorem galerkinRateClass_of_isOrthogonal_p (T : ℝ) (Dc : Set (PiLp 2 W)) (hDc) (cn) (m) (α Ca)
    (happ) {x : PiLp 2 W} (hx : x ∈ Dc) (h : κ) {t : ℝ} (ht : t ∈ Ico 0 (T + 1)) :
    (galerkinRateClass_of_isOrthogonal F hF D hDD hL Z0 hZ hgal hcl T Dc hDc cn m α Ca happ).p x h
        t = (Z0.cmp (T + 1)).p x h t :=
  galerkinRateClass_p F D hDD _ hL Z0 hZ hgal hcl T Dc hDc cn m α Ca happ _ hx h ht

end Bridge

end Galerkin

/-! ### Complexification of a differential -/

section Complexify

variable {W' : ι → Type*} [∀ i, NormedAddCommGroup (W' i)] [∀ i, InnerProductSpace ℝ (W' i)]
  [∀ i, CompleteSpace (W' i)] {H' : HilbertComplex ℝ c W'} {κ' : Type*}

-- over `ℝ`, the normed space structure of the inner product (as in `ApproxFEEC.complexify`)
attribute [local instance high] ApproxFEEC.instNormedSpaceRealOfInner

namespace ApproxFEEC

variable (F : ApproxFEEC.{u} H' κ') (J : PiLp 2 W' →L[ℝ] PiLp 2 W')
  (hJJ : ∀ x, J (J x) = -x) (hJ : ∀ x, ‖J x‖ = ‖x‖)
  (hπJ : ∀ h b, F.proj h (J (F.incl h b)) = 0)
  (hJι : ∀ h a b, ⟪F.incl h a, J (F.incl h b)⟫_ℝ = 0)

/-- **The differential of the complexification**: `𝐝ₕ ⊕ 𝐝ₕ` on real and imaginary parts. -/
def complexifyD (D : ∀ h, F.X h →L[ℝ] F.X h) (h : κ') :
    (F.complexify J hJJ hJ hπJ hJι).X h →L[ℝ] (F.complexify J hJJ hJ hπJ hJι).X h :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (F.X h) (F.X h)).symm.toContinuousLinearMap ∘L
    ((D h ∘L WithLp.fstL 2 ℝ (F.X h) (F.X h)).prod (D h ∘L WithLp.sndL 2 ℝ (F.X h) (F.X h)))

@[simp] theorem complexifyD_apply (D : ∀ h, F.X h →L[ℝ] F.X h) (h : κ') (a b : F.X h) :
    F.complexifyD J hJJ hJ hπJ hJι D h (WithLp.toLp 2 (a, b)) = WithLp.toLp 2 (D h a, D h b) :=
  rfl

theorem complexifyD_D (D : ∀ h, F.X h →L[ℝ] F.X h) (hDD : ∀ h v, D h (D h v) = 0) (h : κ')
    (v : (F.complexify J hJJ hJ hπJ hJι).X h) :
    F.complexifyD J hJJ hJ hπJ hJι D h (F.complexifyD J hJJ hJ hπJ hJι D h v) = 0 := by
  obtain ⟨⟨a, b⟩⟩ := v
  rw [complexifyD_apply, complexifyD_apply, hDD, hDD]; rfl

theorem complexify_L_eq_diffWave (D : ∀ h, F.X h →L[ℝ] F.X h)
    (hL : ∀ h, F.L h = diffWave (D h)) (h : κ') :
    (F.complexify J hJJ hJ hπJ hJι).L h = diffWave (F.complexifyD J hJJ hJ hπJ hJι D h) := by
  refine ContinuousLinearMap.ext fun v => ext_inner_right ℝ fun w => ?_
  obtain ⟨⟨a, b⟩⟩ := v
  obtain ⟨⟨a', b'⟩⟩ := w
  refine Eq.trans ?_ (inner_diffWave (F.complexifyD J hJJ hJ hπJ hJι D h) _ _).symm
  change ⟪WithLp.toLp 2 (F.L h a, F.L h b), WithLp.toLp 2 (a', b')⟫_ℝ =
    ⟪WithLp.toLp 2 (D h a, D h b), WithLp.toLp 2 (a', b')⟫_ℝ -
      ⟪WithLp.toLp 2 (a, b), WithLp.toLp 2 (D h a', D h b')⟫_ℝ
  simp only [WithLp.prod_inner_apply, hL, inner_diffWave]
  ring

theorem complexify_finiteDimensional [hfd : ∀ h, FiniteDimensional ℝ (F.X h)] (h : κ') :
    FiniteDimensional ℝ ((F.complexify J hJJ hJ hπJ hJι).X h) :=
  inferInstanceAs (FiniteDimensional ℝ (WithLp 2 (F.X h × F.X h)))

/-- A pair `(a, b)` of real states as a state of the complexification. -/
def complexifyPair (h : κ') (a b : F.X h) : (F.complexify J hJJ hJ hπJ hJι).X h :=
  WithLp.toLp 2 (a, b)

theorem complexify_galerkin (hF : F.IsOrthogonal) (h : κ') (a b : F.X h) (z : PiLp 2 W')
    (h1 : a - F.L h a = F.proj h z) (h2 : b - F.L h b = -F.proj h (J z)) :
    F.complexifyPair J hJJ hJ hπJ hJι h a b -
        (F.complexify J hJJ hJ hπJ hJι).L h (F.complexifyPair J hJJ hJ hπJ hJι h a b) =
      ((F.complexify J hJJ hJ hπJ hJι).incl h).adjoint z := by
  rw [(hF.complexify J hJJ hJ hπJ hJι).adjoint_incl]
  change WithLp.toLp 2 (a - F.L h a, b - F.L h b) = WithLp.toLp 2 (F.proj h z, -F.proj h (J z))
  rw [h1, h2]

end ApproxFEEC

end Complexify


/-! ### Rates at order `min(α, β, γ)` from the split estimates -/

section RateSplit

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

namespace ApproxComplexCrime

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxComplexCrime.{u} H κ)

/-- The constant `(1 + C_ι) Cₐ + C_β + C_γ` of `rateClass_of_split`. -/
def splitConst (Ca Cb Cg : ℝ) : ℝ := (1 + F.toFamily.boundConst) * Ca + Cb + Cg

open ApproxFEEC in
/-- **A rate class at order `min(α, β, γ)`** from graph-norm, inner-product and cochain rates. -/
def rateClass_of_split (T : ℝ) (Dc : Set (PiLp 2 W)) (hDc : Dc ⊆ (F.Z : Set (PiLp 2 W)))
    (cn : PiLp 2 W → ℝ) (m : κ → ℝ) (α β γ Ca Cb Cg : ℝ)
    (hm0 : ∀ h, 0 ≤ m h) (hm1 : ∀ h, m h ≤ 1) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCg : 0 ≤ Cg) (hcn : ∀ x ∈ Dc, 0 ≤ cn x)
    (hsplit : ∀ x ∈ Dc, ∀ h, ∀ t ∈ Icc 0 T, ∀ y ∈ ({H.waveGroup.S t x,
      H.waveGroup.S t (waveExt H x)} : Set (PiLp 2 W)), ∀ hy : y ∈ H.wave.domain,
      ∃ w : F.toFamily.X h,
        ‖y - F.toFamily.incl h w‖ + ‖H.totalD ⟨y, hy.1⟩ - F.toFamily.incl h (F.toFamily.D h w)‖ ≤
          Ca * m h ^ α * cn x ∧
        ‖(1 - F.toFamily.J h) w‖ + ‖(1 - F.toFamily.J h) (F.toFamily.D h w)‖ ≤
          Cb * m h ^ β * cn x ∧
        ∀ v, ‖⟪F.toFamily.cochainDefect h ⟨y, hy⟩, v⟫_𝕜‖ ≤
          Cg * m h ^ γ * cn x * (‖v‖ + ‖F.toFamily.D h v‖)) :
    (ofComplexCrime F).RateClass T :=
  F.rateClass T Dc hDc cn m (min α (min β γ)) (F.splitConst Ca Cb Cg)
    fun x hx h t ht y hy => by
      set S := F.toFamily
      have hx2 := F.Z_le (hDc hx)
      have hx1 := domainSq_le_domain hx2
      have hyD : y ∈ H.wave.domain := by
        rcases hy with rfl | hy
        · exact waveGroup_mem_domain H hx1 t
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          exact waveGroup_mem_domain H (waveExt_mem_domain H hx2) t
      obtain ⟨w, ha, hb, hcd⟩ := hsplit x hx h t ht y hy hyD
      obtain ⟨h1, h2, h3⟩ := S.rateData_of_split h ⟨y, hyD⟩ w ha hb hcd
      have hC := S.boundConst_nonneg
      have hc := hcn x hx
      have hmh0 := hm0 h
      have hmh1 := hm1 h
      have pa : m h ^ α ≤ m h ^ min α (min β γ) :=
        Real.rpow_le_rpow_of_exponent_ge' hmh0 hmh1 (le_min hα (le_min hβ hγ)) (min_le_left _ _)
      have pb : m h ^ β ≤ m h ^ min α (min β γ) :=
        Real.rpow_le_rpow_of_exponent_ge' hmh0 hmh1 (le_min hα (le_min hβ hγ))
          ((min_le_right _ _).trans (min_le_left _ _))
      have hpa := Real.rpow_nonneg hmh0 α
      have hpb := Real.rpow_nonneg hmh0 β
      have hpμ := Real.rpow_nonneg hmh0 (min α (min β γ))
      -- the combined bound `E_β + C_ι Eₐ + E_γ ≤ Cₐ' m^μ ‖x‖_c`
      have hsum := add_rpow_le_rpow_min hmh0 hmh1 hα hβ hγ
        (mul_nonneg (mul_nonneg hC hCa) hc) (mul_nonneg hCb hc) (mul_nonneg hCg hc)
      have hres : Cb * m h ^ β * cn x + S.boundConst * (Ca * m h ^ α * cn x) +
          Cg * m h ^ γ * cn x ≤ F.splitConst Ca Cb Cg * m h ^ min α (min β γ) * cn x := by
        have e : F.splitConst Ca Cb Cg * m h ^ min α (min β γ) * cn x =
            (S.boundConst * Ca * cn x + Cb * cn x + Cg * cn x) * m h ^ min α (min β γ) +
              Ca * cn x * m h ^ min α (min β γ) := by
          unfold splitConst; ring
        rw [e]
        have : 0 ≤ Ca * cn x * m h ^ min α (min β γ) := by positivity
        have e2 : Cb * m h ^ β * cn x + S.boundConst * (Ca * m h ^ α * cn x) +
            Cg * m h ^ γ * cn x =
            S.boundConst * Ca * cn x * m h ^ α + Cb * cn x * m h ^ β + Cg * cn x * m h ^ γ := by
          ring
        linarith
      refine ⟨w, ?_, ?_, fun v => ?_⟩
      · refine h1.trans ?_
        have e : F.splitConst Ca Cb Cg * m h ^ min α (min β γ) * cn x =
            Ca * cn x * m h ^ min α (min β γ) +
              (S.boundConst * Ca + Cb + Cg) * cn x * m h ^ min α (min β γ) := by
          unfold splitConst; ring
        rw [e]
        have := mul_le_mul_of_nonneg_left pa (mul_nonneg hCa hc)
        have : 0 ≤ (S.boundConst * Ca + Cb + Cg) * cn x * m h ^ min α (min β γ) := by
          positivity
        linarith [show Ca * m h ^ α * cn x = Ca * cn x * m h ^ α by ring]
      · refine h2.trans ?_
        have e : F.splitConst Ca Cb Cg * m h ^ min α (min β γ) * cn x =
            Cb * cn x * m h ^ min α (min β γ) +
              ((1 + S.boundConst) * Ca + Cg) * cn x * m h ^ min α (min β γ) := by
          unfold splitConst; ring
        rw [e]
        have := mul_le_mul_of_nonneg_left pb (mul_nonneg hCb hc)
        have : 0 ≤ ((1 + S.boundConst) * Ca + Cg) * cn x * m h ^ min α (min β γ) := by
          positivity
        linarith [show Cb * m h ^ β * cn x = Cb * cn x * m h ^ β by ring]
      · rw [waveExt_of_mem hyD]
        exact (h3 v).trans (mul_le_mul_of_nonneg_right hres
          (add_nonneg (norm_nonneg _) (norm_nonneg _)))

variable (T : ℝ) (Dc : Set (PiLp 2 W)) (hDc : Dc ⊆ (F.Z : Set (PiLp 2 W)))
  (cn : PiLp 2 W → ℝ) (m : κ → ℝ) (α β γ Ca Cb Cg : ℝ)
  (hm0 : ∀ h, 0 ≤ m h) (hm1 : ∀ h, m h ≤ 1) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
  (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCg : 0 ≤ Cg) (hcn : ∀ x ∈ Dc, 0 ≤ cn x) (hsplit)

theorem rateClass_of_split_α :
    (F.rateClass_of_split T Dc hDc cn m α β γ Ca Cb Cg hm0 hm1 hα hβ hγ hCa hCb hCg hcn
      hsplit).α = min α (min β γ) := rfl

theorem rateClass_of_split_C :
    (F.rateClass_of_split T Dc hDc cn m α β γ Ca Cb Cg hm0 hm1 hα hβ hγ hCa hCb hCg hcn
      hsplit).C = (1 + 8 * F.toFamily.boundConst) *
        ((1 + F.toFamily.boundConst) * Ca + Cb + Cg) := rfl

theorem rateClass_of_split_C' :
    (F.rateClass_of_split T Dc hDc cn m α β γ Ca Cb Cg hm0 hm1 hα hβ hγ hCa hCb hCg hcn
      hsplit).C' = 2 * (1 + 8 * (1 + F.toFamily.boundConst ^ 2) +
        F.toFamily.boundConst * (1 + 8 * F.toFamily.boundConst)) *
        ((1 + F.toFamily.boundConst) * Ca + Cb + Cg) := rfl

/-- **The error at order `min(α, β, γ)`**:
`‖e^{tL} x - iₕ e^{tLₕ} Rₕ x‖ ≤ (C + C_ι C' t) m(h)^{min(α, β, γ)} ‖x‖_c` on `[0, T]`. -/
theorem error_le_of_split {x : PiLp 2 W} (hx : x ∈ Dc) (h : κ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖H.waveGroup.S t x - (ApproxFEEC.ofComplexCrime F).sol h
        ((F.rateClass_of_split T Dc hDc cn m α β γ Ca Cb Cg hm0 hm1 hα hβ hγ hCa hCb hCg
          hcn hsplit).p x h 0) t‖ ≤
      ((F.rateClass_of_split T Dc hDc cn m α β γ Ca Cb Cg hm0 hm1 hα hβ hγ hCa hCb hCg
          hcn hsplit).C + F.toFamily.boundConst *
        (F.rateClass_of_split T Dc hDc cn m α β γ Ca Cb Cg hm0 hm1 hα hβ hγ hCa hCb hCg
          hcn hsplit).C' * t) * (m h ^ min α (min β γ) * cn x) :=
  F.error_le_of_rateClass _ hx h ht

end ApproxComplexCrime

end RateSplit

end Feec.HilbertComplex
