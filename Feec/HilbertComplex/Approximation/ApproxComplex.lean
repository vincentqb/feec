module

public import Feec.HilbertComplex.Approximation.ApproxConforming

/-!
# Approximating families of discrete Hilbert complexes

Discretizations of a Hilbert complex in the setting of [HolstStern2012], §3: finite-dimensional
complexes with their own inner products and cochain maps into it, with the inner-product defect in
the graph norm tending to zero and the graph-norm approximation property. Each is an approximating
FEEC discretization of the Hodge wave equation.

## Main results

* `ApproxComplex.Family.norm_graphFst_sub_inclL_ellProj_le`: the Strang lemma.
* `approxFEEC_ofComplex`: the approximating FEEC theorem for `ofComplex`, with discrete constraints.
* `ConstrainedFEEC.toComplex_sol`: the conforming case recovers the subcomplex scheme.

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012]
* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap Metric

@[expose] public noncomputable section

universe u

namespace Feec.HilbertComplex

open _root_.Feec.HodgeWave

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {c : ComplexShape ι}

/-! ### Finite-dimensional Hilbert complexes -/

section FiniteDim

variable {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)]
  [∀ i, CompleteSpace (V i)] [∀ i, FiniteDimensional 𝕜 (V i)] (E : HilbertComplex 𝕜 c V)

omit [Fintype ι] in
theorem d_domain_eq_top_of_finiteDimensional (i j : ι) : (E.d i j).domain = ⊤ := by
  have hc : IsClosed ((E.d i j).domain : Set (V i)) := Submodule.closed_of_finiteDimensional _
  rw [← SetLike.coe_set_eq, Submodule.top_coe, ← hc.closure_eq, (E.dense i j).closure_eq]

theorem mem_totalD_domain_of_finiteDimensional (v : PiLp 2 V) : v ∈ E.totalD.domain :=
  fun i j => by rw [E.d_domain_eq_top_of_finiteDimensional i j]; trivial

theorem mem_wave_domain_of_finiteDimensional (v : PiLp 2 V) : v ∈ E.wave.domain :=
  ⟨E.mem_totalD_domain_of_finiteDimensional v, E.dual.mem_totalD_domain_of_finiteDimensional v⟩

/-- The total differential `𝐝` of a finite-dimensional complex, as a bounded operator. -/
def totalDL : PiLp 2 V →L[𝕜] PiLp 2 V :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => E.totalD ⟨v, E.mem_totalD_domain_of_finiteDimensional v⟩
      map_add' := fun v w => by
        change E.totalD (⟨v, E.mem_totalD_domain_of_finiteDimensional v⟩ +
          ⟨w, E.mem_totalD_domain_of_finiteDimensional w⟩) = _
        rw [LinearPMap.map_add]
      map_smul' := fun a v => by
        change E.totalD (a • ⟨v, E.mem_totalD_domain_of_finiteDimensional v⟩) = _
        rw [LinearPMap.map_smul]; rfl }

theorem totalDL_apply (v : PiLp 2 V) (hv : v ∈ E.totalD.domain) :
    E.totalDL v = E.totalD ⟨v, hv⟩ := rfl

theorem totalDL_totalDL (v : PiLp 2 V) : E.totalDL (E.totalDL v) = 0 :=
  E.totalD_comp_totalD ⟨v, E.mem_totalD_domain_of_finiteDimensional v⟩

/-- The Hodge wave operator `L = 𝐝 - 𝐝*` of a finite-dimensional complex, as a bounded operator. -/
def waveL : PiLp 2 V →L[𝕜] PiLp 2 V := E.totalDL - E.totalDL.adjoint

theorem waveL_apply' (v : PiLp 2 V) : E.waveL v = E.totalDL v - E.totalDL.adjoint v := rfl

theorem inner_waveL (v w : PiLp 2 V) :
    ⟪E.waveL v, w⟫_𝕜 = ⟪E.totalDL v, w⟫_𝕜 - ⟪v, E.totalDL w⟫_𝕜 := by
  rw [waveL_apply', inner_sub_left, ContinuousLinearMap.adjoint_inner_left]

theorem waveL_skew (v w : PiLp 2 V) : ⟪E.waveL v, w⟫_𝕜 = -⟪v, E.waveL w⟫_𝕜 := by
  rw [inner_waveL, waveL_apply', inner_sub_right, ContinuousLinearMap.adjoint_inner_right]
  ring

theorem waveL_apply (v : PiLp 2 V) :
    E.waveL v = E.wave ⟨v, E.mem_wave_domain_of_finiteDimensional v⟩ := by
  refine ext_inner_right 𝕜 fun w => ?_
  rw [inner_waveL, inner_wave_left E ⟨v, E.mem_wave_domain_of_finiteDimensional v⟩
    ⟨w, E.mem_totalD_domain_of_finiteDimensional w⟩]
  rfl

theorem re_inner_sub_waveL_self (v : PiLp 2 V) :
    RCLike.re ⟪v - E.waveL v, v⟫_𝕜 = ‖v‖ ^ 2 := by
  have hs : RCLike.re ⟪E.waveL v, v⟫_𝕜 = 0 := by
    have h := E.waveL_skew v v
    have : RCLike.re ⟪E.waveL v, v⟫_𝕜 = - RCLike.re ⟪E.waveL v, v⟫_𝕜 := by
      conv_rhs => rw [h, _root_.map_neg, ← inner_conj_symm, RCLike.conj_re]
      simp
    linarith
  rw [inner_sub_left, _root_.map_sub, hs, sub_zero, inner_self_eq_norm_sq]

theorem injective_one_sub_waveL :
    Function.Injective ((1 - E.waveL : PiLp 2 V →L[𝕜] PiLp 2 V) : PiLp 2 V →ₗ[𝕜] PiLp 2 V) := by
  intro a b hab
  have h0 : (a - b) - E.waveL (a - b) = 0 := by
    have : ((1 - E.waveL : PiLp 2 V →L[𝕜] PiLp 2 V)) (a - b) = 0 := by
      rw [_root_.map_sub]; exact sub_eq_zero.2 hab
    simpa using this
  have h1 := E.re_inner_sub_waveL_self (a - b)
  rw [h0, inner_zero_left, _root_.map_zero] at h1
  have : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- `1 - L` as a continuous linear equivalence. -/
def oneSubWaveL : PiLp 2 V ≃L[𝕜] PiLp 2 V :=
  (LinearEquiv.ofInjectiveEndo _ E.injective_one_sub_waveL).toContinuousLinearEquiv

theorem oneSubWaveL_apply (v : PiLp 2 V) : E.oneSubWaveL v = v - E.waveL v := rfl

theorem norm_add_norm_le_of_inner (r : PiLp 2 V) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ v, ‖⟪r - E.waveL r, v⟫_𝕜‖ ≤ M * (‖v‖ + ‖E.totalDL v‖)) :
    ‖r‖ + ‖E.totalDL r‖ ≤ 8 * M := by
  set D := E.totalDL
  have hDv : D (r - D r) = D r := by rw [_root_.map_sub, E.totalDL_totalDL, sub_zero]
  have hv := h (r - D r)
  rw [hDv] at hv
  have e1 : r - E.waveL r = (r - D r) + D.adjoint r := by rw [waveL_apply']; abel
  have e2 : ⟪D.adjoint r, r - D r⟫_𝕜 = ⟪r, D r⟫_𝕜 := by
    rw [ContinuousLinearMap.adjoint_inner_left, hDv]
  have hre : RCLike.re ⟪r - E.waveL r, r - D r⟫_𝕜 =
      ‖r‖ ^ 2 + ‖D r‖ ^ 2 - RCLike.re ⟪r, D r⟫_𝕜 := by
    rw [e1, inner_add_left, _root_.map_add, e2, inner_self_eq_norm_sq, @norm_sub_sq 𝕜]
    ring
  have hle : RCLike.re ⟪r - E.waveL r, r - D r⟫_𝕜 ≤ ‖⟪r - E.waveL r, r - D r⟫_𝕜‖ :=
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

end FiniteDim

section Group

variable {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)]
  [∀ i, CompleteSpace (V i)] [∀ i, FiniteDimensional 𝕜 (V i)] [∀ i, NormedSpace ℝ (V i)]
  [∀ i, IsScalarTower ℝ 𝕜 (V i)] (E : HilbertComplex 𝕜 c V)

theorem ofBounded_waveL_S (t : ℝ) (v : PiLp 2 V) :
    (C0Group.ofBounded E.waveL).S t v = E.waveGroup.S t v := by
  have hv := E.mem_wave_domain_of_finiteDimensional v
  have hu : ∀ s, HasDerivAt (fun s => E.waveGroup.S s v) (E.waveL (E.waveGroup.S s v)) s :=
    fun s => by
      have h := hasDerivAt_waveGroup E hv s
      rwa [← wave_waveGroup hv s, ← E.waveL_apply] at h
  have h := eq_ofBounded_of_hasDerivAt E.waveL E.waveL_skew hu t
  rw [C0Group.S_zero_apply] at h
  exact h.symm

end Group

/-! ### Approximating families of discrete complexes -/

section Family

variable {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)]
  [∀ i, CompleteSpace (W i)]

/-- A **family of discrete Hilbert complexes with reading maps** `iₕ : Vₕ → W`. -/
structure ApproxComplex.Family (H : HilbertComplex 𝕜 c W) (κ : Type*) where
  /-- the discrete spaces -/
  V : κ → ι → Type u
  [normedAddCommGroup : ∀ h i, NormedAddCommGroup (V h i)]
  [innerProductSpace : ∀ h i, InnerProductSpace 𝕜 (V h i)]
  [completeSpace : ∀ h i, CompleteSpace (V h i)]
  [finiteDimensional : ∀ h i, FiniteDimensional 𝕜 (V h i)]
  [normedSpaceReal : ∀ h i, NormedSpace ℝ (V h i)]
  [isScalarTower : ∀ h i, IsScalarTower ℝ 𝕜 (V h i)]
  /-- the discrete complexes -/
  cpx : ∀ h, HilbertComplex 𝕜 c (V h)
  /-- the cochain maps `iₕ` -/
  incl : ∀ h i, V h i →L[𝕜] W i
  incl_mem : ∀ h i j (v : V h i), incl h i v ∈ (H.d i j).domain
  incl_d : ∀ h i j (v : ((cpx h).d i j).domain),
    H.d i j ⟨incl h i v, incl_mem h i j v⟩ = incl h j ((cpx h).d i j v)
  /-- the left inverses `πₕ` -/
  proj : ∀ h i, W i →L[𝕜] V h i
  proj_incl : ∀ h i v, proj h i (incl h i v) = v
  bound : ∃ C, ∀ h i, ‖incl h i‖ ≤ C ∧ ‖proj h i‖ ≤ C

attribute [instance] ApproxComplex.Family.normedAddCommGroup
  ApproxComplex.Family.innerProductSpace ApproxComplex.Family.completeSpace
  ApproxComplex.Family.finiteDimensional ApproxComplex.Family.normedSpaceReal
  ApproxComplex.Family.isScalarTower

theorem norm_piLp_le_of_le {A B : ι → Type*} [∀ i, SeminormedAddCommGroup (A i)]
    [∀ i, SeminormedAddCommGroup (B i)] {x : PiLp 2 A} {y : PiLp 2 B} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖y i‖ ≤ C * ‖x i‖) : ‖y‖ ≤ C * ‖x‖ := by
  have hsq : ‖y‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
    rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (h i) 2
  have := norm_nonneg y
  nlinarith [mul_nonneg hC (norm_nonneg x)]

namespace ApproxComplex.Family

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (S : ApproxComplex.Family.{u} H κ)

/-- A nonnegative uniform bound of `‖iₕ‖`, `‖πₕ‖`. -/
def boundConst : ℝ := max S.bound.choose 0

omit [Fintype ι] in
theorem boundConst_nonneg : 0 ≤ S.boundConst := le_max_right _ _

omit [Fintype ι] in
theorem norm_incl_le (h : κ) (i : ι) : ‖S.incl h i‖ ≤ S.boundConst :=
  (S.bound.choose_spec h i).1.trans (le_max_left _ _)

omit [Fintype ι] in
theorem norm_proj_le (h : κ) (i : ι) : ‖S.proj h i‖ ≤ S.boundConst :=
  (S.bound.choose_spec h i).2.trans (le_max_left _ _)

/-- The total reading map `iₕ : Vₕ → W`, `(iₕ v)ⁱ = iₕⁱ vⁱ`. -/
def inclL (h : κ) : PiLp 2 (S.V h) →L[𝕜] PiLp 2 W :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 fun i => S.incl h i (v i)
      map_add' := fun v w => PiLp.ext fun i => by simp
      map_smul' := fun a v => PiLp.ext fun i => by simp }

@[simp] theorem inclL_apply (h : κ) (v : PiLp 2 (S.V h)) (i : ι) :
    S.inclL h v i = S.incl h i (v i) := rfl

/-- The total left inverse `πₕ : W → Vₕ`. -/
def projL (h : κ) : PiLp 2 W →L[𝕜] PiLp 2 (S.V h) :=
  LinearMap.mkContinuous
    { toFun := fun x => WithLp.toLp 2 fun i => S.proj h i (x i)
      map_add' := fun v w => PiLp.ext fun i => by simp
      map_smul' := fun a v => PiLp.ext fun i => by simp }
    S.boundConst fun x => norm_piLp_le_of_le S.boundConst_nonneg fun i =>
      ((S.proj h i).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (S.norm_proj_le h i) (norm_nonneg _))

@[simp] theorem projL_inclL (h : κ) (v : PiLp 2 (S.V h)) : S.projL h (S.inclL h v) = v :=
  PiLp.ext fun i => S.proj_incl h i (v i)

theorem norm_inclL_apply_le (h : κ) (v : PiLp 2 (S.V h)) :
    ‖S.inclL h v‖ ≤ S.boundConst * ‖v‖ :=
  norm_piLp_le_of_le S.boundConst_nonneg fun i => ((S.incl h i).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (S.norm_incl_le h i) (norm_nonneg _))

theorem norm_inclL_le (h : κ) : ‖S.inclL h‖ ≤ S.boundConst :=
  ContinuousLinearMap.opNorm_le_bound _ S.boundConst_nonneg (S.norm_inclL_apply_le h)

theorem norm_projL_le (h : κ) : ‖S.projL h‖ ≤ S.boundConst :=
  LinearMap.mkContinuous_norm_le _ S.boundConst_nonneg _

theorem norm_le_norm_inclL (h : κ) (v : PiLp 2 (S.V h)) :
    ‖v‖ ≤ S.boundConst * ‖S.inclL h v‖ :=
  calc ‖v‖ = ‖S.projL h (S.inclL h v)‖ := by rw [S.projL_inclL]
    _ ≤ ‖S.projL h‖ * ‖S.inclL h v‖ := (S.projL h).le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_right (S.norm_projL_le h) (norm_nonneg _)

theorem inclL_injective (h : κ) : Function.Injective (S.inclL h) := fun a b hab => by
  have := congrArg (S.projL h) hab
  rwa [S.projL_inclL, S.projL_inclL] at this

theorem inclL_mem (h : κ) (v : PiLp 2 (S.V h)) : S.inclL h v ∈ H.totalD.domain :=
  fun i j => S.incl_mem h i j (v i)

/-- The discrete total differential `𝐝ₕ` on `Vₕ`. -/
abbrev D (h : κ) : PiLp 2 (S.V h) →L[𝕜] PiLp 2 (S.V h) := (S.cpx h).totalDL

/-- The discrete Hodge wave operator `Lₕ = 𝐝ₕ - 𝐝ₕ*`. -/
abbrev L (h : κ) : PiLp 2 (S.V h) →L[𝕜] PiLp 2 (S.V h) := (S.cpx h).waveL

theorem inclL_D (h : κ) (v : PiLp 2 (S.V h)) :
    S.inclL h (S.D h v) = H.totalD ⟨S.inclL h v, S.inclL_mem h v⟩ := by
  refine PiLp.ext fun j => ?_
  rw [totalD_apply, inclL_apply, D, totalDL_apply _ v
    ((S.cpx h).mem_totalD_domain_of_finiteDimensional v), totalD_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => (S.incl_d h i j ⟨v i, _⟩).symm

/-- The lift `v ↦ (iₕ v, 𝐝 iₕ v)` of `Vₕ` into the graph space `Γ(𝐝)`. -/
def graphIncl (h : κ) : PiLp 2 (S.V h) →L[𝕜] H.totalD.GraphSpace :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => H.totalD.toGraphSpace ⟨S.inclL h v, S.inclL_mem h v⟩
      map_add' := fun v w => H.totalD.graphFst_injective (by
        rw [H.totalD.graphFst.map_add]; exact (S.inclL h).map_add v w)
      map_smul' := fun a v => H.totalD.graphFst_injective (by
        rw [RingHom.id_apply, H.totalD.graphFst.map_smul]; exact (S.inclL h).map_smul a v) }

theorem graphFst_graphIncl (h : κ) (v : PiLp 2 (S.V h)) :
    H.totalD.graphFst (S.graphIncl h v) = S.inclL h v := rfl

theorem graphSnd_graphIncl (h : κ) (v : PiLp 2 (S.V h)) :
    H.totalD.graphSnd (S.graphIncl h v) = S.inclL h (S.D h v) := by rw [S.inclL_D]; rfl

/-- The **inner-product operator** `Jₕ = iₕ* iₕ`. -/
def J (h : κ) : PiLp 2 (S.V h) →L[𝕜] PiLp 2 (S.V h) := (S.inclL h).adjoint ∘L S.inclL h

theorem inner_J (h : κ) (v w : PiLp 2 (S.V h)) :
    ⟪S.J h v, w⟫_𝕜 = ⟪S.inclL h v, S.inclL h w⟫_𝕜 := by
  rw [J, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]

/-- **The inner-product defect** `graphDefect`: the norm of `1 - Jₕ` on the graph space of `𝐝ₕ`. -/
def graphDefect (h : κ) : ℝ := (S.D h).graphOpNorm (1 - S.J h)

theorem norm_add_norm_D_le (h : κ) (v : PiLp 2 (S.V h)) :
    ‖v‖ + ‖S.D h v‖ ≤ 2 * S.boundConst * ‖S.graphIncl h v‖ := by
  have h1 := S.norm_le_norm_inclL h v
  have h2 := S.norm_le_norm_inclL h (S.D h v)
  have e1 : ‖S.inclL h v‖ ≤ ‖S.graphIncl h v‖ := by
    rw [← S.graphFst_graphIncl]; exact norm_graphFst_le _
  have e2 : ‖S.inclL h (S.D h v)‖ ≤ ‖S.graphIncl h v‖ := by
    rw [← S.graphSnd_graphIncl]; exact norm_graphSnd_le _
  have hC := S.boundConst_nonneg
  nlinarith [mul_le_mul_of_nonneg_left e1 hC, mul_le_mul_of_nonneg_left e2 hC]

/-! #### The modified elliptic projection -/

/-- The **discrete load** `Gₕ ζ = iₕ* ζ₁ - iₕ* ζ₂ + 𝐝ₕ* iₕ* ζ₁` of `ζ = (ζ₁, ζ₂) ∈ Γ(𝐝)`. -/
def G (h : κ) : H.totalD.GraphSpace →L[𝕜] PiLp 2 (S.V h) :=
  (S.inclL h).adjoint ∘L H.totalD.graphFst - (S.inclL h).adjoint ∘L H.totalD.graphSnd +
    (S.D h).adjoint ∘L (S.inclL h).adjoint ∘L H.totalD.graphFst

theorem inner_G (h : κ) (ζ : H.totalD.GraphSpace) (v : PiLp 2 (S.V h)) :
    ⟪S.G h ζ, v⟫_𝕜 = ⟪H.totalD.graphFst ζ, S.inclL h v⟫_𝕜 -
      ⟪H.totalD.graphSnd ζ, S.inclL h v⟫_𝕜 + ⟪H.totalD.graphFst ζ, S.inclL h (S.D h v)⟫_𝕜 := by
  simp only [G, _root_.add_apply, _root_.sub_apply,
    ContinuousLinearMap.comp_apply, inner_add_left, inner_sub_left,
    ContinuousLinearMap.adjoint_inner_left]

theorem G_waveLift (h : κ) (y : H.wave.domain) :
    S.G h (waveLift H y) = (S.inclL h).adjoint ((y : PiLp 2 W) - H.wave y) := by
  refine ext_inner_right 𝕜 fun v => ?_
  rw [inner_G, ContinuousLinearMap.adjoint_inner_left, inner_sub_left,
    inner_wave_left H y ⟨S.inclL h v, S.inclL_mem h v⟩, S.inclL_D h v]
  simp only [graphFst_waveLift]
  change _ = _ - (⟪H.totalD.graphSnd (waveLift H y), _⟫_𝕜 - _)
  ring

theorem inner_G_graphIncl (h : κ) (w v : PiLp 2 (S.V h)) :
    ⟪S.G h (S.graphIncl h w), v⟫_𝕜 =
      ⟪S.J h w, v⟫_𝕜 - ⟪S.J h (S.D h w), v⟫_𝕜 + ⟪S.J h w, S.D h v⟫_𝕜 := by
  rw [inner_G, S.graphFst_graphIncl, S.graphSnd_graphIncl, S.inner_J, S.inner_J, S.inner_J]

theorem norm_inner_G_le (h : κ) (ζ : H.totalD.GraphSpace) (v : PiLp 2 (S.V h)) :
    ‖⟪S.G h ζ, v⟫_𝕜‖ ≤ 2 * S.boundConst * ‖ζ‖ * (‖v‖ + ‖S.D h v‖) := by
  rw [inner_G]
  have hC := S.boundConst_nonneg
  have a1 : ‖⟪H.totalD.graphFst ζ, S.inclL h v⟫_𝕜‖ ≤ ‖ζ‖ * (S.boundConst * ‖v‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul (norm_graphFst_le _) (S.norm_inclL_apply_le h v)
      (norm_nonneg _) (norm_nonneg _))
  have a2 : ‖⟪H.totalD.graphSnd ζ, S.inclL h v⟫_𝕜‖ ≤ ‖ζ‖ * (S.boundConst * ‖v‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul (norm_graphSnd_le _) (S.norm_inclL_apply_le h v)
      (norm_nonneg _) (norm_nonneg _))
  have a3 : ‖⟪H.totalD.graphFst ζ, S.inclL h (S.D h v)⟫_𝕜‖ ≤
      ‖ζ‖ * (S.boundConst * ‖S.D h v‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul (norm_graphFst_le _)
      (S.norm_inclL_apply_le h _) (norm_nonneg _) (norm_nonneg _))
  have hz := norm_nonneg ζ
  have hv := norm_nonneg v
  calc _ ≤ ‖⟪H.totalD.graphFst ζ, S.inclL h v⟫_𝕜‖ + ‖⟪H.totalD.graphSnd ζ, S.inclL h v⟫_𝕜‖ +
        ‖⟪H.totalD.graphFst ζ, S.inclL h (S.D h v)⟫_𝕜‖ :=
        (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ ‖ζ‖ * (S.boundConst * ‖v‖) + ‖ζ‖ * (S.boundConst * ‖v‖) +
        ‖ζ‖ * (S.boundConst * ‖S.D h v‖) := by linarith
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hz hC) (norm_nonneg (S.D h v))]

/-- The **modified elliptic projection** `Rₕ = (1 - Lₕ)⁻¹ Gₕ : Γ(𝐝) → Vₕ`. -/
def ellProj (h : κ) : H.totalD.GraphSpace →L[𝕜] PiLp 2 (S.V h) :=
  ((S.cpx h).oneSubWaveL.symm : PiLp 2 (S.V h) →L[𝕜] PiLp 2 (S.V h)) ∘L S.G h

theorem ellProj_sub (h : κ) (ζ : H.totalD.GraphSpace) :
    S.ellProj h ζ - S.L h (S.ellProj h ζ) = S.G h ζ :=
  (S.cpx h).oneSubWaveL.apply_symm_apply (S.G h ζ)

theorem eq_ellProj (h : κ) {ζ : H.totalD.GraphSpace} {r : PiLp 2 (S.V h)}
    (hr : r - S.L h r = S.G h ζ) : r = S.ellProj h ζ :=
  (S.cpx h).oneSubWaveL.injective (by
    rw [oneSubWaveL_apply, oneSubWaveL_apply, hr, S.ellProj_sub])

theorem norm_ellProj_add_le (h : κ) (ζ : H.totalD.GraphSpace) :
    ‖S.ellProj h ζ‖ + ‖S.D h (S.ellProj h ζ)‖ ≤ 16 * S.boundConst * ‖ζ‖ := by
  have := (S.cpx h).norm_add_norm_le_of_inner (S.ellProj h ζ)
    (M := 2 * S.boundConst * ‖ζ‖) (by have := S.boundConst_nonneg; positivity)
    fun v => by rw [S.ellProj_sub]; exact S.norm_inner_G_le h ζ v
  linarith

theorem norm_ellProj_apply_le (h : κ) (ζ : H.totalD.GraphSpace) :
    ‖S.ellProj h ζ‖ ≤ 16 * S.boundConst * ‖ζ‖ :=
  le_trans (le_add_of_nonneg_right (norm_nonneg _)) (S.norm_ellProj_add_le h ζ)

theorem norm_ellProj_le (h : κ) : ‖S.ellProj h‖ ≤ 16 * S.boundConst :=
  ContinuousLinearMap.opNorm_le_bound _ (by have := S.boundConst_nonneg; positivity)
    (S.norm_ellProj_apply_le h)

theorem norm_sub_ellProj_add_le (h : κ) (ζ : H.totalD.GraphSpace) (w : PiLp 2 (S.V h)) :
    ‖w - S.ellProj h ζ‖ + ‖S.D h (w - S.ellProj h ζ)‖ ≤
      8 * (‖(1 - S.J h) w‖ + ‖(1 - S.J h) (S.D h w)‖ +
        2 * S.boundConst * ‖ζ - S.graphIncl h w‖) := by
  set p := ‖(1 - S.J h) w‖
  set q := ‖(1 - S.J h) (S.D h w)‖
  set e := w - S.ellProj h ζ
  have he : e - S.L h e = (w - S.L h w) - S.G h ζ := by
    simp only [e, _root_.map_sub]; rw [← S.ellProj_sub]; abel
  refine (S.cpx h).norm_add_norm_le_of_inner e (by
    have := S.boundConst_nonneg; positivity) fun v => ?_
  have hsplit : ⟪e - S.L h e, v⟫_𝕜 = ⟪(1 - S.J h) w, v⟫_𝕜 - ⟪(1 - S.J h) (S.D h w), v⟫_𝕜 +
      ⟪(1 - S.J h) w, S.D h v⟫_𝕜 + ⟪S.G h (S.graphIncl h w - ζ), v⟫_𝕜 := by
    rw [he, (S.G h).map_sub, inner_sub_left, inner_sub_left, inner_sub_left,
      inner_waveL, S.inner_G_graphIncl]
    simp only [_root_.sub_apply, one_apply_eq_self, inner_sub_left]
    ring
  rw [hsplit]
  have b1 : ‖⟪(1 - S.J h) w, v⟫_𝕜‖ ≤ p * ‖v‖ := norm_inner_le_norm _ _
  have b2 : ‖⟪(1 - S.J h) (S.D h w), v⟫_𝕜‖ ≤ q * ‖v‖ := norm_inner_le_norm _ _
  have b3 : ‖⟪(1 - S.J h) w, S.D h v⟫_𝕜‖ ≤ p * ‖S.D h v‖ := norm_inner_le_norm _ _
  have b4 := S.norm_inner_G_le h (S.graphIncl h w - ζ) v
  rw [norm_sub_rev] at b4
  have hq : 0 ≤ q := norm_nonneg _
  have hv := norm_nonneg v
  have hDv := norm_nonneg (S.D h v)
  calc _ ≤ ‖⟪(1 - S.J h) w, v⟫_𝕜‖ + ‖⟪(1 - S.J h) (S.D h w), v⟫_𝕜‖ +
        ‖⟪(1 - S.J h) w, S.D h v⟫_𝕜‖ + ‖⟪S.G h (S.graphIncl h w - ζ), v⟫_𝕜‖ :=
        (norm_add_le _ _).trans (by
          gcongr
          exact (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _))
    _ ≤ _ := by nlinarith [mul_nonneg hq hDv]

/-- **The Strang lemma**: best approximation in the graph norm plus the inner-product defect at `w`
and `𝐝ₕ w` (cf. [HolstStern2012], Thm 3.9, Thm 3.10). -/
theorem norm_graphFst_sub_inclL_ellProj_le (h : κ) (ζ : H.totalD.GraphSpace)
    (w : PiLp 2 (S.V h)) :
    ‖H.totalD.graphFst ζ - S.inclL h (S.ellProj h ζ)‖ ≤
      (1 + 16 * S.boundConst ^ 2) * ‖ζ - S.graphIncl h w‖ +
        8 * S.boundConst * (‖(1 - S.J h) w‖ + ‖(1 - S.J h) (S.D h w)‖) := by
  have e : H.totalD.graphFst ζ - S.inclL h (S.ellProj h ζ) =
      H.totalD.graphFst (ζ - S.graphIncl h w) + S.inclL h (w - S.ellProj h ζ) := by
    rw [H.totalD.graphFst.map_sub, (S.inclL h).map_sub, S.graphFst_graphIncl]; abel
  rw [e]
  have h1 : ‖H.totalD.graphFst (ζ - S.graphIncl h w)‖ ≤ ‖ζ - S.graphIncl h w‖ :=
    norm_graphFst_le _
  have h2 := S.norm_inclL_apply_le h (w - S.ellProj h ζ)
  have h3 := S.norm_sub_ellProj_add_le h ζ w
  have hC := S.boundConst_nonneg
  have h5 : ‖w - S.ellProj h ζ‖ ≤ 8 * (‖(1 - S.J h) w‖ + ‖(1 - S.J h) (S.D h w)‖ +
      2 * S.boundConst * ‖ζ - S.graphIncl h w‖) := by
    linarith [norm_nonneg (S.D h (w - S.ellProj h ζ))]
  calc _ ≤ ‖H.totalD.graphFst (ζ - S.graphIncl h w)‖ + ‖S.inclL h (w - S.ellProj h ζ)‖ :=
        norm_add_le _ _
    _ ≤ ‖ζ - S.graphIncl h w‖ + S.boundConst * (8 * (‖(1 - S.J h) w‖ +
          ‖(1 - S.J h) (S.D h w)‖ + 2 * S.boundConst * ‖ζ - S.graphIncl h w‖)) :=
        add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_left h5 hC))
    _ = _ := by ring

/-! #### The consistency defect -/

/-- The **defect operator** `Δₕ = Rₕ - iₕ* graphFst : Γ(𝐝) → Vₕ`. -/
def defectOp (h : κ) : H.totalD.GraphSpace →L[𝕜] PiLp 2 (S.V h) :=
  S.ellProj h - (S.inclL h).adjoint ∘L H.totalD.graphFst

theorem norm_defectOp_le (h : κ) : ‖S.defectOp h‖ ≤ 17 * S.boundConst := by
  refine (norm_sub_le (S.ellProj h) ((S.inclL h).adjoint ∘L H.totalD.graphFst)).trans ?_
  have h1 := S.norm_ellProj_le h
  have h2 : ‖(S.inclL h).adjoint ∘L H.totalD.graphFst‖ ≤ S.boundConst := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [ContinuousLinearMap.adjoint.norm_map (S.inclL h)]
    have h3 : ‖H.totalD.graphFst‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ζ => by
        rw [one_mul]; exact norm_graphFst_le ζ
    have := S.norm_inclL_le h
    nlinarith [norm_nonneg (S.inclL h), norm_nonneg H.totalD.graphFst]
  linarith

theorem ellProj_defect (h : κ) (y : H.wave.domain) (hLy : H.wave y ∈ H.wave.domain) :
    S.ellProj h (waveLift H ⟨_, hLy⟩) - S.L h (S.ellProj h (waveLift H y)) =
      S.defectOp h (waveLift H ⟨_, hLy⟩) + (-S.defectOp h) (waveLift H y) := by
  have e := S.ellProj_sub h (waveLift H y)
  rw [S.G_waveLift] at e
  have e' : S.L h (S.ellProj h (waveLift H y)) = S.ellProj h (waveLift H y) -
      (S.inclL h).adjoint ((y : PiLp 2 W) - H.wave y) := by rw [← e]; abel
  rw [e', _root_.neg_apply, defectOp, _root_.sub_apply,
    _root_.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, graphFst_waveLift, graphFst_waveLift, _root_.map_sub]
  abel

theorem norm_defectOp_apply_le (h : κ) (ζ : H.totalD.GraphSpace) :
    ‖S.defectOp h ζ‖ ≤ ‖(1 - S.J h) (S.ellProj h ζ)‖ +
      S.boundConst * ‖H.totalD.graphFst ζ - S.inclL h (S.ellProj h ζ)‖ := by
  have e : S.defectOp h ζ = (1 - S.J h) (S.ellProj h ζ) -
      (S.inclL h).adjoint (H.totalD.graphFst ζ - S.inclL h (S.ellProj h ζ)) := by
    simp only [defectOp, J, _root_.sub_apply, one_apply_eq_self,
      ContinuousLinearMap.comp_apply, _root_.map_sub]
    abel
  rw [e]
  refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
  refine ((S.inclL h).adjoint.le_opNorm _).trans ?_
  rw [ContinuousLinearMap.adjoint.norm_map (S.inclL h)]
  exact mul_le_mul_of_nonneg_right (S.norm_inclL_le h) (norm_nonneg _)

theorem norm_one_sub_J_ellProj_le (h : κ) (ζ : H.totalD.GraphSpace) :
    ‖(1 - S.J h) (S.ellProj h ζ)‖ ≤ S.graphDefect h * (16 * S.boundConst * ‖ζ‖) :=
  ((S.D h).norm_apply_le_graphOpNorm (1 - S.J h) _).trans
    (mul_le_mul_of_nonneg_left (S.norm_ellProj_add_le h ζ) ((S.D h).graphOpNorm_nonneg _))

instance (h : κ) (K : Submodule 𝕜 (PiLp 2 (S.V h))) : K.HasOrthogonalProjection :=
  haveI := FiniteDimensional.complete 𝕜 K; .ofCompleteSpace K

instance (h : κ) (i : ι) (K : Submodule 𝕜 (S.V h i)) : K.HasOrthogonalProjection :=
  haveI := FiniteDimensional.complete 𝕜 K; .ofCompleteSpace K

/-- The **approximation property in the graph norm**: every `ζ ∈ Γ(𝐝)` is approximated by lifts. -/
def GraphApprox (l : Filter κ) : Prop :=
  ∀ ζ : H.totalD.GraphSpace, ∀ ε > 0, ∀ᶠ h in l, ∃ v : PiLp 2 (S.V h), ‖ζ - S.graphIncl h v‖ < ε

theorem graphApprox_of_commute {l : Filter κ}
    (hπ : ∀ x : PiLp 2 W, Tendsto (fun h => S.inclL h (S.projL h x)) l (𝓝 x))
    {Z : Set H.totalD.GraphSpace} (hZ : Dense Z)
    (hcomm : ∀ ζ ∈ Z, Tendsto (fun h => ‖S.D h (S.projL h (H.totalD.graphFst ζ)) -
      S.projL h (H.totalD.graphSnd ζ)‖) l (𝓝 0)) :
    S.GraphApprox l := by
  intro ζ ε hε
  obtain ⟨ζ', hζ', hd⟩ := hZ.exists_dist_lt ζ (half_pos hε)
  rw [dist_eq_norm] at hd
  set C := S.boundConst
  have hC := S.boundConst_nonneg
  have hε6 : 0 < ε / 6 := by positivity
  have hε6' : 0 < ε / (6 * (C + 1)) := by positivity
  filter_upwards [Metric.tendsto_nhds.1 (hπ (H.totalD.graphFst ζ')) _ hε6,
    Metric.tendsto_nhds.1 (hπ (H.totalD.graphSnd ζ')) _ hε6,
    Metric.tendsto_nhds.1 (hcomm ζ' hζ') _ hε6'] with h h1 h2 h3
  refine ⟨S.projL h (H.totalD.graphFst ζ'), ?_⟩
  set v := S.projL h (H.totalD.graphFst ζ')
  rw [dist_eq_norm, norm_sub_rev] at h1 h2
  rw [dist_eq_norm, sub_zero, Real.norm_of_nonneg (norm_nonneg _)] at h3
  have e1 : H.totalD.graphFst (ζ' - S.graphIncl h v) =
      H.totalD.graphFst ζ' - S.inclL h (S.projL h (H.totalD.graphFst ζ')) := by
    rw [H.totalD.graphFst.map_sub, S.graphFst_graphIncl]
  have e2 : H.totalD.graphSnd (ζ' - S.graphIncl h v) =
      (H.totalD.graphSnd ζ' - S.inclL h (S.projL h (H.totalD.graphSnd ζ'))) -
        S.inclL h (S.D h v - S.projL h (H.totalD.graphSnd ζ')) := by
    rw [H.totalD.graphSnd.map_sub, S.graphSnd_graphIncl, (S.inclL h).map_sub]; abel
  have h4 : ‖S.inclL h (S.D h v - S.projL h (H.totalD.graphSnd ζ'))‖ ≤ C * (ε / (6 * (C + 1))) :=
    (S.norm_inclL_apply_le h _).trans (mul_le_mul_of_nonneg_left h3.le hC)
  have h5 : C * (ε / (6 * (C + 1))) ≤ ε / 6 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h6 : ‖ζ' - S.graphIncl h v‖ < ε / 2 := by
    refine (norm_le_norm_graphFst_add_norm_graphSnd _).trans_lt ?_
    rw [e1, e2]
    have := norm_sub_le (H.totalD.graphSnd ζ' - S.inclL h (S.projL h (H.totalD.graphSnd ζ')))
      (S.inclL h (S.D h v - S.projL h (H.totalD.graphSnd ζ')))
    linarith
  calc ‖ζ - S.graphIncl h v‖ = ‖(ζ - ζ') + (ζ' - S.graphIncl h v)‖ := by abel_nf
    _ ≤ ‖ζ - ζ'‖ + ‖ζ' - S.graphIncl h v‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hd h6
    _ = ε := add_halves ε

end ApproxComplex.Family

/-- An **approximating family of discrete complexes**: `graphDefect → 0` and `GraphApprox`. -/
structure ApproxComplex (H : HilbertComplex 𝕜 c W) (κ : Type*) where
  /-- the discrete complexes and reading maps -/
  toFamily : ApproxComplex.Family.{u} H κ
  /-- the constraint subspace -/
  K : Submodule 𝕜 (PiLp 2 W)
  isClosed_K : IsClosed (K : Set (PiLp 2 W))
  /-- the filter of refinement -/
  l : Filter κ
  tendsto_graphDefect : Tendsto toFamily.graphDefect l (𝓝 0)
  graphApprox : toFamily.GraphApprox l

namespace ApproxComplex

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxComplex.{u} H κ)

theorem tendsto_inclL_ellProj (ζ : H.totalD.GraphSpace) :
    Tendsto (fun h => F.toFamily.inclL h (F.toFamily.ellProj h ζ)) F.l
      (𝓝 (H.totalD.graphFst ζ)) := by
  set S := F.toFamily
  rw [Metric.tendsto_nhds]
  intro ε hε
  set A := 1 + 16 * S.boundConst ^ 2
  set B := 32 * S.boundConst ^ 2
  have hA : 0 < A := by positivity
  have hB : 0 ≤ B := by positivity
  set η := ε / (2 * A)
  have hη : 0 < η := by positivity
  set M := B * (‖ζ‖ + η)
  have hM : 0 ≤ M := by positivity
  set θ := ε / (2 * (M + 1))
  have hθ : 0 < θ := by positivity
  filter_upwards [F.graphApprox ζ η hη, Metric.tendsto_nhds.1 F.tendsto_graphDefect θ hθ]
    with h ⟨w, hw⟩ hδ
  rw [dist_eq_norm, sub_zero] at hδ
  replace hδ := (Real.le_norm_self _).trans_lt hδ
  rw [dist_eq_norm, norm_sub_rev]
  refine (S.norm_graphFst_sub_inclL_ellProj_le h ζ w).trans_lt ?_
  have hgw : ‖S.graphIncl h w‖ ≤ ‖ζ‖ + η := by
    have := norm_sub_norm_le (S.graphIncl h w) ζ
    rw [norm_sub_rev] at this
    linarith
  have t1 : A * ‖ζ - S.graphIncl h w‖ < ε / 2 := by
    have : A * ‖ζ - S.graphIncl h w‖ < A * η := mul_lt_mul_of_pos_left hw hA
    have e : A * η = ε / 2 := by simp only [η]; field_simp
    linarith
  have t2 : 8 * S.boundConst * (‖(1 - S.J h) w‖ + ‖(1 - S.J h) (S.D h w)‖) < ε / 2 := by
    have hC := S.boundConst_nonneg
    have hδ0 : 0 ≤ S.graphDefect h := (S.D h).graphOpNorm_nonneg _
    have hp : ‖(1 - S.J h) w‖ ≤ S.graphDefect h * (‖w‖ + ‖S.D h w‖) :=
      (S.D h).norm_apply_le_graphOpNorm _ w
    have hq : ‖(1 - S.J h) (S.D h w)‖ ≤ S.graphDefect h * ‖S.D h w‖ :=
      (S.D h).norm_apply_le_graphOpNorm_of_eq_zero _ ((S.cpx h).totalDL_totalDL w)
    have hpq : ‖(1 - S.J h) w‖ + ‖(1 - S.J h) (S.D h w)‖ ≤
        S.graphDefect h * (4 * S.boundConst * ‖S.graphIncl h w‖) := by
      have h1 := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (norm_nonneg w) : ‖S.D h w‖ ≤ ‖w‖ + ‖S.D h w‖) hδ0
      have h2 := mul_le_mul_of_nonneg_left (S.norm_add_norm_D_le h w) hδ0
      nlinarith
    have : 8 * S.boundConst * (‖(1 - S.J h) w‖ + ‖(1 - S.J h) (S.D h w)‖) ≤ M * θ := by
      calc 8 * S.boundConst * (‖(1 - S.J h) w‖ + ‖(1 - S.J h) (S.D h w)‖)
          ≤ 8 * S.boundConst * (S.graphDefect h * (4 * S.boundConst * ‖S.graphIncl h w‖)) :=
            mul_le_mul_of_nonneg_left hpq (by positivity)
        _ = B * S.graphDefect h * ‖S.graphIncl h w‖ := by ring
        _ ≤ B * θ * (‖ζ‖ + η) := by gcongr
        _ = M * θ := by ring
    have e : M * θ = ε / 2 * (M / (M + 1)) := by simp only [θ]; field_simp
    have : M / (M + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
    nlinarith
  linarith

theorem tendsto_defectOp (ζ : H.totalD.GraphSpace) :
    Tendsto (fun h => ‖F.toFamily.defectOp h ζ‖) F.l (𝓝 0) := by
  set S := F.toFamily
  have h1 := F.tendsto_graphDefect
  have h2 := tendsto_iff_norm_sub_tendsto_zero.1 (F.tendsto_inclL_ellProj ζ)
  have hb : Tendsto (fun h => S.graphDefect h * (16 * S.boundConst * ‖ζ‖) +
      S.boundConst * ‖H.totalD.graphFst ζ - S.inclL h (S.ellProj h ζ)‖) F.l (𝓝 0) := by
    have := (h1.mul_const (16 * S.boundConst * ‖ζ‖)).add (h2.const_mul S.boundConst)
    simp only [mul_zero, zero_mul, add_zero] at this
    refine this.congr fun h => ?_
    rw [norm_sub_rev (S.inclL h (S.ellProj h ζ))]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun h => (S.norm_defectOp_apply_le h ζ).trans
    (add_le_add (S.norm_one_sub_J_ellProj_le h ζ) le_rfl)) hb

end ApproxComplex

end Family

/-! ### The approximating FEEC discretization -/

section OfComplex

variable {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)]
  [∀ i, CompleteSpace (W i)]

namespace ApproxFEEC

variable {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxComplex.{u} H κ)

/-- **The approximating FEEC discretization** of `F`: `Xₕ = Vₕ`, `Lₕ = 𝐝ₕ - 𝐝ₕ*`, `ιₕ = iₕ`. -/
def ofComplex : ApproxFEEC H κ where
  K := F.K
  isClosed_K := F.isClosed_K
  l := F.l
  X h := PiLp 2 (F.toFamily.V h)
  L h := F.toFamily.L h
  isSkewAdjoint := H.isSkewAdjoint_wave
  skew h := (F.toFamily.cpx h).waveL_skew
  incl h := F.toFamily.inclL h
  proj h := F.toFamily.projL h
  proj_incl h v := F.toFamily.projL_inclL h v
  bound := ⟨F.toFamily.boundConst, fun h => ⟨F.toFamily.norm_inclL_le h,
    F.toFamily.norm_projL_le h⟩⟩

theorem ofComplex_group (h : κ) (t : ℝ) (v : PiLp 2 (F.toFamily.V h)) :
    ((ofComplex F).group h).S t v = (F.toFamily.cpx h).waveGroup.S t v :=
  (F.toFamily.cpx h).ofBounded_waveL_S t v

theorem ofComplex_sol (h : κ) (v : PiLp 2 (F.toFamily.V h)) (t : ℝ) :
    (ofComplex F).sol h v t = F.toFamily.inclL h ((F.toFamily.cpx h).waveGroup.S t v) := by
  change (ofComplex F).incl h (((ofComplex F).group h).S t v) = _
  rw [ofComplex_group]; rfl

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]

/-- **The core of `ofComplex`**: `D(L²)`, with the modified elliptic projections of the orbits. -/
def ofComplexCore : (ofComplex F).Core :=
  Core.ofOperator (ofComplex F) F.toFamily.ellProj
    ⟨_, F.toFamily.norm_ellProj_le⟩ F.tendsto_inclL_ellProj
    F.toFamily.defectOp (fun h => -F.toFamily.defectOp h)
    ⟨_, fun h => ⟨F.toFamily.norm_defectOp_le h,
      (norm_neg (F.toFamily.defectOp h)).trans_le (F.toFamily.norm_defectOp_le h)⟩⟩
    F.toFamily.ellProj_defect F.tendsto_defectOp
    (fun ζ => (F.tendsto_defectOp ζ).congr fun _ => (norm_neg _).symm)

theorem dense_ofComplexCore_data : Dense ((ofComplexCore F).Data : Set (PiLp 2 W)) :=
  H.isSkewAdjoint_wave.dense_domainSq

theorem ofComplexCore_cmp_p (T : ℝ) {x : PiLp 2 W} (hx : x ∈ H.wave.domain) (h : κ) {t : ℝ}
    (ht : 0 ≤ t) : ((ofComplexCore F).cmp T).p x h t = F.toFamily.ellProj h (waveOrbit H x t) :=
  Comparison.ofOperator_p _ _ T hx h ht

theorem ofComplexCore_cmp_p' (T : ℝ) {x : PiLp 2 W} (hx : x ∈ H.wave.domainSq) (h : κ) {t : ℝ}
    (ht : 0 ≤ t) :
    ((ofComplexCore F).cmp T).p' x h t = F.toFamily.ellProj h (waveOrbit H (waveExt H x) t) :=
  Comparison.ofOperator_p' _ _ T hx h ht

end ApproxFEEC

open ApproxFEEC in
/-- **The approximating FEEC theorem for approximating families of discrete complexes**, with the
discrete constraints and the Strang and consistency defect bounds. -/
theorem approxFEEC_ofComplex [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
    {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ApproxComplex.{u} H κ) :
    (ofComplex F).Verdict (ofComplexCore F) ∧
    Dense ((ofComplexCore F).Data : Set (PiLp 2 W)) ∧
    -- 2. the discrete generator and group
    (∀ h v, (ofComplex F).L h v = (F.toFamily.cpx h).wave
      ⟨v, (F.toFamily.cpx h).mem_wave_domain_of_finiteDimensional v⟩) ∧
    (∀ h t v, ((ofComplex F).group h).S t v = (F.toFamily.cpx h).waveGroup.S t v) ∧
    -- 3. discrete constraints
    (∀ h (Kh : Submodule 𝕜 (PiLp 2 (F.toFamily.V h))),
      (F.toFamily.cpx h).wave.IsReducing Kh ↔
        ∀ t, ∀ v ∈ Kh, ((ofComplex F).group h).S t v ∈ Kh) ∧
    (∀ h (Sh : ∀ i, Submodule 𝕜 (F.toFamily.V h i)), (F.toFamily.cpx h).ReducingSubcomplex Sh →
      ∀ v ∈ totalSub Sh, ∀ t, ((ofComplex F).group h).S t v ∈ totalSub Sh ∧
        ∀ i, Sh i ≤ (F.toFamily.cpx h).cycles i → (ofComplex F).sol h v t i ∈ H.cycles i) ∧
    (∀ h (Kh : Submodule 𝕜 (PiLp 2 (F.toFamily.V h))), (F.toFamily.cpx h).wave.IsReducing Kh →
      Kh.map (F.toFamily.inclL h : PiLp 2 (F.toFamily.V h) →ₗ[𝕜] PiLp 2 W) ≤ F.K →
      ∀ v ∈ Kh, ∀ t, infDist ((ofComplex F).sol h v t) (F.K : Set (PiLp 2 W)) = 0) ∧
    -- 4. the Strang estimate and the consistency defect, with their limits
    (∀ h ζ w, ‖H.totalD.graphFst ζ - (ofComplex F).incl h (F.toFamily.ellProj h ζ)‖ ≤
      (1 + 16 * F.toFamily.boundConst ^ 2) * ‖ζ - F.toFamily.graphIncl h w‖ +
        8 * F.toFamily.boundConst *
          (‖(1 - F.toFamily.J h) w‖ + ‖(1 - F.toFamily.J h) (F.toFamily.D h w)‖)) ∧
    (∀ h ζ, ‖F.toFamily.defectOp h ζ‖ ≤ ‖(1 - F.toFamily.J h) (F.toFamily.ellProj h ζ)‖ +
        F.toFamily.boundConst * ‖H.totalD.graphFst ζ -
          (ofComplex F).incl h (F.toFamily.ellProj h ζ)‖) ∧
    (∀ ζ, Tendsto (fun h => (ofComplex F).incl h (F.toFamily.ellProj h ζ)) F.l
      (𝓝 (H.totalD.graphFst ζ))) ∧
    (∀ ζ, Tendsto (fun h => ‖F.toFamily.defectOp h ζ‖) F.l (𝓝 0)) := by
  set S := F.toFamily
  have hiff : ∀ h (Kh : Submodule 𝕜 (PiLp 2 (S.V h))), (S.cpx h).wave.IsReducing Kh ↔
      ∀ t, ∀ v ∈ Kh, ((ofComplex F).group h).S t v ∈ Kh := fun h Kh => by
    rw [(S.cpx h).isReducing_iff_waveGroup_invariant Kh, C0Group.map_le_iff_forall]
    exact forall_congr' fun t => forall₂_congr fun v _ => by rw [ofComplex_group]; rfl
  refine ⟨approxFEEC _ _, dense_ofComplexCore_data F, fun h => (F.toFamily.cpx h).waveL_apply,
    ofComplex_group F, hiff,
    fun h Sh hS v hv t => ?_, fun h Kh hK hKK v hv t => ?_,
    S.norm_graphFst_sub_inclL_ellProj_le, S.norm_defectOp_apply_le, F.tendsto_inclL_ellProj,
    F.tendsto_defectOp⟩
  · have hmem : ((ofComplex F).group h).S t v ∈ totalSub Sh := by
      rw [ofComplex_group]; exact hS.waveGroup_mem t hv
    refine ⟨hmem, fun i hi => ?_⟩
    rw [ofComplex_sol]
    set u := (S.cpx h).waveGroup.S t v
    have hu : u ∈ totalSub Sh := hS.waveGroup_mem t hv
    obtain ⟨y, hy, hy0⟩ := LinearPMap.mem_ker_iff.1
      (show u i ∈ ((S.cpx h).d i (c.next i)).ker from hi (hu i))
    refine LinearPMap.mem_ker_iff.2 ⟨⟨_, S.incl_mem h i (c.next i) (u i)⟩, rfl, ?_⟩
    have e := S.incl_d h i (c.next i) y
    rw [hy0, _root_.map_zero] at e
    rw [← e]
    congr 2
    rw [hy]
  · have hmem := (hiff h Kh).1 hK t v hv
    refine Metric.infDist_zero_of_mem (hKK ⟨_, hmem, rfl⟩)

/-! ### The conforming case: constrained FEEC discretizations -/

namespace ConstrainedFEEC

variable [∀ i, NormedSpace ℝ (W i)] [∀ i, IsScalarTower ℝ 𝕜 (W i)]
  {H : HilbertComplex 𝕜 c W} {κ : Type*} (F : ConstrainedFEEC H κ)

/-- The discrete complexes of a constrained FEEC discretization, `iₕ` the inclusions. -/
def toFamily : ApproxComplex.Family H κ where
  V h i := ↥((F.V h).V i)
  completeSpace _ _ := FiniteDimensional.complete 𝕜 _
  cpx h := (F.V h).toHilbertComplex
  incl h i := ((F.V h).V i).subtypeL
  incl_mem h i j v := (F.V h).le_domain i j v.2
  incl_d _ _ _ _ := rfl
  proj h i := ((F.V h).V i).orthogonalProjectionOnto
  proj_incl h i v := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self v
  bound := ⟨1, fun h i =>
    ⟨ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [one_mul]; exact le_rfl,
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
        rw [one_mul]; exact ((F.V h).V i).norm_orthogonalProjectionOnto_apply_le x⟩⟩

theorem toFamily_J (h : κ) : F.toFamily.J h = 1 := by
  refine ContinuousLinearMap.ext fun v => ext_inner_right 𝕜 fun w => ?_
  rw [ApproxComplex.Family.inner_J, one_apply_eq_self, PiLp.inner_apply,
    PiLp.inner_apply]
  rfl

theorem toFamily_graphApprox : F.toFamily.GraphApprox F.l := fun ζ ε hε => by
  filter_upwards [F.dense_graph ζ ε hε] with h ⟨w, hw, hlt⟩
  refine ⟨WithLp.toLp 2 fun i => ⟨H.totalD.graphFst w i, hw i⟩, ?_⟩
  convert hlt using 3
  exact H.totalD.graphFst_injective (by rw [F.toFamily.graphFst_graphIncl]; rfl)

/-- **A constrained FEEC discretization as an approximating family**, with `Jₕ = 1`. -/
def toComplex : ApproxComplex H κ where
  toFamily := F.toFamily
  K := F.K
  isClosed_K := F.isClosed_K
  l := F.l
  tendsto_graphDefect := tendsto_const_nhds.congr fun h => by
    rw [ApproxComplex.Family.graphDefect, F.toFamily_J, sub_self]
    exact ((ContinuousLinearMap.graphOpNorm_eq_zero_iff _ _).2 rfl).symm
  graphApprox := F.toFamily_graphApprox

/-- The identification of the total discrete space of `toFamily` with `Xₕ = ∏ Vₕⁱ ⊆ W`. -/
def toXh (h : κ) : PiLp 2 (F.toFamily.V h) →L[𝕜] F.Xh h :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ⟨F.toFamily.inclL h v, fun i => (v i).2⟩
      map_add' := fun v w => Subtype.ext ((F.toFamily.inclL h).map_add v w)
      map_smul' := fun a v => Subtype.ext ((F.toFamily.inclL h).map_smul a v) }

theorem coe_toXh (h : κ) (v : PiLp 2 (F.toFamily.V h)) :
    (F.toXh h v : PiLp 2 W) = F.toFamily.inclL h v := rfl

theorem inner_toXh (h : κ) (v w : PiLp 2 (F.toFamily.V h)) :
    ⟪F.toXh h v, F.toXh h w⟫_𝕜 = ⟪v, w⟫_𝕜 := by
  rw [Submodule.coe_inner, coe_toXh, coe_toXh, ← ApproxComplex.Family.inner_J, F.toFamily_J,
    one_apply_eq_self]

theorem toXh_surjective (h : κ) : Function.Surjective (F.toXh h) := fun y =>
  ⟨WithLp.toLp 2 fun i => ⟨(y : PiLp 2 W) i, y.2 i⟩, Subtype.ext rfl⟩

theorem toXh_L (h : κ) (v : PiLp 2 (F.toFamily.V h)) :
    F.toXh h (F.toFamily.L h v) = F.discreteWave h (F.toXh h v) := by
  refine ext_inner_right 𝕜 fun y => ?_
  obtain ⟨w, rfl⟩ := F.toXh_surjective h y
  rw [F.inner_toXh, inner_waveL, F.inner_discreteWave, ← F.inner_toXh, ← F.inner_toXh,
    Submodule.coe_inner, Submodule.coe_inner]
  congr 1 <;> congr 1
  all_goals first | exact F.toFamily.inclL_D h v | exact F.toFamily.inclL_D h w

/-- **The conforming instance recovers the subcomplex scheme** through `Vₕ ≅ Xₕ`
([QuennevilleBelair2015], (4.10)). -/
theorem toComplex_sol (h : κ) (v : PiLp 2 (F.toFamily.V h)) (t : ℝ) :
    (ApproxFEEC.ofComplex F.toComplex).sol h v t = F.toApprox.sol h (F.toXh h v) t := by
  set B := F.toFamily.L h
  set u : ℝ → F.Xh h := fun s => F.toXh h ((C0Group.ofBounded B).S s v)
  have hu : ∀ s, HasDerivAt u (F.discreteWave h (u s)) s := fun s => by
    have hd := ((F.toXh h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
      (ContinuousLinearMap.hasDerivAt_exp_ofReal_smul_apply B v s)
    rw [← F.toXh_L]
    exact hd
  have e := eq_ofBounded_of_hasDerivAt (F.discreteWave h) (F.discreteWave_skew h) hu t
  have e0 : u 0 = F.toXh h v := by simp only [u, C0Group.S_zero_apply]
  rw [e0] at e
  change F.toFamily.inclL h ((C0Group.ofBounded B).S t v) = _
  rw [toApprox_sol_eq, ← coe_toXh]
  exact congrArg Subtype.val e

theorem toXh_injective (h : κ) : Function.Injective (F.toXh h) := fun _ _ hab =>
  F.toFamily.inclL_injective h (congrArg Subtype.val hab)

theorem toXh_inclL_adjoint (h : κ) (z : PiLp 2 W) :
    F.toXh h ((F.toFamily.inclL h).adjoint z) = F.orthProj h z := by
  refine ext_inner_right 𝕜 fun y => ?_
  obtain ⟨w, rfl⟩ := F.toXh_surjective h y
  rw [F.inner_toXh, ContinuousLinearMap.adjoint_inner_left,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  rfl

theorem toXh_ellProj_waveLift (h : κ) (y : H.wave.domain) :
    F.toXh h (F.toFamily.ellProj h (waveLift H y)) = F.ellipticProj h (waveLift H y) := by
  obtain ⟨r, hr⟩ := F.toXh_surjective h (F.ellipticProj h (waveLift H y))
  rw [← hr]
  refine congrArg (F.toXh h) (F.toFamily.eq_ellProj h ?_).symm
  refine F.toXh_injective h ?_
  rw [F.toFamily.G_waveLift, F.toXh_inclL_adjoint, (F.toXh h).map_sub, F.toXh_L, hr,
    F.discreteWave_ellipticProj, (F.orthProj h).map_sub]
  abel

theorem toComplex_verdict :
    (ApproxFEEC.ofComplex F.toComplex).Verdict (ApproxFEEC.ofComplexCore F.toComplex) :=
  (approxFEEC_ofComplex F.toComplex).1

end ConstrainedFEEC

end OfComplex

end Feec.HilbertComplex
