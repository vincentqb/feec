module

public import Feec.Physics.EinsteinBianchi.MatrixModel
public import Feec.Physics.EinsteinBianchi.WaveFEMTangentialCube
public import Feec.Counterexamples.BoundedBGG

/-!
# The scheme (6.5) converges to a solution that leaves TSD

For the semi-discrete scheme (6.5) of [QuennevilleBelair2015], §6.3 on `Q = (0, ½)³`: energy
estimates, convergence for solutions approximable by the `O(h)` rate class, and the TSD datum
`(0, 0, (0, β))`, whose solution leaves TSD and starts outside the rate class.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace LinearPMap
open Set Filter Topology MeasureTheory

@[expose] public noncomputable section

/-! ### Energy estimates for solutions with different sources -/

namespace Feec.BGG

namespace WaveData

variable {V0 Vt0 Vt1 W0 W1 W2 Wt1 Wt2 : Type*}
  [NormedAddCommGroup V0] [InnerProductSpace ℝ V0] [CompleteSpace V0]
  [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0] [CompleteSpace Vt0]
  [AddCommGroup Vt1] [Module ℝ Vt1]
  [NormedAddCommGroup W0] [InnerProductSpace ℝ W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
  [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1]
  [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]
  {D : WaveData V0 Vt0 Vt1 W0 W1 W2 Wt1 Wt2}

/-- The energy vector `(σ, u, M, ρ)(t)` of a trajectory of (6.1), in `W⁰ × W̃¹ × W² × W̃²`. -/
def Trajectory.vec {T : ℝ} {f : ℝ → Wt1} (s : D.Trajectory T f) (t : ℝ) :
    Feec.BGG.EnergySpace W0 Wt1 W2 Wt2 :=
  Feec.BGG.energyEmb W0 Wt1 W2 Wt2 (D.i0 (s.σ t), D.it1 (s.u t), s.M t, s.ρ t)

theorem Solution.norm_vec_le {T : ℝ} {f : ℝ → Wt1} (s : D.Solution T f)
    (hf : ContinuousOn f (Icc 0 T)) :
    ∀ t ∈ Icc 0 T, ‖s.vec t‖ ≤ ‖s.vec 0‖ + ∫ r in (0:ℝ)..t, ‖f r‖ := by
  have hι := Feec.BGG.isEnergyEmbedding_energyEmb (V0 := W0) (Vt1 := Wt1)
    (W2 := W2) (Wt2 := Wt2)
  set ι := Feec.BGG.energyEmb W0 Wt1 W2 Wt2
  have hn : ∀ t, ‖s.vec t‖ = √(‖D.i0 (s.σ t)‖ ^ 2 + ‖D.it1 (s.u t)‖ ^ 2 + ‖s.M t‖ ^ 2 +
      ‖s.ρ t‖ ^ 2) := fun t => by
    have := Discrete.norm_sub_of_isEnergyEmbedding hι
      (D.i0 (s.σ t), D.it1 (s.u t), s.M t, s.ρ t) 0
    simpa [Trajectory.vec] using this
  refine Evolution.Energy.norm_le_add_integral_of_re_inner_deriv_le (𝕜 := ℝ)
    (e' := fun t => ι (s.σ' t, s.u' t, s.M' t, s.ρ' t)) (g := fun r => ‖f r‖)
    (ι.continuous.comp_continuousOn (s.cσ.prodMk (s.cu.prodMk (s.cM.prodMk s.cρ))))
    (fun t ht => ?_) hf.norm (fun _ _ => norm_nonneg _) (fun t ht => ?_)
  · have h1 : HasDerivWithinAt (fun r => (D.i0 (s.σ r), D.it1 (s.u r), s.M r, s.ρ r))
        (s.σ' t, s.u' t, s.M' t, s.ρ' t) (Ici t) t :=
      (s.dσ t ht).prodMk ((s.du t ht).prodMk ((s.dM t ht).prodMk (s.dρ t ht)))
    exact ι.hasFDerivAt.comp_hasDerivWithinAt t h1
  · rw [RCLike.re_to_real]
    change ⟪ι (s.σ' t, s.u' t, s.M' t, s.ρ' t), ι (D.i0 (s.σ t), D.it1 (s.u t), s.M t, s.ρ t)⟫ ≤
      ‖f t‖ * ‖s.vec t‖
    rw [hι]
    have ht' : t ∈ Icc 0 T := Ico_subset_Icc_self ht
    have ha := s.ea t ht (s.σ t) (s.φ t) (s.mem t ht')
    have hb := s.eb t ht (s.u t)
    have hcM := s.ec t ht (s.M t)
    have hdd := s.ed t ht (s.ρ t)
    have hu : ‖D.it1 (s.u t)‖ ≤ ‖s.vec t‖ := by
      rw [hn]; exact Real.le_sqrt_of_sq_le (by
        nlinarith [sq_nonneg (‖D.i0 (s.σ t)‖), sq_nonneg (‖s.M t‖), sq_nonneg (‖s.ρ t‖)])
    have hfu := (real_inner_le_norm (f t) (D.it1 (s.u t))).trans
      (mul_le_mul_of_nonneg_left hu (norm_nonneg _))
    simp only
    linarith [real_inner_comm (D.dt0 (s.φ t)) (D.it1 (s.u t)),
      real_inner_comm (D.S1 (s.u t)) (s.M t), real_inner_comm (D.dt1 (s.u t)) (s.ρ t),
      real_inner_comm (D.i0 (s.σ t)) (s.σ' t), real_inner_comm (D.it1 (s.u t)) (s.u' t),
      real_inner_comm (s.M t) (s.M' t), real_inner_comm (s.ρ t) (s.ρ' t)]

theorem Solution.norm_vec_sub_le {T : ℝ} {f₁ f₂ : ℝ → Wt1} (s₁ : D.Solution T f₁)
    (s₂ : D.Solution T f₂) (hf : ContinuousOn (f₁ - f₂) (Icc 0 T)) :
    ∀ t ∈ Icc 0 T, ‖s₁.vec t - s₂.vec t‖ ≤ ‖s₁.vec 0 - s₂.vec 0‖ +
      ∫ r in (0:ℝ)..t, ‖f₁ r - f₂ r‖ := by
  intro t ht
  have h := (s₁.sub' s₂).norm_vec_le hf t ht
  have e : ∀ r, (s₁.sub' s₂).vec r = s₁.vec r - s₂.vec r := fun r => by
    simp only [Trajectory.vec]
    rw [← map_sub]
    congr 1
    simp only [Solution.sub', Pi.sub_apply, map_sub, Prod.mk_sub_mk]
  rw [e, e] at h
  simpa using h

end WaveData

end Feec.BGG

namespace Feec.EinsteinBianchi.BoundedFailure

open Feec.Domain Feec.HilbertComplex Feec.FiniteElement Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry Feec.Models.BoundedDomain Feec.EinsteinBianchi.WaveFEM
  Feec.EinsteinBianchi.MatrixModel

/-! ### Classical solutions of (6.2) are solutions of (6.1) -/

set_option maxHeartbeats 4000000 in
/-- A classical solution of (6.2) is a solution of (6.1) of `cubeWaveData`. -/
def exactWave_toSolution {T : ℝ} {f : ℝ → Wv W1}
    (s : Feec.BGG.ExactWave bggSegment T (srcFun f)) : cubeWaveData.Solution T f where
  σ t := D0.toGraphSpace (s.σ t)
  φ t := toGraphVec0 (s.φ t)
  u := s.u
  M := s.M
  ρ := s.ρ
  σ' t := (s.σ' t : W0)
  u' t := incl1 (s.u' t)
  M' := s.M'
  ρ' := s.ρ'
  cσ := (continuous_subtype_val.comp_continuousOn s.cσ).congr fun t _ =>
    LinearPMap.graphFst_toGraphSpace D0 (s.σ t)
  cu := (incl1CLM.continuous.comp_continuousOn s.cu).congr fun t _ => rfl
  cM := s.cM
  cρ := s.cρ
  dσ t ht := by
    have h := (D0.domain.subtypeL.hasFDerivAt).comp_hasDerivWithinAt t (s.dσ t ht)
    exact h.congr (fun r _ => LinearPMap.graphFst_toGraphSpace D0 (s.σ r))
      (LinearPMap.graphFst_toGraphSpace D0 (s.σ t))
  du t ht := by
    have h := incl1CLM.hasFDerivAt.comp_hasDerivWithinAt t (s.du t ht)
    exact h.congr (fun r _ => rfl) rfl
  dM := s.dM
  dρ := s.dρ
  eb t ht v := by
    have h := s.eb t ht v
    change ⟪incl1 (s.u' t), incl1 v⟫ + ⟪ιt1 (bggDt0 (toGraphVec0 (s.φ t))), incl1 v⟫ +
      ⟪s.M t, segS1 v⟫ + ⟪s.ρ t, piMap segD1 v⟫ = ⟪f t, incl1 v⟫
    rw [ιt1_bggDt0_toGraphVec0, ← inner_wv_U1, ← inner_wv_U1]
    exact h
  ec := s.ec
  ed := s.ed
  mem t ht := by
    rw [cubeWaveData_d0, cubeWaveData_S0, ιt0_toGraphVec0, LinearPMap.graphSnd_toGraphSpace]
    exact congrArg Subtype.val (s.ee t ht)
  ea t ht τ ψ hτψ := by
    have h := s.ea t ht (D0.graphDom τ) (rp ψ)
    have e0 : bggSegment.d0 (D0.graphDom τ) = bggSegment.S0 (rp ψ) := by
      refine Subtype.ext ?_
      change D0 (D0.graphDom τ) = wsL2 (Ω := cubeDomain 3) 0 (incl0 (rp ψ))
      rw [LinearPMap.apply_graphDom, incl0_rp, ← cubeWaveData_S0, ← cubeWaveData_d0, hτψ]
    rw [e0, sub_self, map_zero, sub_zero] at h
    change ⟪(s.σ' t : W0), D0.graphFst τ⟫ - ⟪incl1 (s.u t), ιt1 (bggDt0 ψ)⟫ = 0
    rw [ιt1_bggDt0, ← inner_wv_U1]
    exact h

theorem exactWave_toSolution_vec {T : ℝ} {f : ℝ → Wv W1}
    (s : Feec.BGG.ExactWave bggSegment T (srcFun f)) (t : ℝ) :
    (exactWave_toSolution s).vec t =
      Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2) ((s.σ t : W0), incl1 (s.u t), s.M t, s.ρ t) :=
  rfl

/-! ### Strong solutions of the Hodge wave equation are solutions of (6.1) -/

section Strong

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-- The total space `Γ̄ × (L²Λ¹)³ × (L²Λ² × (L²Λ²)³)` of the forms model. -/
abbrev WS := PiLp 2 (ShortHilbertComplex.W3 bggHilb.Γbar (Wv W1) (WithLp 2 (W2 × Wv W2)))

/-- The `Γ̄` component of a point of the total space. -/
def comp0L : WS →L[ℝ] bggHilb.Γbar :=
  PiLp.proj (𝕜 := ℝ) 2 (ShortHilbertComplex.W3 bggHilb.Γbar (Wv W1) (WithLp 2 (W2 × Wv W2))) 0

/-- The `(L²Λ¹)³` component. -/
def comp1L : WS →L[ℝ] Wv W1 :=
  PiLp.proj (𝕜 := ℝ) 2 (ShortHilbertComplex.W3 bggHilb.Γbar (Wv W1) (WithLp 2 (W2 × Wv W2))) 1

/-- The `L²Λ² × (L²Λ²)³` component. -/
def comp2L : WS →L[ℝ] WithLp 2 (W2 × Wv W2) :=
  PiLp.proj (𝕜 := ℝ) 2 (ShortHilbertComplex.W3 bggHilb.Γbar (Wv W1) (WithLp 2 (W2 × Wv W2))) 2

/-- The `Γ̄` component. -/
abbrev comp0 (x : WS) : bggHilb.Γbar := comp0L x
/-- The `(L²Λ¹)³` component. -/
abbrev comp1 (x : WS) : Wv W1 := comp1L x
/-- The `L²Λ² × (L²Λ²)³` component. -/
abbrev comp2 (x : WS) : WithLp 2 (W2 × Wv W2) := comp2L x

/-- The `M` component `L²Λ²`. -/
def compML : WS →L[ℝ] W2 :=
  (ContinuousLinearMap.fst ℝ W2 (Wv W2)).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ W2 (Wv W2)).toContinuousLinearMap.comp comp2L)

/-- The `ρ` component `(L²Λ²)³`. -/
def compρL : WS →L[ℝ] Wv W2 :=
  (ContinuousLinearMap.snd ℝ W2 (Wv W2)).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ W2 (Wv W2)).toContinuousLinearMap.comp comp2L)

theorem compML_apply (x : WS) : compML x = (WithLp.ofLp (comp2 x)).1 := rfl
theorem compρL_apply (x : WS) : compρL x = (WithLp.ofLp (comp2 x)).2 := rfl

open Classical in
/-- The `Γ`-pair `(σ, φ)` of the first component of a point (`0` off `D(d₀)`). -/
def gammaOf (x : WS) : bggHilb.Γ :=
  if h : comp0 x ∈ bggHilb.D0Γ.domain then
    (bggHilb.mem_D0Γ_graph bggS0_injective ⟨_, h⟩).choose else 0

theorem jΓ_gammaOf {x : WS} (h : comp0 x ∈ bggHilb.D0Γ.domain) :
    bggHilb.jΓ (gammaOf x) = (comp0 x, bggHilb.D0Γ ⟨_, h⟩) := by
  unfold gammaOf
  split
  · rename_i h'
    exact (bggHilb.mem_D0Γ_graph bggS0_injective ⟨_, h'⟩).choose_spec
  · contradiction

theorem graphFst_gammaOf {x : WS} (h : comp0 x ∈ bggHilb.D0Γ.domain) :
    D0.graphFst ((gammaOf x : V0 × Vt0).1) = (comp0 x : W0) :=
  congrArg Subtype.val (congrArg Prod.fst (jΓ_gammaOf h))

theorem ιt1_bggDt0_gammaOf {x : WS} (h : comp0 x ∈ bggHilb.D0Γ.domain) :
    ιt1 (bggDt0 (gammaOf x : V0 × Vt0).2) = bggHilb.D0Γ ⟨_, h⟩ :=
  congrArg Prod.snd (jΓ_gammaOf h)

theorem mem_range_of_mem_D1L {y : Wv W1} (h : y ∈ bggHilb.D1L.domain) :
    y ∈ LinearMap.range (bggHilb.ιt1 : Vt1 →ₗ[ℝ] Wv W1) := by
  rw [← bggHilb.D1L_domain]; exact h

open Classical in
/-- The point of `H̊Λ¹(Q)³` (graph space) of the second component (`0` off `D(d₁)`). -/
def vecOf (x : WS) : Vt1 :=
  if h : comp1 x ∈ bggHilb.D1L.domain then (LinearMap.mem_range.1 (mem_range_of_mem_D1L h)).choose
    else 0

theorem ιt1_vecOf {x : WS} (h : comp1 x ∈ bggHilb.D1L.domain) : ιt1 (vecOf x) = comp1 x := by
  unfold vecOf
  split
  · rename_i h'
    exact (LinearMap.mem_range.1 (mem_range_of_mem_D1L h')).choose_spec
  · contradiction

theorem D1L_apply_ιt1 (v : Vt1) (h : ιt1 v ∈ bggHilb.D1L.domain) :
    bggHilb.D1L ⟨ιt1 v, h⟩ = bggHilb.TL v := by
  obtain ⟨y, hy1, hy2⟩ := bggHilb.mem_D1L_graph v
  rw [← hy2]
  exact congrArg bggHilb.D1L (Subtype.ext hy1.symm)

theorem D1L_apply_vecOf {x : WS} (h : comp1 x ∈ bggHilb.D1L.domain) :
    bggHilb.D1L ⟨_, h⟩ = bggHilb.TL (vecOf x) := by
  have h' : ιt1 (vecOf x) ∈ bggHilb.D1L.domain := by rw [ιt1_vecOf h]; exact h
  rw [← D1L_apply_ιt1 _ h']
  exact congrArg bggHilb.D1L (Subtype.ext (ιt1_vecOf h).symm)

open Classical in
/-- `L x` (`0` off `D(L)`). -/
def waveOf (x : WS) : WS := if h : x ∈ formsShort.wave.domain then formsShort.wave ⟨x, h⟩ else 0

theorem waveOf_eq {x : WS} (h : x ∈ formsShort.wave.domain) :
    waveOf x = formsShort.wave ⟨x, h⟩ := by
  unfold waveOf
  split
  · rfl
  · contradiction

/-- `σ` of the (6.1) trajectory of a point: `−` the `V⁰`-part of its `Γ`-pair. -/
def σOf (x : WS) : V0 := -(gammaOf x : V0 × Vt0).1
/-- `φ` of the (6.1) trajectory of a point. -/
def φOf (x : WS) : Vt0 := -(gammaOf x : V0 × Vt0).2
/-- `u` of the (6.1) trajectory of a point. -/
def uOf (x : WS) : Wv U1 := rp1 (vecOf x)

theorem graphFst_σOf {x : WS} (h : comp0 x ∈ bggHilb.D0Γ.domain) :
    D0.graphFst (σOf x) = -((comp0 x : bggHilb.Γbar) : W0) := by
  rw [σOf, map_neg, graphFst_gammaOf h]

theorem incl1_uOf {x : WS} (h : comp1 x ∈ bggHilb.D1L.domain) : incl1 (uOf x) = comp1 x := by
  rw [uOf, incl1_rp1, ιt1_vecOf h]

theorem cubeWaveData_dt0_φOf {x : WS} (h : comp0 x ∈ bggHilb.D0Γ.domain) :
    cubeWaveData.dt0 (φOf x) = -bggHilb.D0Γ ⟨_, h⟩ := by
  have e : cubeWaveData.dt0 (φOf x) = -ιt1 (bggDt0 (gammaOf x : V0 × Vt0).2) := by
    change ιt1 (bggDt0 (-(gammaOf x : V0 × Vt0).2)) = _
    rw [map_neg, map_neg]
  exact e.trans (congrArg Neg.neg (ιt1_bggDt0_gammaOf h))

section Point

set_option maxHeartbeats 2000000

variable {x : WS} (hx : x ∈ formsShort.wave.domain)
include hx

theorem dom0 : comp0 x ∈ bggHilb.D0Γ.domain := (formsShort.mem_wave_domain.1 hx).1
theorem dom1 : comp1 x ∈ bggHilb.D1L.domain := (formsShort.mem_wave_domain.1 hx).2.1
theorem dom1' : comp1 x ∈ bggHilb.D0Γ†.domain := (formsShort.mem_wave_domain.1 hx).2.2.1
theorem dom2 : comp2 x ∈ bggHilb.D1L†.domain := (formsShort.mem_wave_domain.1 hx).2.2.2

theorem comp0_waveOf : comp0 (waveOf x) = -(bggHilb.D0Γ† ⟨comp1 x, dom1' hx⟩) := by
  rw [waveOf_eq hx]
  exact formsShort.wave_apply_zero ⟨x, hx⟩

theorem comp1_waveOf : comp1 (waveOf x) =
    bggHilb.D0Γ ⟨comp0 x, dom0 hx⟩ - bggHilb.D1L† ⟨comp2 x, dom2 hx⟩ := by
  rw [waveOf_eq hx]
  exact formsShort.wave_apply_one ⟨x, hx⟩

theorem comp2_waveOf : comp2 (waveOf x) = bggHilb.D1L ⟨comp1 x, dom1 hx⟩ := by
  rw [waveOf_eq hx]
  exact formsShort.wave_apply_two ⟨x, hx⟩

theorem comp2_waveOf_eq_TL : comp2 (waveOf x) = bggHilb.TL (vecOf x) := by
  rw [comp2_waveOf hx, D1L_apply_vecOf (dom1 hx)]

theorem eb_point (v : Wv U1) :
    ⟪comp1 (waveOf x), cubeWaveData.it1 v⟫ + ⟪cubeWaveData.dt0 (φOf x), cubeWaveData.it1 v⟫ +
      ⟪compML x, cubeWaveData.S1 v⟫ + ⟪compρL x, cubeWaveData.dt1 v⟫ = 0 := by
  have hv : ιt1 (toGraphVec1 v) ∈ bggHilb.D1L.domain := by
    rw [bggHilb.D1L_domain]; exact ⟨toGraphVec1 v, rfl⟩
  have hadj := LinearPMap.adjoint_isFormalAdjoint formsShort.dense₁ ⟨comp2 x, dom2 hx⟩
    ⟨ιt1 (toGraphVec1 v), hv⟩
  change ⟪bggHilb.D1L† ⟨comp2 x, dom2 hx⟩, ιt1 (toGraphVec1 v)⟫ =
    ⟪comp2 x, bggHilb.D1L ⟨ιt1 (toGraphVec1 v), hv⟩⟫ at hadj
  rw [D1L_apply_ιt1, ιt1_toGraphVec1] at hadj
  have hTL : WithLp.ofLp (bggHilb.TL (toGraphVec1 v)) = (segS1 v, piMap segD1 v) := rfl
  rw [WithLp.prod_inner_apply, hTL] at hadj
  have e1 : cubeWaveData.it1 v = incl1 v := rfl
  have e2 : cubeWaveData.S1 v = segS1 v := rfl
  have e3 : cubeWaveData.dt1 v = piMap segD1 v := rfl
  rw [e1, e2, e3, cubeWaveData_dt0_φOf (dom0 hx), comp1_waveOf hx, compML_apply, compρL_apply]
  simp only [inner_sub_left, inner_neg_left]
  linarith

theorem ea_point (τ : V0) (ψ : Vt0) (h : cubeWaveData.d0 τ = cubeWaveData.S0 ψ) :
    ⟪-((comp0 (waveOf x) : bggHilb.Γbar) : W0), cubeWaveData.i0 τ⟫ -
      ⟪cubeWaveData.it1 (uOf x), cubeWaveData.dt0 ψ⟫ = 0 := by
  have hΓ : (τ, ψ) ∈ bggHilb.Γ := bggHilb.mem_Γ.2 (LinearPMap.graphFst_injective D1 h)
  have hg : bggHilb.jΓ ⟨(τ, ψ), hΓ⟩ ∈ bggHilb.D0Γ.graph := by
    rw [bggHilb.D0Γ_graph bggS0_injective]; exact ⟨_, rfl⟩
  obtain ⟨z, hz1, hz2⟩ := (LinearPMap.mem_graph_iff _).1 hg
  have hadj := LinearPMap.adjoint_isFormalAdjoint formsShort.dense₀ ⟨comp1 x, dom1' hx⟩ z
  change ⟪bggHilb.D0Γ† ⟨comp1 x, dom1' hx⟩, (z : bggHilb.Γbar)⟫ =
    ⟪comp1 x, bggHilb.D0Γ z⟫ at hadj
  rw [hz2] at hadj
  have hz : ((z : bggHilb.Γbar) : W0) = cubeWaveData.i0 τ := congrArg Subtype.val hz1
  have e1 : cubeWaveData.it1 (uOf x) = comp1 x := incl1_uOf (dom1 hx)
  have e2 : cubeWaveData.dt0 ψ = ιt1 (bggDt0 ψ) := rfl
  rw [comp0_waveOf hx, e1, e2, ← hz, Submodule.coe_neg, neg_neg, ← Submodule.coe_inner]
  change ⟪bggHilb.D0Γ† ⟨comp1 x, dom1' hx⟩, (z : bggHilb.Γbar)⟫ -
    ⟪comp1 x, (bggHilb.jΓ ⟨(τ, ψ), hΓ⟩).2⟫ = 0
  rw [hadj]
  exact sub_self _

theorem ec_point : (WithLp.ofLp (comp2 (waveOf x))).1 = segS1 (rp1 (vecOf x)) := by
  rw [comp2_waveOf_eq_TL hx]; rfl

theorem ed_point : (WithLp.ofLp (comp2 (waveOf x))).2 = piMap segD1 (rp1 (vecOf x)) := by
  rw [comp2_waveOf_eq_TL hx]
  exact bggDt1_eq (vecOf x)

end Point

theorem mem_gammaOf (x : WS) :
    cubeWaveData.d0 (-(gammaOf x : V0 × Vt0).1) = cubeWaveData.S0 (-(gammaOf x : V0 × Vt0).2) := by
  rw [map_neg, map_neg]
  have h : bggD0 (gammaOf x : V0 × Vt0).1 = bggS0 (gammaOf x : V0 × Vt0).2 :=
    bggHilb.mem_Γ.1 (gammaOf x).2
  change -D1.graphFst (bggD0 (gammaOf x : V0 × Vt0).1) =
    -D1.graphFst (bggS0 (gammaOf x : V0 × Vt0).2)
  rw [h]

theorem hasDerivWithinAt_Ici_of_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {f' : E} {T t : ℝ} (ht : t ∈ Ico 0 T) (hf : HasDerivWithinAt f f' (Icc 0 T) t)
    (hfg : EqOn g f (Icc 0 T)) : HasDerivWithinAt g f' (Ici t) t := by
  have hmem : Icc 0 T ∈ 𝓝[≥] t := Icc_mem_nhdsGE_of_mem ht
  refine (hf.mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq ?_ (hfg (Ico_subset_Icc_self ht))
  filter_upwards [hmem] with s hs using hfg hs

theorem _root_.Feec.Evolution.IsStrongSolution.hasDerivWithinAt_zero {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {A : E →ₗ.[ℝ] E} {I : Set ℝ} {U : ℝ → E}
    (hU : Evolution.IsStrongSolution A I 0 U) {t : ℝ} (ht : t ∈ I) :
    HasDerivWithinAt U (A ⟨U t, hU.mem_domain ht⟩) I t := by
  simpa using hU.hasDerivWithinAt ht

section Traj

variable {T : ℝ} {V : ℝ → WS} (hV : Evolution.IsStrongSolution formsShort.wave (Icc 0 T) 0 V)
include hV

theorem hasDerivWithinAt_waveOf {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt V (waveOf (V t)) (Icc 0 T) t :=
  (hV.hasDerivWithinAt_zero ht).congr_deriv (waveOf_eq (hV.mem_domain ht)).symm

theorem traj_cσ : ContinuousOn (fun s => D0.graphFst (σOf (V s))) (Icc 0 T) :=
  (((continuous_subtype_val.comp comp0L.continuous).comp_continuousOn hV.continuousOn).neg).congr
    fun _ hs => graphFst_σOf (dom0 (hV.mem_domain hs))

theorem traj_cu : ContinuousOn (fun s => incl1 (uOf (V s))) (Icc 0 T) :=
  (comp1L.continuous.comp_continuousOn hV.continuousOn).congr fun _ hs =>
    incl1_uOf (dom1 (hV.mem_domain hs))

theorem traj_dσ {t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (fun s => D0.graphFst (σOf (V s)))
      (-((comp0 (waveOf (V t)) : bggHilb.Γbar) : W0)) (Ici t) t :=
  hasDerivWithinAt_Ici_of_Icc ht
    (((bggHilb.Γbar.subtypeL.comp comp0L).hasFDerivAt.comp_hasDerivWithinAt
    t (hasDerivWithinAt_waveOf hV (Ico_subset_Icc_self ht))).neg)
    fun _ hs => graphFst_σOf (dom0 (hV.mem_domain hs))

theorem traj_du {t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (fun s => incl1 (uOf (V s))) (comp1 (waveOf (V t))) (Ici t) t :=
  hasDerivWithinAt_Ici_of_Icc ht (comp1L.hasFDerivAt.comp_hasDerivWithinAt t
    (hasDerivWithinAt_waveOf hV (Ico_subset_Icc_self ht)))
    fun _ hs => incl1_uOf (dom1 (hV.mem_domain hs))

theorem traj_dM {t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (fun s => compML (V s)) (compML (waveOf (V t))) (Ici t) t :=
  hasDerivWithinAt_Ici_of_Icc ht (compML.hasFDerivAt.comp_hasDerivWithinAt t
    (hasDerivWithinAt_waveOf hV (Ico_subset_Icc_self ht))) fun _ _ => rfl

theorem traj_dρ {t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (fun s => compρL (V s)) (compρL (waveOf (V t))) (Ici t) t :=
  hasDerivWithinAt_Ici_of_Icc ht (compρL.hasFDerivAt.comp_hasDerivWithinAt t
    (hasDerivWithinAt_waveOf hV (Ico_subset_Icc_self ht))) fun _ _ => rfl

theorem traj_eb {t : ℝ} (ht : t ∈ Ico 0 T) (v : Wv U1) :
    ⟪comp1 (waveOf (V t)), cubeWaveData.it1 v⟫ +
      ⟪cubeWaveData.dt0 (φOf (V t)), cubeWaveData.it1 v⟫ +
      ⟪compML (V t), cubeWaveData.S1 v⟫ + ⟪compρL (V t), cubeWaveData.dt1 v⟫ =
      ⟪(0 : ℝ → Wv W1) t, cubeWaveData.it1 v⟫ :=
  (eb_point (hV.mem_domain (Ico_subset_Icc_self ht)) v).trans
    (inner_zero_left (cubeWaveData.it1 v)).symm

theorem traj_ec {t : ℝ} (ht : t ∈ Ico 0 T) (N : W2) :
    ⟪compML (waveOf (V t)), N⟫ - ⟪cubeWaveData.S1 (uOf (V t)), N⟫ = 0 := by
  have h := ec_point (hV.mem_domain (Ico_subset_Icc_self ht))
  rw [← compML_apply] at h
  rw [h, uOf]
  exact sub_self _

theorem traj_ed {t : ℝ} (ht : t ∈ Ico 0 T) (μ : Wv W2) :
    ⟪compρL (waveOf (V t)), μ⟫ - ⟪cubeWaveData.dt1 (uOf (V t)), μ⟫ = 0 := by
  have h := ed_point (hV.mem_domain (Ico_subset_Icc_self ht))
  rw [← compρL_apply] at h
  rw [h, uOf]
  exact sub_self _

theorem traj_ea {t : ℝ} (ht : t ∈ Ico 0 T) (τ : V0) (ψ : Vt0)
    (h : cubeWaveData.d0 τ = cubeWaveData.S0 ψ) :
    ⟪-((comp0 (waveOf (V t)) : bggHilb.Γbar) : W0), cubeWaveData.i0 τ⟫ -
      ⟪cubeWaveData.it1 (uOf (V t)), cubeWaveData.dt0 ψ⟫ = 0 :=
  ea_point (hV.mem_domain (Ico_subset_Icc_self ht)) τ ψ h

/-- A strong solution of the forms-model Hodge wave equation, as a solution of (6.1). -/
def solutionOfStrong : cubeWaveData.Solution T 0 where
  σ t := σOf (V t)
  φ t := φOf (V t)
  u t := uOf (V t)
  M t := compML (V t)
  ρ t := compρL (V t)
  σ' t := -((comp0 (waveOf (V t)) : bggHilb.Γbar) : W0)
  u' t := comp1 (waveOf (V t))
  M' t := compML (waveOf (V t))
  ρ' t := compρL (waveOf (V t))
  cσ := traj_cσ hV
  cu := traj_cu hV
  cM := compML.continuous.comp_continuousOn hV.continuousOn
  cρ := compρL.continuous.comp_continuousOn hV.continuousOn
  dσ _ ht := traj_dσ hV ht
  du _ ht := traj_du hV ht
  dM _ ht := traj_dM hV ht
  dρ _ ht := traj_dρ hV ht
  eb _ ht v := traj_eb hV ht v
  ec _ ht N := traj_ec hV ht N
  ed _ ht μ := traj_ed hV ht μ
  mem t _ := mem_gammaOf (V t)
  ea _ ht τ ψ h := traj_ea hV ht τ ψ h

theorem solutionOfStrong_vec {t : ℝ} (ht : t ∈ Icc 0 T) :
    (solutionOfStrong hV).vec t = Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2)
      (-((comp0 (V t) : bggHilb.Γbar) : W0), comp1 (V t), compML (V t), compρL (V t)) := by
  have e1 : cubeWaveData.i0 ((solutionOfStrong hV).σ t) = -((comp0 (V t) : bggHilb.Γbar) : W0) :=
    graphFst_σOf (dom0 (hV.mem_domain ht))
  have e2 : cubeWaveData.it1 ((solutionOfStrong hV).u t) = comp1 (V t) :=
    incl1_uOf (dom1 (hV.mem_domain ht))
  show Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2) (cubeWaveData.i0 ((solutionOfStrong hV).σ t),
    cubeWaveData.it1 ((solutionOfStrong hV).u t), (solutionOfStrong hV).M t,
    (solutionOfStrong hV).ρ t) = _
  exact congrArg _ (Prod.ext e1 (Prod.ext e2 (Prod.ext rfl rfl)))

end Traj

end Strong

/-! ### Convergence of (6.5) from consistency on a dense class and stability (Lax) -/

section Lax

theorem integral_le_integral_T {g : ℝ → ℝ} {T t : ℝ} (hg : ContinuousOn g (Icc 0 T))
    (hg0 : ∀ r, 0 ≤ g r) (ht : t ∈ Icc 0 T) :
    ∫ r in (0:ℝ)..t, g r ≤ ∫ r in (0:ℝ)..T, g r :=
  intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 (Eventually.of_forall hg0)
    (hg.intervalIntegrable_of_Icc (ht.1.trans ht.2))

theorem integral_mono_Icc {g₁ g₂ : ℝ → ℝ} {T t : ℝ} (hg₁ : ContinuousOn g₁ (Icc 0 T))
    (hg₂ : ContinuousOn g₂ (Icc 0 T)) (h : ∀ r ∈ Icc 0 T, g₁ r ≤ g₂ r) (ht : t ∈ Icc 0 T) :
    ∫ r in (0:ℝ)..t, g₁ r ≤ ∫ r in (0:ℝ)..t, g₂ r :=
  intervalIntegral.integral_mono_on ht.1
    ((hg₁.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1)
    ((hg₂.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1)
    fun r hr => h r ⟨hr.1, hr.2.trans ht.2⟩

theorem lax_abstract {E : Type*} [SeminormedAddCommGroup E] {T : ℝ} {h : ℕ → ℝ}
    (hh : Tendsto h atTop (𝓝 0)) (w : ℝ → E) (sh : ℕ → ℝ → E)
    (h0 : Tendsto (fun N => ‖w 0 - sh N 0‖) atTop (𝓝 0)) (hT0 : 0 ≤ T)
    (happrox : ∀ δ > 0, ∃ (ws : ℝ → E) (wh : ℕ → ℝ → E) (a b c : ℝ), a + b < δ ∧ 0 ≤ b ∧
      (∀ t ∈ Icc 0 T, ‖w t - ws t‖ ≤ a + b) ∧ ‖w 0 - ws 0‖ ≤ a ∧
      (∀ N, ∀ t ∈ Icc 0 T, ‖ws t - wh N t‖ ≤ c * h N) ∧
      (∀ N, ∀ t ∈ Icc 0 T, ‖wh N t - sh N t‖ ≤ ‖wh N 0 - sh N 0‖ + b)) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ t ∈ Icc 0 T, ‖w t - sh N t‖ < ε := by
  intro ε hε
  have hδ : 0 < ε / 5 := by positivity
  obtain ⟨ws, wh, a, b, c, hab, hb, hcont, h0w, hrate, hstab⟩ := happrox (ε / 5) hδ
  have hc : Tendsto (fun N => 2 * c * h N) atTop (𝓝 0) := by
    simpa using hh.const_mul (2 * c)
  filter_upwards [Metric.tendsto_nhds.1 hc _ hδ, Metric.tendsto_nhds.1 h0 _ hδ] with N hN hN0 t ht
  rw [Real.dist_eq, sub_zero] at hN hN0
  rw [abs_of_nonneg (norm_nonneg _)] at hN0
  have h00 : ‖wh N 0 - sh N 0‖ ≤ c * h N + a + ‖w 0 - sh N 0‖ := by
    have e : wh N 0 - sh N 0 = -(ws 0 - wh N 0) - (w 0 - ws 0) + (w 0 - sh N 0) := by abel
    rw [e]
    have k1 := norm_add_le (-(ws 0 - wh N 0) - (w 0 - ws 0)) (w 0 - sh N 0)
    have k2 := norm_sub_le (-(ws 0 - wh N 0)) (w 0 - ws 0)
    rw [norm_neg] at k2
    have k3 := hrate N 0 ⟨le_rfl, hT0⟩
    linarith
  have e : w t - sh N t = (w t - ws t) + (ws t - wh N t) + (wh N t - sh N t) := by abel
  rw [e]
  have htri := norm_add₃_le (a := w t - ws t) (b := ws t - wh N t) (c := wh N t - sh N t)
  have h1 := hcont t ht
  have h2 := hrate N t ht
  have h3 := hstab N t ht
  have := abs_lt.1 hN
  nlinarith [norm_nonneg (w 0 - ws 0)]

variable (Q : Feec.BGG.Discrete bggSegment)

/-- The discrete source: the representer in `Ṽₕ¹` of `v ↦ ⟪f(t), v⟫`. -/
def srcQ [CompleteSpace Q.Vt1h] (f : ℝ → Wv W1) (t : ℝ) : Q.Vt1h :=
  (InnerProductSpace.toDual ℝ Q.Vt1h).symm
    ((innerSL ℝ (f t)).comp (incl1CLM.comp Q.Vt1h.subtypeL))

theorem inner_srcQ [CompleteSpace Q.Vt1h] (f : ℝ → Wv W1) (t : ℝ) (v : Q.Vt1h) :
    ⟪srcQ Q f t, v⟫ = ⟪f t, incl1 (v : Wv U1)⟫ := by
  rw [srcQ, InnerProductSpace.toDual_symm_apply]
  rfl

theorem srcQ_sub [CompleteSpace Q.Vt1h] (f g : ℝ → Wv W1) (t : ℝ) :
    srcQ Q (f - g) t = srcQ Q f t - srcQ Q g t := by
  simp only [srcQ, Pi.sub_apply, map_sub, ContinuousLinearMap.sub_comp]

theorem norm_srcQ_le [CompleteSpace Q.Vt1h] (f : ℝ → Wv W1) (t : ℝ) :
    ‖srcQ Q f t‖ ≤ ‖f t‖ := by
  have h := inner_srcQ Q f t (srcQ Q f t)
  rw [real_inner_self_eq_norm_sq] at h
  have h2 : ⟪f t, incl1 ((srcQ Q f t : Q.Vt1h) : Wv U1)⟫ ≤ ‖f t‖ * ‖srcQ Q f t‖ := by
    refine (real_inner_le_norm _ _).trans (le_of_eq ?_)
    rw [norm_incl1]; rfl
  rcases eq_or_lt_of_le (norm_nonneg (srcQ Q f t)) with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  · have h3 : ‖srcQ Q f t‖ * ‖srcQ Q f t‖ ≤ ‖f t‖ * ‖srcQ Q f t‖ := by
      rw [← sq, h]; exact h2
    exact le_of_mul_le_mul_right h3 h0

/-- The energy embedding of `H̊Λ⁰ × H̊Λ¹(Q)³ × L²Λ² × (L²Λ²)³` into the energy space. -/
def embU : (U0 × Wv U1 × W2 × Wv W2) →L[ℝ] Feec.BGG.EnergySpace W0 (Wv W1) W2 (Wv W2) :=
  (Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2)).comp
    (D0.domain.subtypeL.prodMap (incl1CLM.prodMap (ContinuousLinearMap.id ℝ (W2 × Wv W2))))

theorem embU_apply (x : U0 × Wv U1 × W2 × Wv W2) :
    embU x = Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2) ((x.1 : W0), incl1 x.2.1, x.2.2.1, x.2.2.2) :=
  rfl

theorem isEnergyEmbedding_embU : Feec.BGG.Discrete.IsEnergyEmbedding embU := fun a b => by
  rw [embU_apply, embU_apply, Feec.BGG.isEnergyEmbedding_energyEmb, ← inner_wv_U1]
  rfl

/-- The energy embedding of the discrete states of `Q`. -/
def embQ : (Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) →L[ℝ] Feec.BGG.EnergySpace W0 (Wv W1) W2 (Wv W2) :=
  embU.comp (Q.V0h.subtypeL.prodMap (Q.Vt1h.subtypeL.prodMap (Q.W2h.subtypeL.prodMap
    Q.Wt2h.subtypeL)))

theorem isEnergyEmbedding_embQ : Feec.BGG.Discrete.IsEnergyEmbedding (embQ Q) := fun a b =>
  isEnergyEmbedding_embU ((a.1 : U0), (a.2.1 : Wv U1), (a.2.2.1 : W2), (a.2.2.2 : Wv W2))
    ((b.1 : U0), (b.2.1 : Wv U1), (b.2.2.1 : W2), (b.2.2.2 : Wv W2))

/-- The energy vector `(σₕ, uₕ, Mₕ, ρₕ)(t)` of a discrete solution, in the energy space. -/
def dvec {T : ℝ} {g : ℝ → Q.Vt1h} (sh : Feec.BGG.DiscreteSolution Q.toSegmentH T g) (t : ℝ) :
    Feec.BGG.EnergySpace W0 (Wv W1) W2 (Wv W2) :=
  embQ Q (sh.σ t, sh.u t, sh.M t, sh.ρ t)

theorem norm_dvec_sub {T : ℝ} {g₁ g₂ : ℝ → Q.Vt1h}
    (s₁ : Feec.BGG.DiscreteSolution Q.toSegmentH T g₁)
    (s₂ : Feec.BGG.DiscreteSolution Q.toSegmentH T g₂) (t : ℝ) :
    ‖dvec Q s₁ t - dvec Q s₂ t‖ = √(‖(s₁.sub' s₂).σ t‖ ^ 2 + ‖(s₁.sub' s₂).u t‖ ^ 2 +
      ‖(s₁.sub' s₂).M t‖ ^ 2 + ‖(s₁.sub' s₂).ρ t‖ ^ 2) :=
  Feec.BGG.Discrete.norm_sub_of_isEnergyEmbedding (isEnergyEmbedding_embQ Q) _ _

theorem norm_dvec_sub_le {T : ℝ} {g₁ g₂ : ℝ → Q.Vt1h}
    (s₁ : Feec.BGG.DiscreteSolution Q.toSegmentH T g₁)
    (s₂ : Feec.BGG.DiscreteSolution Q.toSegmentH T g₂)
    (hg : ContinuousOn (g₁ - g₂) (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖dvec Q s₁ t - dvec Q s₂ t‖ ≤ ‖dvec Q s₁ 0 - dvec Q s₂ 0‖ +
      ∫ r in (0:ℝ)..t, ‖g₁ r - g₂ r‖ := by
  have h1 := norm_dvec_sub Q s₁ s₂ t
  have h2 := norm_dvec_sub Q s₁ s₂ 0
  have h3 : √(‖(s₁.sub' s₂).σ t‖ ^ 2 + ‖(s₁.sub' s₂).u t‖ ^ 2 + ‖(s₁.sub' s₂).M t‖ ^ 2 +
      ‖(s₁.sub' s₂).ρ t‖ ^ 2) ≤ √(‖(s₁.sub' s₂).σ 0‖ ^ 2 + ‖(s₁.sub' s₂).u 0‖ ^ 2 +
      ‖(s₁.sub' s₂).M 0‖ ^ 2 + ‖(s₁.sub' s₂).ρ 0‖ ^ 2) + ∫ r in (0:ℝ)..t, ‖g₁ r - g₂ r‖ :=
    (s₁.sub' s₂).sqrt_energy_le hg t ht
  linarith

theorem exactWave_toSolution_vec' {T : ℝ} {f : ℝ → Wv W1}
    (s : Feec.BGG.ExactWave bggSegment T (srcFun f)) (t : ℝ) :
    (exactWave_toSolution s).vec t = embU (s.σ t, s.u t, s.M t, s.ρ t) :=
  rfl

theorem norm_vec_sub_dvec {T : ℝ} {f : ℝ → Wv W1} {g : ℝ → Q.Vt1h}
    (s : Feec.BGG.ExactWave bggSegment T (srcFun f))
    (sh : Feec.BGG.DiscreteSolution Q.toSegmentH T g) (t : ℝ) :
    ‖(exactWave_toSolution s).vec t - dvec Q sh t‖ = √(‖s.σ t - sh.σ t‖ ^ 2 +
      ‖s.u t - sh.u t‖ ^ 2 + ‖s.M t - sh.M t‖ ^ 2 + ‖s.ρ t - sh.ρ t‖ ^ 2) :=
  (congrArg (fun v => ‖v - dvec Q sh t‖) (exactWave_toSolution_vec' s t)).trans
    (Feec.BGG.Discrete.norm_sub_of_isEnergyEmbedding isEnergyEmbedding_embU
      (s.σ t, s.u t, s.M t, s.ρ t)
      ((sh.σ t : U0), (sh.u t : Wv U1), (sh.M t : W2), (sh.ρ t : Wv W2)))

end Lax

/-! ### The cube: convergence of (6.5) for rate-approximable data -/

section CubeLax

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

/-- Classical solutions of (6.2) whose states and time derivatives are `C²` with vanishing
tangential traces, and whose multipliers and their derivatives are bounded, all with bound `L`. -/
def IsRateClass {T : ℝ} {f : ℝ → Wv W1} (s : Feec.BGG.ExactWave bggSegment T (srcFun f))
    (L : ℝ) : Prop :=
  0 ≤ L ∧ (∀ t ∈ Icc 0 T, IsSmoothStateTr L (s.σ t) (s.φ t) (s.u t) (s.M t) (s.ρ t) ∧
      IsSmoothStateTr L (s.σ' t) (s.φ' t) (s.u' t) (s.M' t) (s.ρ' t)) ∧
    ∀ t ∈ Icc 0 T, ∀ μ : U1, |s.ℓ t μ| ≤ L * ‖μ‖ ∧ |s.ℓ' t μ| ≤ L * ‖μ‖

/-- Approximability of a solution of (6.1) by the rate class, in energy and in the source. -/
def IsRateApproximable {T : ℝ} {fw : ℝ → Wv W1} (w : cubeWaveData.Solution T fw) : Prop :=
  ∀ ε > 0, ∃ (f : ℝ → Wv W1) (_ : ContinuousOn f (Icc 0 T))
    (s : Feec.BGG.ExactWave bggSegment T (srcFun f)) (L : ℝ), IsRateClass s L ∧
      ‖w.vec 0 - (exactWave_toSolution s).vec 0‖ + ∫ r in (0:ℝ)..T, ‖fw r - f r‖ < ε

set_option maxHeartbeats 4000000 in
/-- If `w` solves (6.1) with a continuous source `fw` and is approximable by the rate class, the
solutions of (6.5) with source `P fw` and initial states `→ w(0)` converge to `w` uniformly. -/
theorem tendsto_of_isRateApproximable {T : ℝ} (hT0 : 0 < T) {fw : ℝ → Wv W1}
    (hfw : ContinuousOn fw (Icc 0 T)) (w : cubeWaveData.Solution T fw)
    (hw : IsRateApproximable w)
    (sh : ∀ N, Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N fw))
    (h0 : Tendsto (fun N => ‖w.vec 0 - dvec (cubeFEM hT hB N) (sh N) 0‖) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ t ∈ Icc 0 T, ‖w.vec t - dvec (cubeFEM hT hB N) (sh N) t‖ < ε := by
  obtain ⟨K, hK0, hK⟩ := cubeWave_rate_tr' hT hB
  refine lax_abstract tendsto_meshSize w.vec (fun N => dvec (cubeFEM hT hB N) (sh N)) h0
    hT0.le fun δ hδ => ?_
  obtain ⟨f, hf, s, L, hs, hsw⟩ := hw δ hδ
  have hrate := fun N => hK N hT0 hf s hs.1 hs.2.1 hs.2.2
  choose sh' _ hsh' using hrate
  have hfc : ContinuousOn (fun r => ‖fw r - f r‖) (Icc 0 T) := (hfw.sub hf).norm
  have hKL : 0 ≤ K * L := mul_nonneg hK0 hs.1
  refine ⟨(exactWave_toSolution s).vec, fun N => dvec (cubeFEM hT hB N) (sh' N),
    ‖w.vec 0 - (exactWave_toSolution s).vec 0‖, ∫ r in (0:ℝ)..T, ‖fw r - f r‖, K * L * (1 + T),
    hsw, intervalIntegral.integral_nonneg hT0.le fun _ _ => norm_nonneg _, fun t ht => ?_,
    le_rfl, fun N t ht => ?_, fun N t ht => ?_⟩
  · exact (w.norm_vec_sub_le _ (hfw.sub hf) t ht).trans
      (add_le_add le_rfl (integral_le_integral_T hfc (fun _ => norm_nonneg _) ht))
  · have h1 := hsh' N t ht
    have h2 := norm_vec_sub_dvec (cubeFEM hT hB N) s (sh' N) t
    have hh := (meshSize_pos N).le
    have h3 : K * L * (1 + t) * meshSize N ≤ K * L * (1 + T) * meshSize N :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hKL) hh
    linarith
  · have hgc : ContinuousOn (cubeSource hT hB N f - cubeSource hT hB N fw) (Icc 0 T) :=
      (continuousOn_cubeSource hT hB N hf).sub (continuousOn_cubeSource hT hB N hfw)
    have hst := norm_dvec_sub_le (cubeFEM hT hB N) (sh' N) (sh N) hgc ht
    have hpt : ∀ r ∈ Icc 0 T, ‖cubeSource hT hB N f r - cubeSource hT hB N fw r‖ ≤
        ‖fw r - f r‖ := fun r _ => by
      have e : cubeSource hT hB N f r - cubeSource hT hB N fw r =
          srcQ (cubeFEM hT hB N) (f - fw) r := (srcQ_sub (cubeFEM hT hB N) f fw r).symm
      rw [e, norm_sub_rev]
      exact norm_srcQ_le (cubeFEM hT hB N) (f - fw) r
    have hint : ∫ r in (0:ℝ)..t, ‖cubeSource hT hB N f r - cubeSource hT hB N fw r‖ ≤
        ∫ r in (0:ℝ)..T, ‖fw r - f r‖ :=
      (integral_mono_Icc hgc.norm hfc hpt ht).trans
        (integral_le_integral_T hfc (fun _ => norm_nonneg _) ht)
    linarith

end CubeLax

/-! ### The TSD datum that leaves TSD -/

section Beta

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

open Feec.Counterexamples.BoundedBGG Feec.Counterexamples.BoundedDomainTSD

theorem nonempty_cubeDomain : (cubeDomain 3).Nonempty :=
  ⟨fun _ => 1 / 4, fun _ _ => ⟨by norm_num, by norm_num⟩⟩

/-- The TSD datum `(σ, u, (M, B))(0) = (0, 0, (0, β))`, `β = x₃ (e₁ e₂ᵀ + e₂ e₁ᵀ)`, on `Q`. -/
abbrev betaDatum : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3))) :=
  ShortHilbertComplex.mk3 0 0 (betaPair (isOpen_cubeDomain 3) (isBounded_cubeDomain 3) 0)

/-- The magnetic rows `ρ(0)` of the datum in the forms model: the rows of `β` as `2`-forms. -/
def rhoBeta : Wv W2 := rows2Equiv.symm (betaL2 (isOpen_cubeDomain 3) (isBounded_cubeDomain 3))

theorem comp0_totalE_symm (y : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))) :
    comp0 (totalE.symm y) = zeroEquiv.symm (y 0) := rfl

theorem comp1_totalE_symm (y : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))) :
    comp1 (totalE.symm y) = rowsEquiv.symm (y 1) := rfl

theorem compML_totalE_symm (y : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))) :
    compML (totalE.symm y) = starEquiv.symm (WithLp.ofLp (y 2 : W2B ℝ (cubeDomain 3))).1 := rfl

theorem compρL_totalE_symm (y : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3))
    (L2F ℝ (cubeDomain 3) Ix) (W2B ℝ (cubeDomain 3)))) :
    compρL (totalE.symm y) = rows2Equiv.symm (WithLp.ofLp (y 2 : W2B ℝ (cubeDomain 3))).2 := rfl

theorem norm_snd_le_energyEmb {V0 Vt1 W2 Wt2 : Type*}
    [NormedAddCommGroup V0] [InnerProductSpace ℝ V0] [NormedAddCommGroup Vt1]
    [InnerProductSpace ℝ Vt1] [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
    [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2] (a b : V0 × Vt1 × W2 × Wt2) :
    ‖a.2.1 - b.2.1‖ ≤
      ‖Feec.BGG.energyEmb V0 Vt1 W2 Wt2 a - Feec.BGG.energyEmb V0 Vt1 W2 Wt2 b‖ := by
  rw [Feec.BGG.Discrete.norm_sub_of_isEnergyEmbedding Feec.BGG.isEnergyEmbedding_energyEmb]
  exact Real.le_sqrt_of_sq_le (by
    nlinarith [sq_nonneg ‖a.1 - b.1‖, sq_nonneg ‖a.2.2.1 - b.2.2.1‖,
      sq_nonneg ‖a.2.2.2 - b.2.2.2‖])

theorem norm_last_le_energyEmb {V0 Vt1 W2 Wt2 : Type*}
    [NormedAddCommGroup V0] [InnerProductSpace ℝ V0] [NormedAddCommGroup Vt1]
    [InnerProductSpace ℝ Vt1] [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
    [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2] (a b : V0 × Vt1 × W2 × Wt2) :
    ‖a.2.2.2 - b.2.2.2‖ ≤
      ‖Feec.BGG.energyEmb V0 Vt1 W2 Wt2 a - Feec.BGG.energyEmb V0 Vt1 W2 Wt2 b‖ := by
  rw [Feec.BGG.Discrete.norm_sub_of_isEnergyEmbedding Feec.BGG.isEnergyEmbedding_energyEmb]
  exact Real.le_sqrt_of_sq_le (by
    nlinarith [sq_nonneg ‖a.1 - b.1‖, sq_nonneg ‖a.2.1 - b.2.1‖,
      sq_nonneg ‖a.2.2.1 - b.2.2.1‖])

theorem dvec_eq (Q : Feec.BGG.Discrete bggSegment) {T : ℝ} {g : ℝ → Q.Vt1h}
    (sh : Feec.BGG.DiscreteSolution Q.toSegmentH T g) (t : ℝ) :
    dvec Q sh t = Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2)
      ((((sh.σ t : Q.V0h) : U0) : W0), incl1 ((sh.u t : Q.Vt1h) : Wv U1),
        ((sh.M t : Q.W2h) : W2), ((sh.ρ t : Q.Wt2h) : Wv W2)) := rfl

theorem exists_betaSolution {T : ℝ} (hT0 : 0 < T) :
    ∃ U : ℝ → PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix)
        (W2B ℝ (cubeDomain 3))),
      U 0 = betaDatum ∧ Evolution.IsStrongSolution matrixComplex.wave (Icc 0 T) 0 U ∧
      (∀ V, V 0 = betaDatum → Evolution.IsStrongSolution matrixComplex.wave (Icc 0 T) 0 V →
        EqOn V U (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, (U t 0 : L2 ℝ (cubeDomain 3)) = 0) ∧
      (∃ t ∈ Icc 0 T, (U t 1 : L2F ℝ (cubeDomain 3) Ix) ∉ tsd (cubeDomain 3)) ∧
      ∃ t ∈ Icc 0 T, (WithLp.ofLp (U t 2 : W2B ℝ (cubeDomain 3))).2 ∉ symSub ℝ (cubeDomain 3) :=
  (bggComplex_verdict (isOpen_cubeDomain 3) (isBounded_cubeDomain 3) nonempty_cubeDomain).2.2 T
    hT0

theorem isStrongSolution_forms {T : ℝ}
    {U : ℝ → PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix)
      (W2B ℝ (cubeDomain 3)))}
    (hU : Evolution.IsStrongSolution matrixComplex.wave (Icc 0 T) 0 U) :
    Evolution.IsStrongSolution formsShort.wave (Icc 0 T) 0 fun t => totalE.symm (U t) := by
  refine isStrongSolution_iff.2 (hU.congr (fun t _ => (totalE.apply_symm_apply _).symm)
    (fun t _ => ?_))
  change (0 : PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix)
    (W2B ℝ (cubeDomain 3)))) = totalE 0
  exact totalE.toLinearEquiv.map_zero.symm

theorem solutionOfStrong_vec_zero {T : ℝ} (hT0 : 0 < T)
    {U : ℝ → PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix)
      (W2B ℝ (cubeDomain 3)))}
    (hU : Evolution.IsStrongSolution matrixComplex.wave (Icc 0 T) 0 U) (hU0 : U 0 = betaDatum) :
    (solutionOfStrong (isStrongSolution_forms hU)).vec 0 =
      Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2) (0, 0, 0, rhoBeta) := by
  rw [solutionOfStrong_vec (isStrongSolution_forms hU) ⟨le_rfl, hT0.le⟩]
  simp only [comp0_totalE_symm, comp1_totalE_symm, compML_totalE_symm, compρL_totalE_symm, hU0]
  have e0 : ((zeroEquiv.symm (betaDatum 0) : bggHilb.Γbar) : W0) = 0 := by
    rw [ShortHilbertComplex.mk3_apply_zero, map_zero]; rfl
  have e1 : rowsEquiv.symm (betaDatum 1) = 0 := by
    rw [ShortHilbertComplex.mk3_apply_one, map_zero]
  have e2 : starEquiv.symm (WithLp.ofLp (betaDatum 2 : W2B ℝ (cubeDomain 3))).1 = 0 := by
    rw [ShortHilbertComplex.mk3_apply_two]
    exact map_zero _
  rw [e0, e1, e2, neg_zero]
  rfl

section BetaDiscrete

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

theorem Wt2h_eq (N : ℕ) : (cubeFEM hT hB N).Wt2h = tsub ((polyMin 3 PolySeq.lagrangeP2 N).V 2) :=
  rfl

theorem tendsto_infDist_rhoBeta :
    Tendsto (fun N => Metric.infDist rhoBeta ((cubeFEM hT hB N).Wt2h : Set (Wv W2))) atTop
      (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun N =>
    ha.trans_le Metric.infDist_nonneg, fun ε hε => ?_⟩
  have h2 : 0 < ε / 2 := half_pos hε
  have hrows : ∀ᶠ N in atTop, ∀ a : Fin 3, ∃ v ∈ (polyMin 3 PolySeq.lagrangeP2 N).V 2,
      ‖rhoBeta a - v‖ < ε / 2 :=
    Filter.eventually_all.2 fun a => eventually_exists_polyMin_lt PolySeq.lagrangeP2 2 _ h2
  filter_upwards [hrows] with N hN
  choose v hv hvε using hN
  have hx : (WithLp.toLp 2 v : Wv W2) ∈ (cubeFEM hT hB N).Wt2h := by
    rw [Wt2h_eq]; exact fun a => hv a
  refine (Metric.infDist_le_dist_of_mem hx).trans_lt ?_
  rw [dist_eq_norm]
  have hsq : ‖rhoBeta - WithLp.toLp 2 v‖ ^ 2 < ε ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
    have e : ∀ a, (rhoBeta - WithLp.toLp 2 v) a = rhoBeta a - v a := fun a => rfl
    rw [e, e, e]
    have := hvε 0; have := hvε 1; have := hvε 2
    nlinarith [norm_nonneg (rhoBeta 0 - v 0), norm_nonneg (rhoBeta 1 - v 1),
      norm_nonneg (rhoBeta 2 - v 2)]
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).1 hsq

/-- The discrete magnetic datum: the `L²` projection of `ρ(0)` onto `P₁Λ̊² ⊗ ℝ³`. -/
def rhoBetaH (N : ℕ) : (cubeFEM hT hB N).Wt2h :=
  haveI : CompleteSpace (cubeFEM hT hB N).Wt2h := FiniteDimensional.complete ℝ _
  ⟨(cubeFEM hT hB N).Wt2h.starProjection rhoBeta, Submodule.starProjection_apply_mem _ _⟩

theorem norm_rhoBeta_sub_rhoBetaH (N : ℕ) :
    ‖rhoBeta - ((rhoBetaH hT hB N : (cubeFEM hT hB N).Wt2h) : Wv W2)‖ =
      Metric.infDist rhoBeta ((cubeFEM hT hB N).Wt2h : Set (Wv W2)) := by
  have : CompleteSpace (cubeFEM hT hB N).Wt2h := FiniteDimensional.complete ℝ _
  rw [← dist_eq_norm]
  exact Submodule.dist_starProjection_eq_infDist _ _

theorem exists_betaDiscrete {T : ℝ} (hT0 : 0 < T) (N : ℕ) :
    ∃ s : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N 0),
      s.σ 0 = 0 ∧ s.u 0 = 0 ∧ s.M 0 = 0 ∧ s.ρ 0 = rhoBetaH hT hB N :=
  (cubeWave_exists_iff_compatible_u hT hB N hT0
    (continuousOn_cubeSource hT hB N (continuousOn_const (c := (0 : Wv W1)))) 0 0 0
    (rhoBetaH hT hB N)).2 fun _ _ => inner_zero_left _

theorem norm_symm_sub {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (e : E ≃ₗᵢ[ℝ] F) (x : F) (y : E) :
    ‖e.symm x - y‖ = ‖x - e y‖ := by
  rw [← e.norm_map, LinearIsometryEquiv.map_sub, LinearIsometryEquiv.apply_symm_apply]

section Main

variable {T : ℝ} (hT0 : 0 < T)

/-- The matrix-model solution of the TSD datum on `[0,T]` (`exists_betaSolution`). -/
def betaU : ℝ → PiLp 2 (ShortHilbertComplex.W3 (L2 ℝ (cubeDomain 3)) (L2F ℝ (cubeDomain 3) Ix)
    (W2B ℝ (cubeDomain 3))) :=
  (exists_betaSolution hT0).choose

theorem betaU_spec :
    betaU hT0 0 = betaDatum ∧
      Evolution.IsStrongSolution matrixComplex.wave (Icc 0 T) 0 (betaU hT0) ∧
      (∀ V, V 0 = betaDatum → Evolution.IsStrongSolution matrixComplex.wave (Icc 0 T) 0 V →
        EqOn V (betaU hT0) (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, (betaU hT0 t 0 : L2 ℝ (cubeDomain 3)) = 0) ∧
      (∃ t ∈ Icc 0 T, (betaU hT0 t 1 : L2F ℝ (cubeDomain 3) Ix) ∉ tsd (cubeDomain 3)) ∧
      ∃ t ∈ Icc 0 T, (WithLp.ofLp (betaU hT0 t 2 : W2B ℝ (cubeDomain 3))).2 ∉
        symSub ℝ (cubeDomain 3) :=
  (exists_betaSolution hT0).choose_spec

/-- The electric field `E(t) ∈ L²(Q; ℝ³ˣ³)` of the matrix-model solution. -/
def betaE (t : ℝ) : L2F ℝ (cubeDomain 3) Ix := betaU hT0 t 1

/-- The magnetic field `B(t) ∈ L²(Q; ℝ³ˣ³)` of the matrix-model solution. -/
def betaB (t : ℝ) : L2F ℝ (cubeDomain 3) Ix :=
  (WithLp.ofLp (betaU hT0 t 2 : W2B ℝ (cubeDomain 3))).2

/-- The TSD solution in the forms model, as a solution of (6.1) of `cubeWaveData`. -/
def betaW : cubeWaveData.Solution T 0 :=
  solutionOfStrong (isStrongSolution_forms (betaU_spec hT0).2.1)

theorem betaW_vec {t : ℝ} (ht : t ∈ Icc 0 T) :
    (betaW hT0).vec t = Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2)
      (-((zeroEquiv.symm (betaU hT0 t 0) : bggHilb.Γbar) : W0), rowsEquiv.symm (betaU hT0 t 1),
        starEquiv.symm (WithLp.ofLp (betaU hT0 t 2 : W2B ℝ (cubeDomain 3))).1,
        rows2Equiv.symm (WithLp.ofLp (betaU hT0 t 2 : W2B ℝ (cubeDomain 3))).2) :=
  solutionOfStrong_vec (isStrongSolution_forms (betaU_spec hT0).2.1) ht

theorem betaW_vec_zero :
    (betaW hT0).vec 0 = Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2) (0, 0, 0, rhoBeta) :=
  solutionOfStrong_vec_zero hT0 (betaU_spec hT0).2.1 (betaU_spec hT0).1

set_option maxHeartbeats 2000000 in
theorem norm_rowsEquiv_sub_le {t : ℝ} (ht : t ∈ Icc 0 T) {N : ℕ} {g : ℝ → (cubeFEM hT hB N).Vt1h}
    (sh : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T g) :
    ‖betaE hT0 t - rowsEquiv (incl1 ((sh.u t : _) : Wv U1))‖ ≤
      ‖(betaW hT0).vec t - dvec (cubeFEM hT hB N) sh t‖ := by
  have h := norm_snd_le_energyEmb (V0 := W0) (Vt1 := Wv W1) (W2 := W2) (Wt2 := Wv W2)
    (-((zeroEquiv.symm (betaU hT0 t 0) : bggHilb.Γbar) : W0), rowsEquiv.symm (betaE hT0 t),
      starEquiv.symm (WithLp.ofLp (betaU hT0 t 2 : W2B ℝ (cubeDomain 3))).1,
      rows2Equiv.symm (betaB hT0 t))
    ((((sh.σ t : (cubeFEM hT hB N).V0h) : U0) : W0),
      incl1 ((sh.u t : (cubeFEM hT hB N).Vt1h) : Wv U1),
      ((sh.M t : (cubeFEM hT hB N).W2h) : W2), ((sh.ρ t : (cubeFEM hT hB N).Wt2h) : Wv W2))
  have e1 := betaW_vec hT0 ht
  have e2 := dvec_eq (cubeFEM hT hB N) sh t
  have e3 := norm_symm_sub rowsEquiv (betaE hT0 t)
    (incl1 ((sh.u t : (cubeFEM hT hB N).Vt1h) : Wv U1))
  exact e3.symm.trans_le (h.trans_eq (congrArg₂ (fun x y => ‖x - y‖) e1.symm e2.symm))

set_option maxHeartbeats 2000000 in
theorem norm_rows2Equiv_sub_le {t : ℝ} (ht : t ∈ Icc 0 T) {N : ℕ}
    {g : ℝ → (cubeFEM hT hB N).Vt1h} (sh : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T g) :
    ‖betaB hT0 t - rows2Equiv ((sh.ρ t : _) : Wv W2)‖ ≤
      ‖(betaW hT0).vec t - dvec (cubeFEM hT hB N) sh t‖ := by
  have h := norm_last_le_energyEmb (V0 := W0) (Vt1 := Wv W1) (W2 := W2) (Wt2 := Wv W2)
    (-((zeroEquiv.symm (betaU hT0 t 0) : bggHilb.Γbar) : W0), rowsEquiv.symm (betaE hT0 t),
      starEquiv.symm (WithLp.ofLp (betaU hT0 t 2 : W2B ℝ (cubeDomain 3))).1,
      rows2Equiv.symm (betaB hT0 t))
    ((((sh.σ t : (cubeFEM hT hB N).V0h) : U0) : W0),
      incl1 ((sh.u t : (cubeFEM hT hB N).Vt1h) : Wv U1),
      ((sh.M t : (cubeFEM hT hB N).W2h) : W2), ((sh.ρ t : (cubeFEM hT hB N).Wt2h) : Wv W2))
  have e1 := betaW_vec hT0 ht
  have e2 := dvec_eq (cubeFEM hT hB N) sh t
  have e3 := norm_symm_sub rows2Equiv (betaB hT0 t)
    ((sh.ρ t : (cubeFEM hT hB N).Wt2h) : Wv W2)
  exact e3.symm.trans_le (h.trans_eq (congrArg₂ (fun x y => ‖x - y‖) e1.symm e2.symm))

theorem eventually_not_mem_of_tendsto {E : Type*} [SeminormedAddCommGroup E] {S : Set E}
    (hS : IsClosed S) {x : E} (hx : x ∉ S) {y : ℕ → E}
    (hy : ∀ ε > 0, ∀ᶠ N in atTop, ‖x - y N‖ < ε) : ∀ᶠ N in atTop, y N ∉ S := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hS.isOpen_compl x hx
  filter_upwards [hy r hr] with N hN
  exact hball (by rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]; exact hN)

set_option maxHeartbeats 4000000 in
/-- The solution of the TSD datum `(0, 0, (0, β))` leaves TSD; if it is approximable by the rate
class, solutions of (6.5) with initial states converging to it converge, and their fields leave
TSD. -/
theorem waveFEM_converges_to_non_tsd_of_isRateApproximable
    {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
    (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
    (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C) {T : ℝ} (hT0 : 0 < T) :
    (betaU hT0 0 = betaDatum ∧
      Evolution.IsStrongSolution matrixComplex.wave (Icc 0 T) 0 (betaU hT0) ∧
      (∀ V, V 0 = betaDatum → Evolution.IsStrongSolution matrixComplex.wave (Icc 0 T) 0 V →
        EqOn V (betaU hT0) (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, (betaU hT0 t 0 : L2 ℝ (cubeDomain 3)) = 0) ∧
      (∃ t ∈ Icc 0 T, betaE hT0 t ∉ tsd (cubeDomain 3)) ∧
      ∃ t ∈ Icc 0 T, betaB hT0 t ∉ symSub ℝ (cubeDomain 3)) ∧
    (betaW hT0).vec 0 = Feec.BGG.energyEmb W0 (Wv W1) W2 (Wv W2) (0, 0, 0, rhoBeta) ∧
    (∃ sh : ∀ N, Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N 0),
      (∀ N, (sh N).σ 0 = 0 ∧ (sh N).u 0 = 0 ∧ (sh N).M 0 = 0 ∧ (sh N).ρ 0 = rhoBetaH hT hB N) ∧
      Tendsto (fun N => ‖(betaW hT0).vec 0 - dvec (cubeFEM hT hB N) (sh N) 0‖) atTop (𝓝 0)) ∧
    (IsRateApproximable (betaW hT0) →
      ∀ sh : ∀ N, Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N 0),
        Tendsto (fun N => ‖(betaW hT0).vec 0 - dvec (cubeFEM hT hB N) (sh N) 0‖) atTop (𝓝 0) →
        (∀ ε > 0, ∀ᶠ N in atTop, ∀ t ∈ Icc 0 T,
          ‖(betaW hT0).vec t - dvec (cubeFEM hT hB N) (sh N) t‖ < ε) ∧
        (∀ ε > 0, ∀ᶠ N in atTop, ∀ t ∈ Icc 0 T,
          ‖betaE hT0 t - rowsEquiv (incl1 (((sh N).u t : (cubeFEM hT hB N).Vt1h) : Wv U1))‖ < ε ∧
          ‖betaB hT0 t - rows2Equiv (((sh N).ρ t : (cubeFEM hT hB N).Wt2h) : Wv W2)‖ < ε) ∧
        (∃ t ∈ Icc 0 T, ∀ᶠ N in atTop,
          rowsEquiv (incl1 (((sh N).u t : (cubeFEM hT hB N).Vt1h) : Wv U1)) ∉
            tsd (cubeDomain 3)) ∧
        ∃ t ∈ Icc 0 T, ∀ᶠ N in atTop,
          rows2Equiv (((sh N).ρ t : (cubeFEM hT hB N).Wt2h) : Wv W2) ∉
            symSub ℝ (cubeDomain 3)) := by
  obtain ⟨h0, hU, huniq, hσ, ⟨t₁, ht₁, hE⟩, ⟨t₂, ht₂, hBt⟩⟩ := betaU_spec hT0
  refine ⟨⟨h0, hU, huniq, hσ, ⟨t₁, ht₁, hE⟩, ⟨t₂, ht₂, hBt⟩⟩, betaW_vec_zero hT0, ?_, ?_⟩
  · choose sh hsh using fun N => exists_betaDiscrete hT hB hT0 N
    refine ⟨sh, hsh, ?_⟩
    have e : ∀ N, ‖(betaW hT0).vec 0 - dvec (cubeFEM hT hB N) (sh N) 0‖ =
        Metric.infDist rhoBeta ((cubeFEM hT hB N).Wt2h : Set (Wv W2)) := fun N => by
      rw [betaW_vec_zero, dvec_eq, (hsh N).1, (hsh N).2.1, (hsh N).2.2.1, (hsh N).2.2.2,
        Feec.BGG.Discrete.norm_sub_of_isEnergyEmbedding Feec.BGG.isEnergyEmbedding_energyEmb]
      simp only [ZeroMemClass.coe_zero, map_zero, sub_self, norm_zero]
      rw [← norm_rhoBeta_sub_rhoBetaH hT hB N]
      simp
    simp_rw [e]
    exact tendsto_infDist_rhoBeta hT hB
  · intro hw sh hsh0
    have hconv := tendsto_of_isRateApproximable hT hB hT0 continuousOn_const (betaW hT0) hw sh
      hsh0
    have hEB : ∀ ε > 0, ∀ᶠ N in atTop, ∀ t ∈ Icc 0 T,
        ‖betaE hT0 t - rowsEquiv (incl1 (((sh N).u t : (cubeFEM hT hB N).Vt1h) : Wv U1))‖ < ε ∧
        ‖betaB hT0 t - rows2Equiv (((sh N).ρ t : (cubeFEM hT hB N).Wt2h) : Wv W2)‖ < ε :=
      fun ε hε => (hconv ε hε).mono fun N hN t ht =>
        ⟨(norm_rowsEquiv_sub_le hT hB hT0 ht (sh N)).trans_lt (hN t ht),
          (norm_rows2Equiv_sub_le hT hB hT0 ht (sh N)).trans_lt (hN t ht)⟩
    refine ⟨hconv, hEB, ⟨t₁, ht₁, ?_⟩, ⟨t₂, ht₂, ?_⟩⟩
    · exact eventually_not_mem_of_tendsto isClosed_tsd hE fun ε hε =>
        (hEB ε hε).mono fun N hN => (hN t₁ ht₁).1
    · exact eventually_not_mem_of_tendsto isClosed_symSub hBt fun ε hε =>
        (hEB ε hε).mono fun N hN => (hN t₂ ht₂).2

end Main

end BetaDiscrete

end Beta

section DomainData

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

end DomainData

/-! ### The TSD datum is not in the rate class -/

section NotRateClass

open Feec.Counterexamples.BoundedDomainTSD

theorem rhoBeta_zero_idx2_one :
    ((rhoBeta 0 (idx2 1) : L2 ℝ (cubeDomain 3)) : (Fin 3 → ℝ) → ℝ)
      =ᵐ[volume.restrict (cubeDomain 3)] fun y => -y 2 := by
  have e : rhoBeta 0 (idx2 1) = sgn2 1 •
      betaL2 (isOpen_cubeDomain 3) (isBounded_cubeDomain 3) (0, 1) := by
    simp [rhoBeta]
  rw [e]
  filter_upwards [Lp.coeFn_smul (sgn2 1) (betaL2 (isOpen_cubeDomain 3) (isBounded_cubeDomain 3)
      (0, 1)),
    MemLp.coeFn_toLp (memLp_of_continuous (isOpen_cubeDomain 3).measurableSet
      (isBounded_cubeDomain 3) (contDiff_betaField (0, 1)).continuous)] with y h1 h2
  rw [h1, Pi.smul_apply]
  change sgn2 1 • ((betaL2 (isOpen_cubeDomain 3) (isBounded_cubeDomain 3) (0, 1) :
    L2 ℝ (cubeDomain 3)) : (Fin 3 → ℝ) → ℝ) y = _
  rw [show ((betaL2 (isOpen_cubeDomain 3) (isBounded_cubeDomain 3) (0, 1) : L2 ℝ (cubeDomain 3)) :
    (Fin 3 → ℝ) → ℝ) y = betaField (0, 1) y from h2]
  simp [sgn2, betaField]

theorem not_isCsFormTr_rhoBeta (s : ℕ) (L : ℝ) : ¬ IsCsFormTr s 2 L (rhoBeta 0) := by
  rintro (hj | ⟨k, hk, w, hw, -, htan, -, he⟩)
  · norm_num at hj
  obtain rfl : k = 2 := by exact_mod_cast hk
  have hae := congrArg (fun z : W2 => (z (idx2 1) : (Fin 3 → ℝ) → ℝ)) he
  have h2 := coeFn_formL2 (isOpen_cubeDomain 3).measurableSet (isBounded_cubeDomain 3) 2
    ⟨w, hw.continuous⟩ (idx2 1)
  have hae' : (fun y : Fin 3 → ℝ => -y 2) =ᵐ[volume.restrict (cubeDomain 3)]
      fun y => w y (idx2 1).1 :=
    rhoBeta_zero_idx2_one.symm.trans ((Filter.EventuallyEq.of_eq hae).trans h2)
  have hc1 : Continuous fun y : Fin 3 → ℝ => -y 2 := (continuous_apply 2).neg
  have hc2 : Continuous fun y => w y (idx2 1).1 := (continuous_apply _).comp hw.continuous
  have heq := (MeasureTheory.Measure.eqOn_of_ae_eq hae' hc1.continuousOn hc2.continuousOn
    (by rw [(isOpen_cubeDomain 3).interior_eq]; exact subset_closure)).closure hc1 hc2
  set y₀ : Fin 3 → ℝ := ![1 / 4, 0, 1 / 4]
  have hy₀ : y₀ ∈ closure (cubeDomain 3) := mem_closure_cubeDomain.2 fun i => by
    fin_cases i <;> simp [y₀] <;> norm_num
  have h0 : w y₀ (idx2 1).1 = 0 := htan y₀ hy₀ 1 (idx2 1).1 (by decide) (Or.inl (by simp [y₀]))
  have h1 : -y₀ 2 = w y₀ (idx2 1).1 := heq hy₀
  rw [h0] at h1
  simp [y₀] at h1

/-- No classical solution of the rate class starts from the TSD datum: if `s.ρ(0) = ρ(0)`, then
`s` is in no `IsRateClass s L`. -/
theorem not_isRateClass_of_rho {T : ℝ} (hT0 : 0 ≤ T) {f : ℝ → Wv W1}
    (s : Feec.BGG.ExactWave bggSegment T (srcFun f)) (hρ : s.ρ 0 = rhoBeta) (L : ℝ) :
    ¬ IsRateClass s L := fun h => by
  have := ((h.2.1 0 ⟨le_rfl, hT0⟩).1.2.2.2.2 0)
  rw [hρ] at this
  exact not_isCsFormTr_rhoBeta 0 L this

end NotRateClass

end Feec.EinsteinBianchi.BoundedFailure
