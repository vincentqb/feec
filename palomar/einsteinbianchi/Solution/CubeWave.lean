module

public import Solution.CubeStatic
public import Feec.Physics.EinsteinBianchi.WaveFEMTangentialCube
public import Feec.Models.Cube.WeakSymmetrySobolevRate

/-!
# The wave problem on the cube

A classical solution of (6.2) of the challenge for `𝒟` is a `Feec.BGG.ExactWave` of
`bggSegment` with the source `srcFun f` (`toExactWave`), and the solutions of `Feec`'s
semi-discrete system for `cubeWave` are those of the challenge's (6.5) for `cubeQ`
(`isDiscreteWave_of`), and conversely on every `[0, T']`, `T' < T` (`toDiscreteSolution`). The
rate is `Feec.Models.Cube.WeakSymmetry.cubeWave_rate_tr'` and the uniqueness
`Feec.Models.Cube.WeakSymmetry.cubeWave_exists_unique`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.1 (6.2), §6.2 ((6.3), Prop 6.2), §6.3 ((6.5), Table 6.1)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set Filter Topology

@[expose] public noncomputable section

-- the instances of `Wv ↥U0` (vectors of a domain) need a deeper search here
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.HilbertComplex Feec.Models.Cube.FEM
  Feec.Models.Cube.WeakSymmetry

/-! ### Calculus through isometric embeddings -/

section Iso

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] (e : E →ₗ[ℝ] F) (he : ∀ x, ‖e x‖ = ‖x‖)
include he

theorem hasDerivWithinAt_of_isometry {f : ℝ → E} {f' : E} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt (fun r => e (f r)) (e f') s t) : HasDerivWithinAt f f' s t := by
  rw [hasDerivWithinAt_iff_isLittleO] at h ⊢
  have h2 := h.norm_left
  have e2 : (fun r => ‖e (f r) - e (f t) - (r - t) • e f'‖) =
      fun r => ‖f r - f t - (r - t) • f'‖ := funext fun r => by
    rw [← map_sub, ← map_smul, ← map_sub, he]
  rw [e2] at h2
  exact Asymptotics.isLittleO_norm_left.1 h2

theorem continuousOn_of_isometry {f : ℝ → E} {s : Set ℝ}
    (h : ContinuousOn (fun r => e (f r)) s) : ContinuousOn f s :=
  (AddMonoidHomClass.isometry_of_norm e he).isUniformInducing.isInducing.continuousOn_iff.2 h

end Iso

/-- Derivatives of maps into a subspace are those of the maps into the space. -/
theorem hasDerivWithinAt_subtype {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Submodule ℝ E) {f : ℝ → p} {f' : p} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt (fun r => (f r : E)) (f' : E) s t) : HasDerivWithinAt f f' s t :=
  hasDerivWithinAt_of_isometry p.subtype (fun _ => rfl) h

theorem continuousOn_subtype {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Submodule ℝ E) {f : ℝ → p} {s : Set ℝ} (h : ContinuousOn (fun r => (f r : E)) s) :
    ContinuousOn f s :=
  continuousOn_of_isometry p.subtype (fun _ => rfl) h

/-- The coercion of a differentiable map into a subspace. -/
theorem hasDerivWithinAt_coe {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : Submodule ℝ E) {f : ℝ → p} {f' : p} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt f f' s t) : HasDerivWithinAt (fun r => (f r : E)) (f' : E) s t :=
  p.subtypeL.hasFDerivAt.comp_hasDerivWithinAt t h

/-- Derivatives of vectors of elements of a subspace are those of the vectors in the space. -/
theorem hasDerivWithinAt_piSubtype {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Submodule ℝ E) {n : ℕ} {f : ℝ → PiLp 2 (fun _ : Fin n => p)}
    {f' : PiLp 2 (fun _ : Fin n => p)} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt (fun r => (WithLp.toLp 2 fun a => ((f r a : p) : E) :
      PiLp 2 fun _ : Fin n => E)) (WithLp.toLp 2 fun a => ((f' a : p) : E)) s t) :
    HasDerivWithinAt f f' s t := by
  let e : PiLp 2 (fun _ : Fin n => p) →ₗ[ℝ] PiLp 2 (fun _ : Fin n => E) :=
    (WithLp.linearEquiv 2 ℝ (Fin n → E)).symm.toLinearMap ∘ₗ
      (LinearMap.pi fun a => p.subtype ∘ₗ LinearMap.proj a) ∘ₗ
        (WithLp.linearEquiv 2 ℝ (Fin n → p)).toLinearMap
  have he : ∀ x, ‖e x‖ = ‖x‖ := fun x => by
    rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]; rfl
  exact hasDerivWithinAt_of_isometry e he (f := f) (f' := f') h

/-- The coercion of a differentiable vector of elements of a subspace. -/
theorem hasDerivWithinAt_piCoe {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Submodule ℝ E) {n : ℕ} {f : ℝ → PiLp 2 (fun _ : Fin n => p)}
    {f' : PiLp 2 (fun _ : Fin n => p)} {s : Set ℝ} {t : ℝ} (h : HasDerivWithinAt f f' s t) :
    HasDerivWithinAt (fun r => (WithLp.toLp 2 fun a => ((f r a : p) : E) :
      PiLp 2 fun _ : Fin n => E)) (WithLp.toLp 2 fun a => ((f' a : p) : E)) s t := by
  let e : PiLp 2 (fun _ : Fin n => p) →ₗ[ℝ] PiLp 2 (fun _ : Fin n => E) :=
    (WithLp.linearEquiv 2 ℝ (Fin n → E)).symm.toLinearMap ∘ₗ
      (LinearMap.pi fun a => p.subtype ∘ₗ LinearMap.proj a) ∘ₗ
        (WithLp.linearEquiv 2 ℝ (Fin n → p)).toLinearMap
  have he : ∀ x, ‖e x‖ ≤ 1 * ‖x‖ := fun x => by
    rw [one_mul, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]; rfl
  exact (e.mkContinuous 1 he).hasFDerivAt.comp_hasDerivWithinAt t h

/-- `d̃φ` as an element of `D(d̃¹)`. -/
def dφD (φ : 𝒟.dt0.domain) : 𝒟.dt1.domain := ⟨𝒟.dt0 φ, (isBGG_𝒟.2.1 φ).1⟩

/-! ### Classical solutions as `Feec`'s `ExactWave` -/

variable {T : ℝ} {f : ℝ → Wv W1} {σ σ' : ℝ → 𝒟.d0.domain}
  {φ φ' : ℝ → 𝒟.dt0.domain} {u u' : ℝ → 𝒟.dt1.domain} {M M' : ℝ → W2}
  {ρ ρ' : ℝ → Wv W2} {lam lam' : ℝ → W1}

/-- The multiplier functional `μ ↦ ⟪λ, μ⟫` on `H̊Λ¹(Q)`. -/
def multFun (l : W1) : U1 →ₗ[ℝ] ℝ := (innerSL ℝ l).toLinearMap ∘ₗ D1.domain.subtype

theorem multFun_apply (l : W1) (μ : U1) : multFun l μ = ⟪l, (μ : W1)⟫ := rfl

/-- **A classical solution of the challenge as an `ExactWave`.** -/
def toExactWave (hw : 𝒟.IsWaveSolution T f σ σ' φ φ' u u' M M' ρ ρ' lam lam') :
    @Feec.BGG.ExactWave U0 (Wv U1) W2 (Wv W2) U1 (Wv U0) _ _ _ _ _ _ _ _ _ _ _ _ bggSegment T
      (srcFun f) where
  σ := σ
  φ t := e0 (φ t)
  u t := e1 (u t)
  M := M
  ρ := ρ
  ℓ t := multFun (lam t)
  σ' := σ'
  φ' t := e0 (φ' t)
  u' t := e1 (u' t)
  M' := M'
  ρ' := ρ'
  ℓ' t := multFun (lam' t)
  cσ := hw.1.1
  cu := e1.continuous.comp_continuousOn hw.2.1.1
  cM := hw.2.2.2.2.1.1
  cρ := hw.2.2.2.2.2.1.1
  cdφ := e1.continuous.comp_continuousOn
    (continuousOn_subtype _ (f := fun s => dφD (φ s)) hw.2.2.1.1)
  cSu := (wsL2 (Ω := cubeDomain 3) 1).continuous.comp_continuousOn
    (continuous_subtype_val.comp_continuousOn hw.2.1.1)
  cdu := hw.2.2.2.1.1
  cℓ μ := (continuous_id.inner continuous_const).comp_continuousOn hw.2.2.2.2.2.2.1.1
  cσ' := hw.1.2.1
  cu' := e1.continuous.comp_continuousOn hw.2.1.2.1
  cM' := hw.2.2.2.2.1.2.1
  cρ' := hw.2.2.2.2.2.1.2.1
  cdφ' := e1.continuous.comp_continuousOn
    (continuousOn_subtype _ (f := fun s => dφD (φ' s)) hw.2.2.1.2.1)
  cSu' := (wsL2 (Ω := cubeDomain 3) 1).continuous.comp_continuousOn
    (continuous_subtype_val.comp_continuousOn hw.2.1.2.1)
  cdu' := hw.2.2.2.1.2.1
  cℓ' μ := (continuous_id.inner continuous_const).comp_continuousOn hw.2.2.2.2.2.2.1.2.1
  dσ t ht := hw.1.2.2 t ht
  du t ht := hasDerivWithinAt_piSubtype D1.domain (f := fun s => e1 (u s)) (f' := e1 (u' t))
    ((vecOpC (n := 3) D1).domain.subtypeL.hasFDerivAt.comp_hasDerivWithinAt t (hw.2.1.2.2 t ht))
  dM t ht := hw.2.2.2.2.1.2.2 t ht
  dρ t ht := hw.2.2.2.2.2.1.2.2 t ht
  ddφ t ht := hasDerivWithinAt_piSubtype D1.domain (f := fun s => bggSegment.dt0 (e0 (φ s)))
    (f' := bggSegment.dt0 (e0 (φ' t))) (hw.2.2.1.2.2 t ht)
  dSu t ht := by
    have h1 : HasDerivWithinAt (fun s => ((u s : 𝒟.dt1.domain) : Wv W1))
        ((u' t : 𝒟.dt1.domain) : Wv W1) (Ici t) t :=
      ((vecOpC (n := 3) D1).domain.subtypeL).hasFDerivAt.comp_hasDerivWithinAt t (hw.2.1.2.2 t ht)
    exact (wsL2 (Ω := cubeDomain 3) 1).hasFDerivAt.comp_hasDerivWithinAt t h1
  ddu t ht := hw.2.2.2.1.2.2 t ht
  dℓ t ht μ := by
    have := (hw.2.2.2.2.2.2.1.2.2 t ht).inner ℝ (hasDerivWithinAt_const t (Ici t) (μ : W1))
    simpa [multFun_apply] using this
  ea t ht τ ψ := by
    have := (hw.2.2.2.2.2.2.2.1 t ht).1 τ (e0.symm ψ)
    rw [multFun_apply]
    convert this using 2
    · rw [inner_wv_U1]; rfl
    · rfl
  eb t ht v := by
    have := (hw.2.2.2.2.2.2.2.1 t ht).2.1 (e1.symm v)
    rw [srcFun_apply]
    convert this using 3 <;> rfl
  ec t ht z := by
    rw [(hw.2.2.2.2.2.2.2.1 t ht).2.2.1, ← S1_e1, sub_self]
  ed t ht z := by
    rw [(hw.2.2.2.2.2.2.2.1 t ht).2.2.2, ← dt1_e1, sub_self]
  ee t ht := Subtype.ext ((hw.2.2.2.2.2.2.2.2 t ht).1.trans (S0_e0 _).symm)
  ee' t ht := Subtype.ext ((hw.2.2.2.2.2.2.2.2 t ht).2.trans (S0_e0 _).symm)

/-! ### `Feec`'s semi-discrete solutions are solutions of (6.5) of the challenge -/

section Disc

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C) (N : ℕ)

set_option maxHeartbeats 8000000 in
/-- **The rate of (6.5) on the cube** (`cubeWave_rate_tr'`, the solution of `Feec`'s (6.3) for
`cubeWave` being a solution of (6.5) for `cubeQ`). -/
theorem cube_wave_rate : ∃ K, ∀ N T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' L, 0 < T →
    ContinuousOn f (Icc 0 T) → 𝒟.IsWaveSolution T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' →
    (∀ t ∈ Icc 0 T, IsSmoothStateTr L (σ t) (e0 (φ t)) (e1 (u t)) (M t) (ρ t) ∧
      IsSmoothStateTr L (σ' t) (e0 (φ' t)) (e1 (u' t)) (M' t) (ρ' t) ∧ ‖lam t‖ ≤ L ∧
      ‖lam' t‖ ≤ L) →
    ∃ σh φh uh Mh ρh lamh, (cubeQ hT hB N).IsDiscreteWave T f σh φh uh Mh ρh lamh ∧
      ∀ t ∈ Icc 0 T, √(‖(σ t : W0) - σh t‖ ^ 2 + ‖(u t : Wv W1) - uh t‖ ^ 2 +
        ‖M t - Mh t‖ ^ 2 + ‖ρ t - ρh t‖ ^ 2) ≤
          K * L * (1 + t) * Feec.Models.Cube.FEM.meshSize N := by
  obtain ⟨K, -, hK⟩ := cubeWave_rate_tr' hT hB
  refine ⟨K, fun N T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' L hT0 hf hw hreg => ?_⟩
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT0.le⟩
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hreg 0 h0).2.2.1
  obtain ⟨sh, -, hsh⟩ := hK N hT0 hf (toExactWave hw) hL0
    (fun t ht => ⟨(hreg t ht).1, (hreg t ht).2.1⟩) (fun t ht μ =>
      ⟨(abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hreg t ht).2.2.1
        (norm_nonneg _)),
       (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hreg t ht).2.2.2
        (norm_nonneg _))⟩)
  refine ⟨fun t => ((sh.σ t : U0) : 𝒟.d0.domain), fun t => e0.symm (sh.φ t : Wv U0),
    fun t => ofWv1 (sh.u t : Wv U1), fun t => (sh.M t : W2), fun t => (sh.ρ t : Wv W2),
    fun t => ((sh.lam t : U1) : W1), ⟨?_, ?_, ?_, ?_, fun t ht => ?_,
      fun t => ((sh.σ' t : U0) : W0), fun t => ((ofWv1 (sh.u' t : Wv U1) : 𝒟.dt1.domain) : Wv W1),
      fun t => (sh.M' t : W2), fun t => (sh.ρ' t : Wv W2), fun t ht => ?_⟩, fun t ht => ?_⟩
  · exact continuous_subtype_val.comp_continuousOn (continuous_subtype_val.comp_continuousOn sh.cσ)
  · exact incl1CLM.continuous.comp_continuousOn (continuous_subtype_val.comp_continuousOn sh.cu)
  · exact continuous_subtype_val.comp_continuousOn sh.cM
  · exact continuous_subtype_val.comp_continuousOn sh.cρ
  · have hc := sh.constraint ht
    exact ⟨(sh.σ t).2, fun a => (sh.φ t).2 a, fun a => (sh.u t).2 a, (sh.M t).2,
      fun a => (sh.ρ t).2 a, (sh.lam t).2,
      (congrArg (fun x : (cubeFEM hT hB N).V1h => ((x : U1) : W1)) hc :)⟩
  · have ht' : t ∈ Icc 0 T := Ico_subset_Icc_self ht
    have hu1 := hasDerivWithinAt_coe _ (sh.du t ht)
    have hu2 := hasDerivWithinAt_piCoe D1.domain hu1
    refine ⟨hasDerivWithinAt_coe _ (hasDerivWithinAt_coe _ (sh.dσ t ht)), hu2,
      hasDerivWithinAt_coe _ (sh.dM t ht), hasDerivWithinAt_coe _ (sh.dρ t ht),
      fun τ ψ hτ hψ => ?_, fun v hv => ?_, fun z hz => ?_, fun z hz => ?_⟩
    · exact sh.ea t ht' ⟨τ, hτ⟩ ⟨e0 ψ, e0_mem hT hB N hψ⟩
    · have := sh.eb t ht ⟨e1 v, e1_mem hT hB N hv⟩
      have hs := inner_cubeSource hT hB N f t ⟨e1 v, e1_mem hT hB N hv⟩
      exact this.trans hs
    · have := sh.ec t ht ⟨z, hz⟩
      exact sub_eq_zero.1 this
    · have := sh.ed t ht ⟨z, fun a => hz a⟩
      exact sub_eq_zero.1 this
  · have e1' : (u t : Wv W1) - ((ofWv1 (sh.u t : Wv U1) : 𝒟.dt1.domain) : Wv W1) =
        incl1 (e1 (u t) - (sh.u t : Wv U1)) := by rw [map_sub]; rfl
    have hn : ‖(u t : Wv W1) - ((ofWv1 (sh.u t : Wv U1) : 𝒟.dt1.domain) : Wv W1)‖ =
        ‖e1 (u t) - (sh.u t : Wv U1)‖ := by rw [e1']; exact norm_incl1 _
    rw [hn]
    exact hsh t ht

set_option maxHeartbeats 8000000 in
/-- **The rate of (6.5) on the cube for `H¹_univ` states** (`cubeWave_rate_sobolev_of_one_le`,
the solution of `Feec`'s (6.3) for `cubeWave` being a solution of (6.5) for `cubeQ`). -/
theorem cube_wave_rate_sob : ∃ K, ∀ N T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' L, 0 < T →
    ContinuousOn f (Icc 0 T) → 𝒟.IsWaveSolution T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' →
    (∀ t ∈ Icc 0 T, IsSobolevStateTr 1 L (σ t) (e0 (φ t)) (e1 (u t)) (M t) (ρ t) ∧
      IsSobolevStateTr 1 L (σ' t) (e0 (φ' t)) (e1 (u' t)) (M' t) (ρ' t) ∧ ‖lam t‖ ≤ L ∧
      ‖lam' t‖ ≤ L) →
    ∃ σh φh uh Mh ρh lamh, (cubeQ hT hB N).IsDiscreteWave T f σh φh uh Mh ρh lamh ∧
      ∀ t ∈ Icc 0 T, √(‖(σ t : W0) - σh t‖ ^ 2 + ‖(u t : Wv W1) - uh t‖ ^ 2 +
        ‖M t - Mh t‖ ^ 2 + ‖ρ t - ρh t‖ ^ 2) ≤
          K * L * (1 + t) * Feec.Models.Cube.FEM.meshSize N := by
  obtain ⟨K, -, hK⟩ := cubeWave_rate_sobolev_of_one_le hT hB
  refine ⟨K, fun N T f σ σ' φ φ' u u' M M' ρ ρ' lam lam' L hT0 hf hw hreg => ?_⟩
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT0.le⟩
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hreg 0 h0).2.2.1
  obtain ⟨sh, -, hsh⟩ := hK N hT0 hf (toExactWave hw) (s := 1) le_rfl hL0
    (fun t ht => ⟨(hreg t ht).1, (hreg t ht).2.1⟩) (fun t ht μ =>
      ⟨(abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hreg t ht).2.2.1
        (norm_nonneg _)),
       (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hreg t ht).2.2.2
        (norm_nonneg _))⟩)
  refine ⟨fun t => ((sh.σ t : U0) : 𝒟.d0.domain), fun t => e0.symm (sh.φ t : Wv U0),
    fun t => ofWv1 (sh.u t : Wv U1), fun t => (sh.M t : W2), fun t => (sh.ρ t : Wv W2),
    fun t => ((sh.lam t : U1) : W1), ⟨?_, ?_, ?_, ?_, fun t ht => ?_,
      fun t => ((sh.σ' t : U0) : W0), fun t => ((ofWv1 (sh.u' t : Wv U1) : 𝒟.dt1.domain) : Wv W1),
      fun t => (sh.M' t : W2), fun t => (sh.ρ' t : Wv W2), fun t ht => ?_⟩, fun t ht => ?_⟩
  · exact continuous_subtype_val.comp_continuousOn (continuous_subtype_val.comp_continuousOn sh.cσ)
  · exact incl1CLM.continuous.comp_continuousOn (continuous_subtype_val.comp_continuousOn sh.cu)
  · exact continuous_subtype_val.comp_continuousOn sh.cM
  · exact continuous_subtype_val.comp_continuousOn sh.cρ
  · have hc := sh.constraint ht
    exact ⟨(sh.σ t).2, fun a => (sh.φ t).2 a, fun a => (sh.u t).2 a, (sh.M t).2,
      fun a => (sh.ρ t).2 a, (sh.lam t).2,
      (congrArg (fun x : (cubeFEM hT hB N).V1h => ((x : U1) : W1)) hc :)⟩
  · have ht' : t ∈ Icc 0 T := Ico_subset_Icc_self ht
    have hu1 := hasDerivWithinAt_coe _ (sh.du t ht)
    have hu2 := hasDerivWithinAt_piCoe D1.domain hu1
    refine ⟨hasDerivWithinAt_coe _ (hasDerivWithinAt_coe _ (sh.dσ t ht)), hu2,
      hasDerivWithinAt_coe _ (sh.dM t ht), hasDerivWithinAt_coe _ (sh.dρ t ht),
      fun τ ψ hτ hψ => ?_, fun v hv => ?_, fun z hz => ?_, fun z hz => ?_⟩
    · exact sh.ea t ht' ⟨τ, hτ⟩ ⟨e0 ψ, e0_mem hT hB N hψ⟩
    · have := sh.eb t ht ⟨e1 v, e1_mem hT hB N hv⟩
      have hs := inner_cubeSource hT hB N f t ⟨e1 v, e1_mem hT hB N hv⟩
      exact this.trans hs
    · have := sh.ec t ht ⟨z, hz⟩
      exact sub_eq_zero.1 this
    · have := sh.ed t ht ⟨z, fun a => hz a⟩
      exact sub_eq_zero.1 this
  · have e1' : (u t : Wv W1) - ((ofWv1 (sh.u t : Wv U1) : 𝒟.dt1.domain) : Wv W1) =
        incl1 (e1 (u t) - (sh.u t : Wv U1)) := by rw [map_sub]; rfl
    have hn : ‖(u t : Wv W1) - ((ofWv1 (sh.u t : Wv U1) : 𝒟.dt1.domain) : Wv W1)‖ =
        ‖e1 (u t) - (sh.u t : Wv U1)‖ := by rw [e1']; exact norm_incl1 _
    rw [hn]
    exact hsh t ht

end Disc

end FEEC
