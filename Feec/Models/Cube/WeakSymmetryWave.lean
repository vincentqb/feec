module

public import Feec.Models.Cube.WeakSymmetryFEM
public import Feec.HilbertComplex.BGG.DiscreteWave

/-!
# The semi-discrete BGG wave system (6.5) on the cube: well-posedness, stability, `O(h)` rate

The method of [QuennevilleBelair2015], §6.3, (6.5), Table 6.1, for the BGG data (4.16) on
`Q = (0, ½)³`: well-posedness, energy stability and, under `CurlPotential`, `O(h)` convergence to
the classical solutions of (6.2) that are `C²` up to `∂Q` with vanishing tangential traces and
have `L²`-bounded multipliers.

## Main results

* `Feec.BGG.ExactWave.exists_discreteSolution_rate`: the abstract `O(h)` rate theorem.
* `Feec.BGG.DiscreteSolution.sqrt_energy_le`: energy stability.
* `cubeWave_exists_iff`, `cubeWave_exists_unique`: Prop 6.2 (adapted) for (6.5).
* `cubeWave_rate_tr`: the rate `K L (1 + t) h_N` from the elliptic projection (6.4).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open MeasureTheory Set Filter

@[expose] public noncomputable section


/-! ## Classical solutions of (6.2) and the rate theorem in components -/

namespace Feec.BGG

section ExactWave

variable {V0 Vt1 W2 Wt2 V1 Vt0 : Type*}
  [NormedAddCommGroup V0] [InnerProductSpace ℝ V0]
  [NormedAddCommGroup V1] [InnerProductSpace ℝ V1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
  [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0]
  [NormedAddCommGroup Vt1] [InnerProductSpace ℝ Vt1]
  [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]

variable (V0 Vt1 W2 Wt2) in
/-- The energy space `V⁰ × Ṽ¹ × V² × Ṽ²` with the `L²`-product (sum) inner product. -/
abbrev EnergySpace : Type _ := WithLp 2 (V0 × WithLp 2 (Vt1 × WithLp 2 (W2 × Wt2)))

variable (V0 Vt1 W2 Wt2) in
/-- The energy embedding `(σ, u, M, ρ) ↦ (σ, u, M, ρ) ∈ EnergySpace`. -/
def energyEmb : (V0 × Vt1 × W2 × Wt2) →L[ℝ] EnergySpace V0 Vt1 W2 Wt2 :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ V0 _).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℝ V0).prodMap
      ((WithLp.prodContinuousLinearEquiv 2 ℝ Vt1 _).symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.id ℝ Vt1).prodMap
          (WithLp.prodContinuousLinearEquiv 2 ℝ W2 Wt2).symm.toContinuousLinearMap)))

theorem isEnergyEmbedding_energyEmb : Discrete.IsEnergyEmbedding (energyEmb V0 Vt1 W2 Wt2) := by
  intro a b
  simp only [energyEmb, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_prodMap',
    Prod.map, ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_symm_apply,
    ContinuousLinearMap.id_apply, WithLp.prod_inner_apply]
  ring

variable (V0 Vt1 W2 Wt2) in
/-- The coordinates of the energy space. -/
def energyCoord : EnergySpace V0 Vt1 W2 Wt2 →ₗ[ℝ] V0 × Vt1 × W2 × Wt2 where
  toFun x := ((WithLp.ofLp x).1, (WithLp.ofLp (WithLp.ofLp x).2).1,
    (WithLp.ofLp (WithLp.ofLp (WithLp.ofLp x).2).2).1,
    (WithLp.ofLp (WithLp.ofLp (WithLp.ofLp x).2).2).2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem energyCoord_energyEmb (a : V0 × Vt1 × W2 × Wt2) :
    energyCoord V0 Vt1 W2 Wt2 (energyEmb V0 Vt1 W2 Wt2 a) = a := rfl

theorem energyEmb_injective : Function.Injective (energyEmb V0 Vt1 W2 Wt2) := fun a b h => by
  simpa using congrArg (energyCoord V0 Vt1 W2 Wt2) h

variable (V0 Vt1 W2 Wt2) in
/-- The skew form `a` of §6.2 for a segment `D'`, as a bilinear form on `EnergySpace × Ṽ⁰`. -/
def skewBil (D' : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2) :
    (EnergySpace V0 Vt1 W2 Wt2 × Vt0) →ₗ[ℝ] (EnergySpace V0 Vt1 W2 Wt2 × Vt0) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => discreteSkewForm D' (energyCoord V0 Vt1 W2 Wt2 x.1, x.2)
      (energyCoord V0 Vt1 W2 Wt2 y.1, y.2))
    (by intros; simp only [discreteSkewForm, Prod.fst_add, Prod.snd_add, map_add,
          inner_add_left]; ring)
    (by intros; simp only [discreteSkewForm, Prod.smul_fst, Prod.smul_snd, map_smul,
          real_inner_smul_left, smul_eq_mul]; ring)
    (by intros; simp only [discreteSkewForm, Prod.fst_add, Prod.snd_add, map_add,
          inner_add_right]; ring)
    (by intros; simp only [discreteSkewForm, Prod.smul_fst, Prod.smul_snd, map_smul,
          real_inner_smul_right, smul_eq_mul]; ring)

/-- **A classical solution of the multiplier problem (6.2)** of [QuennevilleBelair2015], §6.1. -/
structure ExactWave (D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2) (T : ℝ) (g : ℝ → Vt1 →ₗ[ℝ] ℝ) where
  σ : ℝ → V0
  φ : ℝ → Vt0
  u : ℝ → Vt1
  M : ℝ → W2
  ρ : ℝ → Wt2
  ℓ : ℝ → V1 →ₗ[ℝ] ℝ
  σ' : ℝ → V0
  φ' : ℝ → Vt0
  u' : ℝ → Vt1
  M' : ℝ → W2
  ρ' : ℝ → Wt2
  ℓ' : ℝ → V1 →ₗ[ℝ] ℝ
  cσ : ContinuousOn σ (Icc 0 T)
  cu : ContinuousOn u (Icc 0 T)
  cM : ContinuousOn M (Icc 0 T)
  cρ : ContinuousOn ρ (Icc 0 T)
  cdφ : ContinuousOn (fun s => D.dt0 (φ s)) (Icc 0 T)
  cSu : ContinuousOn (fun s => D.S1 (u s)) (Icc 0 T)
  cdu : ContinuousOn (fun s => D.dt1 (u s)) (Icc 0 T)
  cℓ : ∀ μ, ContinuousOn (fun s => ℓ s μ) (Icc 0 T)
  cσ' : ContinuousOn σ' (Icc 0 T)
  cu' : ContinuousOn u' (Icc 0 T)
  cM' : ContinuousOn M' (Icc 0 T)
  cρ' : ContinuousOn ρ' (Icc 0 T)
  cdφ' : ContinuousOn (fun s => D.dt0 (φ' s)) (Icc 0 T)
  cSu' : ContinuousOn (fun s => D.S1 (u' s)) (Icc 0 T)
  cdu' : ContinuousOn (fun s => D.dt1 (u' s)) (Icc 0 T)
  cℓ' : ∀ μ, ContinuousOn (fun s => ℓ' s μ) (Icc 0 T)
  dσ : ∀ t ∈ Ico 0 T, HasDerivWithinAt σ (σ' t) (Ici t) t
  du : ∀ t ∈ Ico 0 T, HasDerivWithinAt u (u' t) (Ici t) t
  dM : ∀ t ∈ Ico 0 T, HasDerivWithinAt M (M' t) (Ici t) t
  dρ : ∀ t ∈ Ico 0 T, HasDerivWithinAt ρ (ρ' t) (Ici t) t
  ddφ : ∀ t ∈ Ico 0 T, HasDerivWithinAt (fun s => D.dt0 (φ s)) (D.dt0 (φ' t)) (Ici t) t
  dSu : ∀ t ∈ Ico 0 T, HasDerivWithinAt (fun s => D.S1 (u s)) (D.S1 (u' t)) (Ici t) t
  ddu : ∀ t ∈ Ico 0 T, HasDerivWithinAt (fun s => D.dt1 (u s)) (D.dt1 (u' t)) (Ici t) t
  dℓ : ∀ t ∈ Ico 0 T, ∀ μ, HasDerivWithinAt (fun s => ℓ s μ) (ℓ' t μ) (Ici t) t
  ea : ∀ t ∈ Ico 0 T, ∀ τ ψ, ⟪σ' t, τ⟫ - ⟪u t, D.dt0 ψ⟫ - ℓ t (D.d0 τ - D.S0 ψ) = 0
  eb : ∀ t ∈ Ico 0 T, ∀ v,
    ⟪u' t, v⟫ + ⟪D.dt0 (φ t), v⟫ + ⟪M t, D.S1 v⟫ + ⟪ρ t, D.dt1 v⟫ = g t v
  ec : ∀ t ∈ Ico 0 T, ∀ N, ⟪M' t, N⟫ - ⟪D.S1 (u t), N⟫ = 0
  ed : ∀ t ∈ Ico 0 T, ∀ μ, ⟪ρ' t, μ⟫ - ⟪D.dt1 (u t), μ⟫ = 0
  ee : ∀ t ∈ Icc 0 T, D.d0 (σ t) = D.S0 (φ t)
  ee' : ∀ t ∈ Icc 0 T, D.d0 (σ' t) = D.S0 (φ' t)

theorem hasDerivWithinAt_inner_const {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : ℝ → E} {g' : E} {s : Set ℝ} {t : ℝ} (h : HasDerivWithinAt g g' s t) (w : E) :
    HasDerivWithinAt (fun r => ⟪g r, w⟫) ⟪g', w⟫ s t := by
  simpa using h.inner ℝ (hasDerivWithinAt_const t s w)

theorem continuousOn_inner_const {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : ℝ → E} {s : Set ℝ} (h : ContinuousOn g s) (w : E) :
    ContinuousOn (fun r => ⟪g r, w⟫) s :=
  h.inner continuousOn_const

/-- **Energy stability of (6.3)**: `E(t)^{1/2} ≤ E(0)^{1/2} + ∫₀ᵗ ‖f‖` on `[0, T]`. -/
theorem DiscreteSolution.sqrt_energy_le {P0 P1 P2 Pt0 Pt1 Pt2 : Type*}
    [NormedAddCommGroup P0] [InnerProductSpace ℝ P0]
    [NormedAddCommGroup P1] [InnerProductSpace ℝ P1]
    [NormedAddCommGroup P2] [InnerProductSpace ℝ P2]
    [NormedAddCommGroup Pt0] [InnerProductSpace ℝ Pt0]
    [NormedAddCommGroup Pt1] [InnerProductSpace ℝ Pt1]
    [NormedAddCommGroup Pt2] [InnerProductSpace ℝ Pt2]
    {D : Segment ℝ P0 P1 P2 Pt0 Pt1 Pt2} {T : ℝ} {f : ℝ → Pt1} (s : DiscreteSolution D T f)
    (hf : ContinuousOn f (Icc 0 T)) :
    ∀ t ∈ Icc 0 T, √(‖s.σ t‖ ^ 2 + ‖s.u t‖ ^ 2 + ‖s.M t‖ ^ 2 + ‖s.ρ t‖ ^ 2) ≤
      √(‖s.σ 0‖ ^ 2 + ‖s.u 0‖ ^ 2 + ‖s.M 0‖ ^ 2 + ‖s.ρ 0‖ ^ 2) + ∫ r in (0:ℝ)..t, ‖f r‖ := by
  have hι := isEnergyEmbedding_energyEmb (V0 := P0) (Vt1 := Pt1) (W2 := P2) (Wt2 := Pt2)
  set ι := energyEmb P0 Pt1 P2 Pt2
  set e : ℝ → EnergySpace P0 Pt1 P2 Pt2 := fun t => ι (s.σ t, s.u t, s.M t, s.ρ t)
  have hn : ∀ t, ‖e t‖ = √(‖s.σ t‖ ^ 2 + ‖s.u t‖ ^ 2 + ‖s.M t‖ ^ 2 + ‖s.ρ t‖ ^ 2) := fun t => by
    have := Discrete.norm_sub_of_isEnergyEmbedding hι (s.σ t, s.u t, s.M t, s.ρ t) 0
    simpa [e] using this
  have hc : ContinuousOn (fun t => e t - 0) (Icc 0 T) :=
    (ι.continuous.comp_continuousOn (s.cσ.prodMk (s.cu.prodMk (s.cM.prodMk s.cρ)))).sub
      continuousOn_const
  have hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt (fun t => e t - 0)
      (ι (s.σ' t, s.u' t, s.M' t, s.ρ' t)) (Ici t) t := fun t ht => by
    have h1 : HasDerivWithinAt (fun r => (s.σ r, s.u r, s.M r, s.ρ r))
        (s.σ' t, s.u' t, s.M' t, s.ρ' t) (Ici t) t :=
      (s.dσ t ht).prodMk ((s.du t ht).prodMk ((s.dM t ht).prodMk (s.dρ t ht)))
    exact (ι.hasFDerivAt.comp_hasDerivWithinAt t h1).sub_const 0
  have key := Variational.norm_sub_le_of_projected_error (𝕜 := ℝ) (u := e) (p := e)
    (uh := fun _ => 0) hc hd (hf.norm) (fun _ _ => norm_nonneg _) (fun t ht => by
      rw [RCLike.re_to_real, sub_zero, hι]
      have ht' : t ∈ Icc 0 T := Ico_subset_Icc_self ht
      have ha := s.ea t ht' (s.σ t) (s.φ t)
      rw [s.constraint ht', sub_self, inner_zero_right, sub_zero] at ha
      have hb := s.eb t ht (s.u t)
      have hcM := s.ec t ht (s.M t)
      have hdd := s.ed t ht (s.ρ t)
      have hu : ‖s.u t‖ ≤ ‖e t‖ := by
        rw [hn]; exact Real.le_sqrt_of_sq_le (by
          nlinarith [sq_nonneg (‖s.σ t‖), sq_nonneg (‖s.M t‖), sq_nonneg (‖s.ρ t‖)])
      have hfu := (real_inner_le_norm (f t) (s.u t)).trans
        (mul_le_mul_of_nonneg_left hu (norm_nonneg _))
      simp only
      linarith [real_inner_comm (s.σ t) (s.σ' t), real_inner_comm (D.dt0 (s.φ t)) (s.u t),
        real_inner_comm (s.u t) (s.u' t), real_inner_comm (D.S1 (s.u t)) (s.M t),
        real_inner_comm (D.dt1 (s.u t)) (s.ρ t), real_inner_comm (s.M t) (s.M' t),
        real_inner_comm (s.ρ t) (s.ρ' t)])
  intro t ht
  have := key t ht
  simp only [sub_self, norm_zero, zero_add, sub_zero] at this
  rwa [hn, hn] at this

namespace Discrete

variable {D : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2} (Q : Discrete D) {T : ℝ} {g : ℝ → Vt1 →ₗ[ℝ] ℝ}

/-- The discrete BGG data of `Q` on the continuous spaces: `d`, `S₀,ₕ = Π¹S₀`, `S₁,ₕ = Π²S₁`. -/
def hSegment : Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2 where
  d0 := D.d0
  d1 := D.d1
  dt0 := D.dt0
  dt1 := D.dt1
  S0 := Q.S0h
  S1 := Q.S1h
  d1_d0 := D.d1_d0
  dt1_dt0 := D.dt1_dt0
  anticomm := Q.anticomm_h

/-- The constraint map `(x, ψ) ↦ Π¹ dσ − S₀,ₕψ ∈ Vₕ¹` on `EnergySpace × Ṽ⁰`. -/
def constraintH : (EnergySpace V0 Vt1 W2 Wt2 × Vt0) →ₗ[ℝ] Q.V1h :=
  LinearMap.codRestrict Q.V1h
    ((Q.P1 ∘ₗ D.d0 ∘ₗ (LinearMap.fst ℝ V0 _) ∘ₗ energyCoord V0 Vt1 W2 Wt2) ∘ₗ
        LinearMap.fst ℝ _ Vt0 - Q.S0h ∘ₗ LinearMap.snd ℝ _ Vt0)
    fun _ => Q.V1h.sub_mem (Q.P1_mem _) (Q.S0h_mem _)

variable (D) in
/-- The multiplier term `(x, ψ) ↦ ℓ(dσ − S₀ψ)`. -/
def multTerm (ℓ : V1 →ₗ[ℝ] ℝ) : (EnergySpace V0 Vt1 W2 Wt2 × Vt0) →ₗ[ℝ] ℝ :=
  ℓ ∘ₗ ((D.d0 ∘ₗ (LinearMap.fst ℝ V0 _) ∘ₗ energyCoord V0 Vt1 W2 Wt2) ∘ₗ
    LinearMap.fst ℝ _ Vt0 - D.S0 ∘ₗ LinearMap.snd ℝ _ Vt0)

theorem _root_.Feec.BGG.ExactWave.hasDerivWithinAt_ellipticDataH (s : ExactWave D T g) {t : ℝ}
    (ht : t ∈ Ico 0 T) (y : (Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) × Q.Vt0h) :
    HasDerivWithinAt (fun r => Q.ellipticDataH (s.σ r) (s.φ r) (s.u r) (s.M r) (s.ρ r) (s.ℓ r) y)
      (Q.ellipticDataH (s.σ' t) (s.φ' t) (s.u' t) (s.M' t) (s.ρ' t) (s.ℓ' t) y) (Ici t) t := by
  have h := (((((((((((hasDerivWithinAt_inner_const (s.dσ t ht) (y.1.1 : V0)).add
    (hasDerivWithinAt_inner_const (s.du t ht) (y.1.2.1 : Vt1))).add
    (hasDerivWithinAt_inner_const (s.dM t ht) (y.1.2.2.1 : W2))).add
    (hasDerivWithinAt_inner_const (s.dρ t ht) (y.1.2.2.2 : Wt2))).sub
    (hasDerivWithinAt_inner_const (s.du t ht) (D.dt0 (y.2 : Vt0)))).add
    (hasDerivWithinAt_inner_const (s.ddφ t ht) (y.1.2.1 : Vt1))).add
    (hasDerivWithinAt_inner_const (s.dM t ht) (D.S1 (y.1.2.1 : Vt1)))).add
    (hasDerivWithinAt_inner_const (s.dρ t ht) (D.dt1 (y.1.2.1 : Vt1)))).sub
    (hasDerivWithinAt_inner_const (s.dSu t ht) (y.1.2.2.1 : W2))).sub
    (hasDerivWithinAt_inner_const (s.ddu t ht) (y.1.2.2.2 : Wt2))).sub
    (s.dℓ t ht (D.d0 (y.1.1 : V0) - D.S0 (y.2 : Vt0))))
  exact h

theorem _root_.Feec.BGG.ExactWave.continuousOn_ellipticDataH (s : ExactWave D T g)
    (y : (Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) × Q.Vt0h) :
    ContinuousOn (fun r => Q.ellipticDataH (s.σ r) (s.φ r) (s.u r) (s.M r) (s.ρ r) (s.ℓ r) y)
      (Icc 0 T) := by
  exact ((((((((((continuousOn_inner_const s.cσ _).add
    (continuousOn_inner_const s.cu _)).add (continuousOn_inner_const s.cM _)).add
    (continuousOn_inner_const s.cρ _)).sub (continuousOn_inner_const s.cu _)).add
    (continuousOn_inner_const s.cdφ _)).add (continuousOn_inner_const s.cM _)).add
    (continuousOn_inner_const s.cρ _)).sub (continuousOn_inner_const s.cSu _)).sub
    (continuousOn_inner_const s.cdu _)).sub (s.cℓ _)

theorem _root_.Feec.BGG.ExactWave.continuousOn_ellipticDataH' (s : ExactWave D T g)
    (y : (Q.V0h × Q.Vt1h × Q.W2h × Q.Wt2h) × Q.Vt0h) :
    ContinuousOn
      (fun r => Q.ellipticDataH (s.σ' r) (s.φ' r) (s.u' r) (s.M' r) (s.ρ' r) (s.ℓ' r) y)
      (Icc 0 T) := by
  exact ((((((((((continuousOn_inner_const s.cσ' _).add
    (continuousOn_inner_const s.cu' _)).add (continuousOn_inner_const s.cM' _)).add
    (continuousOn_inner_const s.cρ' _)).sub (continuousOn_inner_const s.cu' _)).add
    (continuousOn_inner_const s.cdφ' _)).add (continuousOn_inner_const s.cM' _)).add
    (continuousOn_inner_const s.cρ' _)).sub (continuousOn_inner_const s.cSu' _)).sub
    (continuousOn_inner_const s.cdu' _)).sub (s.cℓ' _)

/-- **`O(h)` convergence of (6.3)** ([QuennevilleBelair2015], §6.2): under `Stability`, (5.4), onto
`S₀,ₕ` and consistency bounds, Strang data `≤ (c h)²` give a solution within `C |c h| (1 + t)`. -/
theorem _root_.Feec.BGG.ExactWave.exists_discreteSolution_rate {Cp CR CS : ℝ}
    (H : Stability D Cp CR CS) (h54 : Q.Compatible) [FiniteDimensional ℝ Q.V0h]
    [FiniteDimensional ℝ Q.V1h] [FiniteDimensional ℝ Q.W2h]
    [FiniteDimensional ℝ Q.Vt0h] [FiniteDimensional ℝ Q.Vt1h]
    [FiniteDimensional ℝ Q.Wt2h] (hS : Function.Surjective Q.toSegmentH.S0)
    (hT : 0 < T) (s : ExactWave D T g) {fh : ℝ → Q.Vt1h} (hfh : ContinuousOn fh (Icc 0 T))
    (hg : ∀ t ∈ Ico 0 T, ∀ v : Q.Vt1h, g t v = ⟪fh t, v⟫) {K0 K1 c h : ℝ}
    (hK0 : ∀ t ∈ Icc 0 T, ∀ ψ ∈ Q.Vt0h, |s.ℓ t ((D.S0 - Q.S0h) ψ)| ≤ K0 * √(graphSq D.dt0 ψ))
    (hK0' : ∀ t ∈ Icc 0 T, ∀ ψ ∈ Q.Vt0h,
      |s.ℓ' t ((D.S0 - Q.S0h) ψ)| ≤ K0 * √(graphSq D.dt0 ψ))
    (hK1 : ∀ t ∈ Icc 0 T, ∀ v ∈ Q.Vt1h, |⟪s.M t, (D.S1 - Q.S1h) v⟫| ≤ K1 * √(Q.gnSq v))
    (hK1' : ∀ t ∈ Icc 0 T, ∀ v ∈ Q.Vt1h, |⟪s.M' t, (D.S1 - Q.S1h) v⟫| ≤ K1 * √(Q.gnSq v))
    (hdata : ∀ t ∈ Icc 0 T,
      Q.strangData (s.σ t) (s.φ t) (s.u t) (s.M t) (s.ρ t) K0 K1 ≤ (c * h) ^ 2)
    (hdata' : ∀ t ∈ Icc 0 T,
      Q.strangData (s.σ' t) (s.φ' t) (s.u' t) (s.M' t) (s.ρ' t) K0 K1 ≤ (c * h) ^ 2) :
    ∃ sh : DiscreteSolution Q.toSegmentH T fh,
      (sh.σ 0, sh.u 0, sh.M 0, sh.ρ 0) =
        (ellipticProjection Q.toSegmentH (toSegmentH_dt0_injective H)
          (exists_sub_eq_of_surjective hS) (ellipticRhs (Q.ellipticDataH (s.σ 0) (s.φ 0)
            (s.u 0) (s.M 0) (s.ρ 0) (s.ℓ 0)) 0)).1.1 ∧
      ∀ t ∈ Icc 0 T, √(‖s.σ t - sh.σ t‖ ^ 2 + ‖s.u t - sh.u t‖ ^ 2 + ‖s.M t - sh.M t‖ ^ 2 +
        ‖s.ρ t - sh.ρ t‖ ^ 2) ≤ √(2 * (strangConst Cp + 1)) * |c| * |h| * (2 + 2 * t) := by
  have hιc := isEnergyEmbedding_energyEmb (V0 := V0) (Vt1 := Vt1) (W2 := W2) (Wt2 := Wt2)
  obtain ⟨sh, hinit, hbd⟩ := exists_discreteSolution_norm_sub_le_rate (Q := Q) H h54 hS
    hιc LinearMap.id (skewBil V0 Vt1 W2 Wt2 D) (skewBil V0 Vt1 W2 Wt2 Q.hSegment)
    Q.constraintH (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun a ψ => Subtype.ext (by
      change Q.P1 (D.d0 (a.1 : V0)) - Q.S0h (ψ : Vt0) = D.d0 (a.1 : V0) - Q.S0h (ψ : Vt0)
      rw [Q.P1_id _ (Q.d0_mem _ a.1.2)]))
    hT hfh (fun t => (s.σ t, s.u t, s.M t, s.ρ t)) (fun t => (s.σ' t, s.u' t, s.M' t, s.ρ' t))
    s.φ s.φ' s.ℓ s.ℓ' (fun t => multTerm D (s.ℓ t)) (fun _ _ _ => rfl)
    (fun t => energyEmb V0 Vt1 W2 Wt2 (0, (fh t : Vt1), 0, 0))
    (fun t _ b => by
      rw [Discrete.embedH_apply, hιc]
      simp)
    (s.cσ.prodMk (s.cu.prodMk (s.cM.prodMk s.cρ)))
    (s.cσ'.prodMk (s.cu'.prodMk (s.cM'.prodMk s.cρ')))
    (by
      rintro t ht _ ⟨⟨b, ψ⟩, rfl⟩
      change ⟪energyEmb V0 Vt1 W2 Wt2 (s.σ' t, s.u' t, s.M' t, s.ρ' t),
          energyEmb V0 Vt1 W2 Wt2 ((b.1 : V0), (b.2.1 : Vt1), (b.2.2.1 : W2), (b.2.2.2 : Wt2))⟫ +
        discreteSkewForm D ((s.σ t, s.u t, s.M t, s.ρ t), s.φ t)
          (((b.1 : V0), (b.2.1 : Vt1), (b.2.2.1 : W2), (b.2.2.2 : Wt2)), (ψ : Vt0)) -
        s.ℓ t (D.d0 (b.1 : V0) - D.S0 (ψ : Vt0)) =
        ⟪energyEmb V0 Vt1 W2 Wt2 (0, (fh t : Vt1), 0, 0),
          energyEmb V0 Vt1 W2 Wt2 ((b.1 : V0), (b.2.1 : Vt1), (b.2.2.1 : W2), (b.2.2.2 : Wt2))⟫
      rw [hιc, hιc]
      simp only [discreteSkewForm, inner_zero_left]
      have ha := s.ea t ht b.1 ψ
      have hb := s.eb t ht b.2.1
      have hc := s.ec t ht b.2.2.1
      have hd := s.ed t ht b.2.2.2
      have he := hg t ht b.2.1
      rw [Submodule.coe_inner] at he
      linarith)
    (fun y => s.continuousOn_ellipticDataH Q y)
    (fun t ht y => s.hasDerivWithinAt_ellipticDataH Q ht y)
    (fun y => s.continuousOn_ellipticDataH' Q y) s.ee s.ee' hK0 hK0' hK1 hK1' hdata hdata'
  refine ⟨sh, ?_, fun t ht => ?_⟩
  · have e := energyEmb_injective hinit
    refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_)
      (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)))
    · exact congrArg Prod.fst e
    · exact congrArg (fun z => z.2.1) e
    · exact congrArg (fun z => z.2.2.1) e
    · exact congrArg (fun z => z.2.2.2) e
  · have hb := hbd t ht
    rw [Discrete.embedH_apply, norm_sub_of_isEnergyEmbedding hιc] at hb
    exact hb

end Discrete

end ExactWave

end Feec.BGG

namespace Feec.Models.Cube.WeakSymmetry

open Feec.Domain Feec.HilbertComplex Feec.FiniteElement Feec.Models.Cube.FEM

section Segment

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

theorem exists_segS0_eq_testField {χ : formIdx 3 1 → (Fin 3 → ℝ) → ℝ}
    (hχ : IsTestField (cubeDomain 3) χ) :
    ∃ ψ : Wv U0, ((segS0 ψ : U1) : W1) = testField hχ := by
  have hψ : ∀ a, IsTestField (cubeDomain 3) (proxy0 χ a) := fun a r => hχ _
  refine ⟨WithLp.toLp 2 fun a => ⟨testField (hψ a),
    ConstCoeffOp.testField_mem_minimal_domain _ (isOpen_cubeDomain 3) (hψ a)⟩, ?_⟩
  rw [coe_segS0]
  exact (wsL2_testField (Ω := cubeDomain 3) (k := 0) hψ).trans
    (testField_congr _ _ (wsFields_proxy0 χ))

theorem exists_S0h_eq (N : ℕ) {μ : U1} (hμ : μ ∈ (cubeFEM hT hB N).V1h) :
    ∃ ψ, (cubeFEM hT hB N).S0h ψ = μ := by
  set π1 : W1 →ₗ[ℝ] W1 := (hT.proj N).π 1
  set K : Submodule ℝ W1 := LinearMap.range (π1 ∘ₗ D1.domain.subtype ∘ₗ segS0)
  have hK : K ≤ (polyMin 3 PolySeq.lowestOrder N).V 1 := by
    rintro _ ⟨ψ, rfl⟩; exact (hT.proj N).mem 1 _
  have : FiniteDimensional ℝ K := Submodule.finiteDimensional_of_le hK
  have hKc : IsClosed (K : Set W1) := K.closed_of_finiteDimensional
  have hπc : Continuous π1 :=
    (LinearMap.mkContinuous π1 (2 * C) (hT.norm_proj_le N 1)).continuous
  have htest : ∀ x ∈ testFieldSub ℝ (cubeDomain 3) (formIdx 3 1), π1 x ∈ K := by
    rintro _ ⟨χ, hχ, rfl⟩
    obtain ⟨ψ, hψ⟩ := exists_segS0_eq_testField hχ
    exact ⟨ψ, by simp [hψ]⟩
  have hall : ∀ x : W1, π1 x ∈ K := by
    intro x
    have hx : x ∈ closure (testFieldSub ℝ (cubeDomain 3) (formIdx 3 1) : Set W1) :=
      (dense_testFieldSub (isOpen_cubeDomain 3) _) x
    have := map_mem_closure hπc hx htest
    rwa [hKc.closure_eq] at this
  obtain ⟨ψ, hψ⟩ := hall μ
  refine ⟨ψ, Subtype.ext ?_⟩
  change π1 ((segS0 ψ : U1) : W1) = (μ : W1)
  rw [show π1 ((segS0 ψ : U1) : W1) = π1 μ from hψ]
  exact (hT.proj N).proj 1 _ hμ

/-! ### The discrete segment of Table 6.1 -/

/-- **The discrete BGG data of Table 6.1**, with `S₀,ₕ = π¹S⁰` and `S₁,ₕ = π²S¹`. -/
abbrev cubeWave (N : ℕ) := (cubeFEM hT hB N).toSegmentH

instance cubeWave_fd2 (N : ℕ) : FiniteDimensional ℝ (cubeFEM hT hB N).W2h :=
  inferInstanceAs (FiniteDimensional ℝ ((polyMin 3 PolySeq.lowestOrder N).V 2))
instance cubeWave_fdt2 (N : ℕ) : FiniteDimensional ℝ (cubeFEM hT hB N).Wt2h :=
  finiteDimensional_tsub ((polyMin 3 PolySeq.lagrangeP2 N).V 2)

theorem cubeWave_dt0_injective (N : ℕ) : Function.Injective (cubeWave hT hB N).dt0 := by
  intro a b hab
  have h : bggSegment.dt0 ((a : Wv U0) - b) = 0 := by
    rw [map_sub, sub_eq_zero]; exact congrArg Subtype.val hab
  have := seg_poinct0 ((a : Wv U0) - b)
  rw [← bggSegment_dt0, h, norm_zero, mul_zero] at this
  exact Subtype.ext (sub_eq_zero.1 (norm_le_zero_iff.1 this))

set_option maxHeartbeats 1000000 in
theorem cubeWave_S0_surjective (N : ℕ) : Function.Surjective (cubeWave hT hB N).S0 := by
  intro μ
  obtain ⟨ψ, hψ⟩ := exists_S0h_eq hT hB N (μ := (μ : U1)) μ.2
  have hc : (cubeFEM hT hB N).S0h ((cubeFEM hT hB N).Pt0 ψ) = (μ : U1) := by
    rw [Feec.BGG.Discrete.S0h_apply, cubeFEM_compatible hT hB N ψ,
      ← Feec.BGG.Discrete.S0h_apply, hψ]
  exact ⟨⟨_, (cubeFEM hT hB N).Pt0_mem ψ⟩, Subtype.ext hc⟩

/-- **[QuennevilleBelair2015], Prop 6.2 (adapted), for (6.5)**: a solution exists iff the
compatibility conditions (C1)–(C3) hold. -/
theorem cubeWave_exists_iff (N : ℕ) {T : ℝ} (hT0 : 0 < T)
    {f : ℝ → (cubeFEM hT hB N).Vt1h} (hf : ContinuousOn f (Icc 0 T)) (σ₀ : (cubeFEM hT hB N).V0h)
    (φ₀ : (cubeFEM hT hB N).Vt0h) (u₀ : (cubeFEM hT hB N).Vt1h) (M₀ : (cubeFEM hT hB N).W2h)
    (ρ₀ : (cubeFEM hT hB N).Wt2h) :
    (∃ s : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T f, s.σ 0 = σ₀ ∧ s.φ 0 = φ₀ ∧
      s.u 0 = u₀ ∧ s.M 0 = M₀ ∧ s.ρ 0 = ρ₀) ↔
      (cubeWave hT hB N).d0 σ₀ = (cubeWave hT hB N).S0 φ₀ ∧
        (∀ ψ, (cubeWave hT hB N).S0 ψ = 0 → ⟪u₀, (cubeWave hT hB N).dt0 ψ⟫ = 0) ∧
        (∀ ψ, (cubeWave hT hB N).S0 ψ = 0 →
          ⟪(cubeWave hT hB N).dt0 φ₀, (cubeWave hT hB N).dt0 ψ⟫ =
            ⟪f 0, (cubeWave hT hB N).dt0 ψ⟫) := by
  constructor
  · rintro ⟨s, rfl, rfl, rfl, -, -⟩
    exact Feec.BGG.DiscreteSolution.compatible hT0 s
  · rintro ⟨h1, h2, h3⟩
    exact Feec.BGG.exists_discreteSolution_of_continuousOn (cubeWave_dt0_injective hT hB N)
      (cubeWave_S0_surjective hT hB N) hT0.le hf h1 h2 h3

/-! ### Well-posedness of (6.5) -/

theorem cubeWave_exists_iff_compatible_u (N : ℕ) {T : ℝ} (hT0 : 0 < T)
    {f : ℝ → (cubeFEM hT hB N).Vt1h} (hf : ContinuousOn f (Icc 0 T))
    (σ₀ : (cubeFEM hT hB N).V0h) (u₀ : (cubeFEM hT hB N).Vt1h) (M₀ : (cubeFEM hT hB N).W2h)
    (ρ₀ : (cubeFEM hT hB N).Wt2h) :
    (∃ s : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T f, s.σ 0 = σ₀ ∧ s.u 0 = u₀ ∧
      s.M 0 = M₀ ∧ s.ρ 0 = ρ₀) ↔
      ∀ ψ, (cubeWave hT hB N).S0 ψ = 0 → ⟪u₀, (cubeWave hT hB N).dt0 ψ⟫ = 0 :=
  Feec.BGG.exists_discreteSolution_iff_compatible_u hT0 (cubeWave_dt0_injective hT hB N)
    (cubeWave_S0_surjective hT hB N) hf σ₀ u₀ M₀ ρ₀

/-- **[QuennevilleBelair2015], Prop 6.2 (adapted), for (6.5), dynamic data**: existence and
uniqueness under (C2). -/
theorem cubeWave_exists_unique (N : ℕ) {T : ℝ} (hT0 : 0 < T)
    {f : ℝ → (cubeFEM hT hB N).Vt1h} (hf : ContinuousOn f (Icc 0 T))
    (σ₀ : (cubeFEM hT hB N).V0h) (u₀ : (cubeFEM hT hB N).Vt1h) (M₀ : (cubeFEM hT hB N).W2h)
    (ρ₀ : (cubeFEM hT hB N).Wt2h)
    (hC2 : ∀ ψ, (cubeWave hT hB N).S0 ψ = 0 → ⟪u₀, (cubeWave hT hB N).dt0 ψ⟫ = 0) :
    ∃ s : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T f,
      (s.σ 0 = σ₀ ∧ s.u 0 = u₀ ∧ s.M 0 = M₀ ∧ s.ρ 0 = ρ₀) ∧
      s.φ 0 = Feec.BGG.phiMap (cubeWave hT hB N) (cubeWave_dt0_injective hT hB N)
        (cubeWave_S0_surjective hT hB N) (σ₀, f 0) ∧
      ∀ s' : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T f,
        (s'.σ 0 = σ₀ ∧ s'.u 0 = u₀ ∧ s'.M 0 = M₀ ∧ s'.ρ 0 = ρ₀) →
        (∀ t ∈ Icc 0 T, s'.σ t = s.σ t ∧ s'.u t = s.u t ∧ s'.M t = s.M t ∧ s'.ρ t = s.ρ t ∧
          s'.lam t = s.lam t) ∧ (∀ t ∈ Ico 0 T, s'.φ t = s.φ t) :=
  Feec.BGG.exists_discreteSolution_unique hT0 (cubeWave_dt0_injective hT hB N)
    (cubeWave_S0_surjective hT hB N) hf σ₀ u₀ M₀ ρ₀ hC2

end Segment

/-! ### Interpolation errors in degree `2` and the data of the Strang bound -/

section Rate

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

/-- **Flat regularity of a state**: all components and `S¹u` are `IsCsFormMin 0` with bound `L`. -/
def IsSmoothState (L : ℝ) (σ : U0) (φ : Wv U0) (u : Wv U1) (M : W2) (ρ : Wv W2) : Prop :=
  IsCsFormMin 0 0 L (σ : W0) ∧ (∀ a, IsCsFormMin 0 0 L (φ a : W0)) ∧
    (∀ a, IsCsFormMin 0 1 L (u a : W1)) ∧ IsCsFormMin 0 2 L (bggSegment.S1 u) ∧
    IsCsFormMin 0 2 L M ∧ ∀ a, IsCsFormMin 0 2 L (ρ a)

/-- The interpolation constant of the Strang data on the cube. -/
def interpConst (C : ℝ) : ℝ :=
  2 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lowestOrder 0) ^ 2 +
    3 * (2 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 0) ^ 2) +
    (1 + 8 * C ^ 2) * (3 * (2 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 1) ^ 2)) +
    ((1 + 2 * C) * polyInterpBound 3 PolySeq.lowestOrder 2) ^ 2 +
    3 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 2) ^ 2 +
    ((1 + 2 * C) * polyInterpBound 3 PolySeq.lowestOrder 2) ^ 2

theorem interpConst_nonneg (C : ℝ) : 0 ≤ interpConst C := by unfold interpConst; positivity

/-- The source functional `v ↦ ⟪f, v⟫` on `H̊Λ¹(Q)³` of an `L²` source `f ∈ (L²Λ¹)³`. -/
def srcFun (f : ℝ → Wv W1) (t : ℝ) : Wv U1 →ₗ[ℝ] ℝ := (innerSL ℝ (f t)).toLinearMap ∘ₗ incl1

theorem srcFun_apply (f : ℝ → Wv W1) (t : ℝ) (v : Wv U1) : srcFun f t v = ⟪f t, incl1 v⟫ := rfl

/-- The inclusion `H̊Λ¹(Q)³ → (L²Λ¹(Q))³` as a bounded map. -/
def incl1CLM : Wv U1 →L[ℝ] Wv W1 :=
  LinearMap.mkContinuous incl1 1 fun x => by rw [norm_incl1, one_mul]

instance cubeWave_completeSpace_t1 (N : ℕ) : CompleteSpace (cubeFEM hT hB N).Vt1h :=
  FiniteDimensional.complete ℝ _

/-- **The discrete source of (6.5)**: the `L²` projection of `f(t)` onto `P₂⁻Λ̊¹ ⊗ ℝ³`. -/
def cubeSource (N : ℕ) (f : ℝ → Wv W1) (t : ℝ) : (cubeFEM hT hB N).Vt1h :=
  (InnerProductSpace.toDual ℝ (cubeFEM hT hB N).Vt1h).symm
    ((innerSL ℝ (f t)).comp (incl1CLM.comp (cubeFEM hT hB N).Vt1h.subtypeL))

theorem inner_cubeSource (N : ℕ) (f : ℝ → Wv W1) (t : ℝ) (v : (cubeFEM hT hB N).Vt1h) :
    ⟪cubeSource hT hB N f t, v⟫ = ⟪f t, incl1 (v : Wv U1)⟫ := by
  rw [cubeSource, InnerProductSpace.toDual_symm_apply]
  rfl

theorem continuousOn_cubeSource (N : ℕ) {f : ℝ → Wv W1} {T : ℝ}
    (hf : ContinuousOn f (Icc 0 T)) : ContinuousOn (cubeSource hT hB N f) (Icc 0 T) := by
  have h1 : Continuous fun w : Wv W1 =>
      (innerSL ℝ w).comp (incl1CLM.comp (cubeFEM hT hB N).Vt1h.subtypeL) :=
    ((ContinuousLinearMap.compL ℝ (cubeFEM hT hB N).Vt1h (Wv W1) ℝ).flip
      (incl1CLM.comp (cubeFEM hT hB N).Vt1h.subtypeL)).continuous.comp (innerSL ℝ).continuous
  exact (InnerProductSpace.toDual ℝ (cubeFEM hT hB N).Vt1h).symm.continuous.comp_continuousOn
    (h1.comp_continuousOn hf)

set_option maxHeartbeats 4000000 in
theorem cubeWave_rate_of_bounds {CR : ℝ} (hCR0 : 0 ≤ CR)
    (hCR : ∀ u : V1, ∃ φ : Vt0, bggD1 (bggS0 φ) = bggD1 u ∧ ‖φ‖ ≤ CR * ‖bggD1 u‖) :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {T : ℝ} (_hT0 : 0 < T) {f : ℝ → Wv W1}
      (_hf : ContinuousOn f (Icc 0 T)) (s : Feec.BGG.ExactWave bggSegment T (srcFun f)) {L : ℝ},
      0 ≤ L →
      (∀ t ∈ Icc 0 T, ∀ K0 K1 : ℝ,
        (cubeFEM hT hB N).strangData (s.σ t) (s.φ t) (s.u t) (s.M t) (s.ρ t) K0 K1 ≤
          interpConst C * (L * meshSize N) ^ 2 + K0 ^ 2 + K1 ^ 2 ∧
        (cubeFEM hT hB N).strangData (s.σ' t) (s.φ' t) (s.u' t) (s.M' t) (s.ρ' t) K0 K1 ≤
          interpConst C * (L * meshSize N) ^ 2 + K0 ^ 2 + K1 ^ 2) →
      (∀ t ∈ Icc 0 T,
        (‖s.M t‖ ≤ (1 + Fintype.card (formIdx 3 1) * 3 + Fintype.card (formIdx 3 2)) * L ∧
          ∀ w : U1, |⟪s.M t, bggSegment.d1 w⟫| ≤ ((1 + Fintype.card (formIdx 3 1) * 3 + Fintype.card (formIdx 3 2)) * L) * ‖w‖) ∧
        (‖s.M' t‖ ≤ (1 + Fintype.card (formIdx 3 1) * 3 + Fintype.card (formIdx 3 2)) * L ∧
          ∀ w : U1, |⟪s.M' t, bggSegment.d1 w⟫| ≤ ((1 + Fintype.card (formIdx 3 1) * 3 + Fintype.card (formIdx 3 2)) * L) * ‖w‖)) →
      (∀ t ∈ Icc 0 T, ∀ μ : U1, |s.ℓ t μ| ≤ L * ‖μ‖ ∧ |s.ℓ' t μ| ≤ L * ‖μ‖) →
      ∃ sh : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N f),
        (sh.σ 0, sh.u 0, sh.M 0, sh.ρ 0) =
          (Feec.BGG.ellipticProjection (cubeWave hT hB N) (cubeWave_dt0_injective hT hB N)
            (Feec.BGG.exists_sub_eq_of_surjective (cubeWave_S0_surjective hT hB N))
            (Feec.BGG.ellipticRhs ((cubeFEM hT hB N).ellipticDataH (s.σ 0) (s.φ 0) (s.u 0)
              (s.M 0) (s.ρ 0) (s.ℓ 0)) 0)).1.1 ∧
        ∀ t ∈ Icc 0 T, √(‖s.σ t - sh.σ t‖ ^ 2 + ‖s.u t - sh.u t‖ ^ 2 +
          ‖s.M t - sh.M t‖ ^ 2 + ‖s.ρ t - sh.ρ t‖ ^ 2) ≤ K * L * (1 + t) * meshSize N := by
  have hh0 := cubeFEM_happ0 hT hB
  obtain ⟨C0, hh1⟩ := hh0
  have hC00 := hh1.1
  have hhapp := hh1.2
  have hC := hT.two_mul_nonneg
  have hreg := regConst_nonneg hT
  have Capp_ex : ∃ x : ℝ, x = C0 + regConst C := ⟨_, rfl⟩
  obtain ⟨Capp, hCapp_def⟩ := Capp_ex
  have hCapp0 : 0 ≤ Capp := by rw [hCapp_def]; linarith
  have Cp_ex : ∃ x : ℝ, x = (2 * Real.pi)⁻¹ := ⟨_, rfl⟩
  obtain ⟨Cp, hCp⟩ := Cp_ex
  have hCp0 : 0 ≤ Cp := by rw [hCp]; positivity
  have wa_ex : ∃ x : ℝ, x = √(1 + Cp ^ 2) * (1 + 2 * C * (1 + 1 * CR)) := ⟨_, rfl⟩
  obtain ⟨wa, hwa⟩ := wa_ex
  have wb_ex : ∃ x : ℝ, x = (1 + (1 + 2 * C) * Real.sqrt 2) * CR := ⟨_, rfl⟩
  obtain ⟨wb, hwb⟩ := wb_ex
  have hwa0 : 0 ≤ wa := by rw [hwa]; positivity
  have hwb0 : 0 ≤ wb := by rw [hwb]; positivity
  have cM_ex : ∃ x : ℝ,
      x = 1 + Fintype.card (formIdx 3 1) * 3 + Fintype.card (formIdx 3 2) := ⟨_, rfl⟩
  obtain ⟨cM, hcM⟩ := cM_ex
  have hcM0 : 0 ≤ cM := by rw [hcM]; positivity
  have Kd_ex : ∃ x : ℝ,
      x = interpConst C + Capp ^ 2 + (Capp * ((wa + wb) * cM)) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Kd, hKd⟩ := Kd_ex
  have hKd0 : 0 ≤ Kd := by rw [hKd]; have := interpConst_nonneg C; positivity
  have Ks_ex : ∃ x : ℝ, x = √(2 * (Feec.BGG.Discrete.strangConst Cp + 1)) := ⟨_, rfl⟩
  obtain ⟨Ks, hKs⟩ := Ks_ex
  have hKs0 : 0 ≤ Ks := by rw [hKs]; positivity
  refine ⟨2 * Ks * √Kd, by positivity, fun N T hT0 f hf s L hL0 hdat hM hmult => ?_⟩
  have hh : 0 ≤ meshSize N := (meshSize_pos N).le
  have H : Feec.BGG.Stability bggSegment Cp CR (Real.sqrt 2) := by
    rw [hCp]; exact bggStability_of hCR0 hCR
  have Bd := cubeFEM_bounded hT hB N
  have h54 := cubeFEM_compatible hT hB N
  have happ : ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
      ‖bggSegment.S0 ψ - (cubeFEM hT hB N).S0h ψ‖ ^ 2 ≤
        (Capp * meshSize N) ^ 2 * Feec.BGG.graphSq bggSegment.dt0 ψ := fun ψ hψ => by
    refine (hhapp N ψ hψ).trans (mul_le_mul_of_nonneg_right ?_ (Feec.BGG.graphSq_nonneg _ _))
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right
      (by rw [hCapp_def]; linarith) hh) 2
  have Rg := cubeFEMReg hT hB N hCR0 hCR (by rw [hCapp_def]; linarith : regConst C ≤ Capp)
  have hK0 : ∀ ℓ : U1 →ₗ[ℝ] ℝ, (∀ μ, |ℓ μ| ≤ L * ‖μ‖) → ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
      |ℓ ((bggSegment.S0 - (cubeFEM hT hB N).S0h) ψ)| ≤
        (L * Capp * meshSize N) * √(Feec.BGG.graphSq bggSegment.dt0 ψ) := fun ℓ hℓ =>
    Feec.BGG.Discrete.consistency_S0_of_approx hh hCapp0 hL0 ℓ hℓ happ
  have hK1 : ∀ z : W2, (‖z‖ ≤ (1 + Fintype.card (formIdx 3 1) * 3 + Fintype.card (formIdx 3 2)) * L ∧
        ∀ w : U1, |⟪z, bggSegment.d1 w⟫| ≤ ((1 + Fintype.card (formIdx 3 1) * 3 + Fintype.card (formIdx 3 2)) * L) * ‖w‖) → ∀ v ∈ (cubeFEM hT hB N).Vt1h,
      |⟪z, (bggSegment.S1 - (cubeFEM hT hB N).S1h) v⟫| ≤
        (Capp * meshSize N * ((wa + wb) * (cM * L))) * √((cubeFEM hT hB N).gnSq v) := by
    intro z hz v hv
    obtain ⟨hzn, hzd⟩ := hz
    rw [← hcM] at hzn hzd
    have hw := Feec.BGG.Discrete.weakConsistency_of_regularPotential_of_bound H Bd hh hCapp0 Rg
      happ (by positivity) hzd v hv
    have hwc : Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1 CR (‖z‖)
        (cM * L) ≤ (wa + wb) * (cM * L) := by
      have e : Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1 CR (‖z‖)
          (cM * L) = (cM * L) * wa + ‖z‖ * wb := by
        rw [hwa, hwb]; unfold Feec.BGG.Discrete.weakConsistencyConst; ring
      rw [e]; nlinarith
    have hwc0 : 0 ≤ Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1 CR (‖z‖)
        (cM * L) := Feec.BGG.Discrete.weakConsistencyConst_nonneg hCp0 (Real.sqrt_nonneg _) hC
          zero_le_one hCR0 (norm_nonneg _) (by positivity)
    refine hw.trans ?_
    have hg := Feec.BGG.Discrete.sqrt_graphSq_le_sqrt_gnSq (Q := cubeFEM hT hB N) v
    have hm : 0 ≤ Capp * meshSize N := by positivity
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwc hm)
      (Real.sqrt_nonneg (Feec.BGG.graphSq bggSegment.dt1 v))
    have h2 := mul_le_mul_of_nonneg_left hg
      (by positivity : 0 ≤ Capp * meshSize N * ((wa + wb) * (cM * L)))
    exact h1.trans h2
  have hdata : ∀ {σ : U0} {φ : Wv U0} {u : Wv U1} {M : W2} {ρ : Wv W2},
      (∀ K0 K1 : ℝ, (cubeFEM hT hB N).strangData σ φ u M ρ K0 K1 ≤
        interpConst C * (L * meshSize N) ^ 2 + K0 ^ 2 + K1 ^ 2) →
      (cubeFEM hT hB N).strangData σ φ u M ρ (L * Capp * meshSize N)
        (Capp * meshSize N * ((wa + wb) * (cM * L))) ≤ (√Kd * L * meshSize N) ^ 2 := by
    intro σ φ u M ρ hs
    refine (hs _ _).trans (le_of_eq ?_)
    rw [show (√Kd * L * meshSize N) ^ 2 = √Kd ^ 2 * (L * meshSize N) ^ 2 by ring,
      Real.sq_sqrt hKd0, hKd]
    ring
  have hrate := s.exists_discreteSolution_rate (cubeFEM hT hB N) H h54
    (K0 := L * Capp * meshSize N) (K1 := Capp * meshSize N * ((wa + wb) * (cM * L)))
    (c := √Kd * L) (h := meshSize N) (cubeWave_S0_surjective hT hB N) hT0
    (continuousOn_cubeSource hT hB N hf) (fun t _ v => (inner_cubeSource hT hB N f t v).symm)
    (fun t ht => hK0 (s.ℓ t) fun μ => (hmult t ht μ).1)
    (fun t ht => hK0 (s.ℓ' t) fun μ => (hmult t ht μ).2)
    (fun t ht => hK1 (s.M t) (hM t ht).1) (fun t ht => hK1 (s.M' t) (hM t ht).2)
    (fun t ht => hdata fun K0 K1 => (hdat t ht K0 K1).1)
    (fun t ht => hdata fun K0 K1 => (hdat t ht K0 K1).2)
  obtain ⟨sh, h0, hb⟩ := hrate
  refine ⟨sh, h0, fun t ht => (hb t ht).trans (le_of_eq ?_)⟩
  rw [abs_of_nonneg (by positivity : 0 ≤ √Kd * L), abs_of_nonneg hh, ← hKs]
  ring


theorem cubeFEM_err_P2_tr (N : ℕ) {L : ℝ} (hL0 : 0 ≤ L) (z : W2) (hz : IsCsFormTr 0 2 L z) :
    ‖(cubeFEM hT hB N).P2 z - z‖ ^ 2 ≤
      ((1 + 2 * C) * polyInterpBound 3 PolySeq.lowestOrder 2) ^ 2 * (L * meshSize N) ^ 2 := by
  have hA : 0 ≤ 1 + 2 * C := by linarith [hT.two_mul_nonneg]
  obtain ⟨v, hv, hv1, -⟩ := hz.exists_mem_polyMin_le (S := PolySeq.lowestOrder)
    ((polyOrder_zero _).polyOrderAt 2) hL0 N
  have h' : ‖(cubeFEM hT hB N).P2 z - z‖ ≤
      (1 + 2 * C) * (polyInterpBound 3 PolySeq.lowestOrder 2 * L * meshSize N) := by
    rw [norm_sub_rev]
    change ‖z - (hT.proj N).π 2 z‖ ≤ _
    refine (norm_sub_π_le_of_mem (hT.proj N) (hT.norm_proj_le N 2) hv).trans
      (mul_le_mul_of_nonneg_left ?_ hA)
    simpa using hv1
  have := pow_le_pow_left₀ (norm_nonneg _) h' 2
  nlinarith

theorem cubeFEM_err_Pt2_tr (N : ℕ) {L : ℝ} (hL0 : 0 ≤ L) (ρ : Wv W2)
    (hρ : ∀ a, IsCsFormTr 0 2 L (ρ a)) :
    ‖(cubeFEM hT hB N).Pt2 ρ - ρ‖ ^ 2 ≤
      3 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 2) ^ 2 * (L * meshSize N) ^ 2 := by
  have hA : 0 ≤ 1 + 2 * C := by linarith [hT.two_mul_nonneg]
  have hc : ∀ a, ‖((cubeFEM hT hB N).Pt2 ρ - ρ) a‖ ^ 2 ≤
      ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 2) ^ 2 * (L * meshSize N) ^ 2 := by
    intro a
    obtain ⟨v, hv, hv1, -⟩ := (hρ a).exists_mem_polyMin_le (S := PolySeq.lagrangeP2)
      ((polyOrder_zero _).polyOrderAt 2) hL0 N
    have h' : ‖((cubeFEM hT hB N).Pt2 ρ - ρ) a‖ ≤
        (1 + 2 * C) * (polyInterpBound 3 PolySeq.lagrangeP2 2 * L * meshSize N) := by
      rw [PiLp.sub_apply, norm_sub_rev]
      change ‖ρ a - (hB.proj N).π 2 (ρ a)‖ ≤ _
      refine (norm_sub_π_le_of_mem (hB.proj N) (hB.norm_proj_le N 2) hv).trans
        (mul_le_mul_of_nonneg_left ?_ hA)
      simpa using hv1
    have := pow_le_pow_left₀ (norm_nonneg _) h' 2
    nlinarith
  rw [norm_sq_wv]
  calc ∑ a, ‖((cubeFEM hT hB N).Pt2 ρ - ρ) a‖ ^ 2 ≤
      ∑ _a : Fin 3, ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 2) ^ 2 *
        (L * meshSize N) ^ 2 := Finset.sum_le_sum fun a _ => hc a
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- All components are `C²` up to `∂Q`, with vanishing tangential traces and bound `L`. -/
def IsSmoothStateTr (L : ℝ) (σ : U0) (φ : Wv U0) (u : Wv U1) (M : W2) (ρ : Wv W2) : Prop :=
  IsCsFormTr 0 0 L (σ : W0) ∧ (∀ a, IsCsFormTr 0 0 L (φ a : W0)) ∧
    (∀ a, IsCsFormTr 0 1 L (u a : W1)) ∧ IsCsFormTr 0 2 L M ∧ ∀ a, IsCsFormTr 0 2 L (ρ a)

theorem IsSmoothStateTr.isCsFormTr_M {L : ℝ} {σ : U0} {φ : Wv U0} {u : Wv U1} {M : W2}
    {ρ : Wv W2} (h : IsSmoothStateTr L σ φ u M ρ) : IsCsFormTr 0 2 L M := h.2.2.2.1

theorem IsSmoothStateTr.mono {L L' : ℝ} {σ : U0} {φ : Wv U0} {u : Wv U1} {M : W2}
    {ρ : Wv W2} (h : IsSmoothStateTr L σ φ u M ρ) (hLL' : L ≤ L') :
    IsSmoothStateTr L' σ φ u M ρ :=
  ⟨h.1.mono hLL', fun a => (h.2.1 a).mono hLL', fun a => (h.2.2.1 a).mono hLL',
    h.2.2.2.1.mono hLL', fun a => (h.2.2.2.2 a).mono hLL'⟩

theorem IsSmoothState.isSmoothStateTr {L : ℝ} {σ : U0} {φ : Wv U0} {u : Wv U1} {M : W2}
    {ρ : Wv W2} (h : IsSmoothState L σ φ u M ρ) : IsSmoothStateTr L σ φ u M ρ :=
  ⟨h.1.isCsFormTr, fun a => (h.2.1 a).isCsFormTr, fun a => (h.2.2.1 a).isCsFormTr,
    h.2.2.2.2.1.isCsFormTr, fun a => (h.2.2.2.2.2 a).isCsFormTr⟩

/-- A state of `IsSmoothStateTr` with `S¹u` in the same class, at the same bound. -/
def IsSmoothStateTrS1 (L : ℝ) (σ : U0) (φ : Wv U0) (u : Wv U1) (M : W2) (ρ : Wv W2) : Prop :=
  IsSmoothStateTr L σ φ u M ρ ∧ IsCsFormTr 0 2 L (bggSegment.S1 u)

theorem exists_isSmoothStateTrS1 : ∃ c : ℝ, 1 ≤ c ∧ ∀ {L : ℝ} {σ : U0} {φ : Wv U0} {u : Wv U1}
    {M : W2} {ρ : Wv W2}, 0 ≤ L → IsSmoothStateTr L σ φ u M ρ →
      IsSmoothStateTrS1 (c * L) σ φ u M ρ := by
  obtain ⟨c, hc1, hc⟩ := exists_isCsFormTr_segS1
  exact ⟨c, hc1, fun hL0 h => ⟨h.mono (le_mul_of_one_le_left hL0 hc1), hc _ hL0 h.2.2.1⟩⟩

set_option maxHeartbeats 2000000 in
theorem cubeFEM_strangData_le_tr (N : ℕ) {L : ℝ} (hL0 : 0 ≤ L) {σ : U0} {φ : Wv U0} {u : Wv U1}
    {M : W2} {ρ : Wv W2} (hs : IsSmoothStateTrS1 L σ φ u M ρ) (K0 K1 : ℝ) :
    (cubeFEM hT hB N).strangData σ φ u M ρ K0 K1 ≤
      interpConst C * (L * meshSize N) ^ 2 + K0 ^ 2 + K1 ^ 2 := by
  obtain ⟨⟨hσ, hφ, hu, hM, hρ⟩, hSu⟩ := hs
  have h1 := cubeFEM_err_P0_tr hT hB N hL0 σ hσ
  have h2 := cubeFEM_err_Pt0_tr hT hB N hL0 φ hφ
  have h3 := cubeFEM_err_gnSq_tr hT hB N hL0 u hu
  have h4 := cubeFEM_err_P2_tr hT hB N hL0 M hM
  have h5 := cubeFEM_err_Pt2_tr hT hB N hL0 ρ hρ
  have h6 := cubeFEM_err_S1_tr hT hB N hL0 u hSu
  have g1 : ‖(cubeFEM hT hB N).P0 σ - σ‖ ^ 2 ≤
      Feec.BGG.graphSq bggSegment.d0 ((cubeFEM hT hB N).P0 σ - σ) := by
    unfold Feec.BGG.graphSq; nlinarith [sq_nonneg ‖bggSegment.d0 ((cubeFEM hT hB N).P0 σ - σ)‖]
  have g2 : ‖bggSegment.dt0 ((cubeFEM hT hB N).Pt0 φ - φ)‖ ^ 2 ≤
      Feec.BGG.graphSq bggSegment.dt0 ((cubeFEM hT hB N).Pt0 φ - φ) := by
    unfold Feec.BGG.graphSq; nlinarith [sq_nonneg ‖(cubeFEM hT hB N).Pt0 φ - φ‖]
  have e1 : (cubeFEM hT hB N).strangData σ φ u M ρ K0 K1 =
      ‖(cubeFEM hT hB N).P0 σ - σ‖ ^ 2 + ‖bggSegment.dt0 ((cubeFEM hT hB N).Pt0 φ - φ)‖ ^ 2 +
        (cubeFEM hT hB N).gnSq ((cubeFEM hT hB N).Pt1 u - u) +
        ‖(cubeFEM hT hB N).P2 M - M‖ ^ 2 + ‖(cubeFEM hT hB N).Pt2 ρ - ρ‖ ^ 2 + K0 ^ 2 + K1 ^ 2 +
        ‖bggSegment.S1 u - (cubeFEM hT hB N).S1h u‖ ^ 2 := rfl
  have e2 : interpConst C * (L * meshSize N) ^ 2 =
      2 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lowestOrder 0) ^ 2 * (L * meshSize N) ^ 2 +
      3 * (2 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 0) ^ 2) *
        (L * meshSize N) ^ 2 +
      (1 + 8 * C ^ 2) * (3 * (2 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 1) ^ 2)) *
        (L * meshSize N) ^ 2 +
      ((1 + 2 * C) * polyInterpBound 3 PolySeq.lowestOrder 2) ^ 2 * (L * meshSize N) ^ 2 +
      3 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 2) ^ 2 * (L * meshSize N) ^ 2 +
      ((1 + 2 * C) * polyInterpBound 3 PolySeq.lowestOrder 2) ^ 2 * (L * meshSize N) ^ 2 := by
    unfold interpConst; ring
  rw [e1, e2]
  linarith

theorem _root_.Feec.Models.Cube.FEM.IsCsFormTr.bounds_two {L : ℝ} (hL0 : 0 ≤ L) {z : W2}
    (hz : IsCsFormTr 0 2 L z) :
    ‖z‖ ≤ (1 + Fintype.card (formIdx 3 1) * 3 + Fintype.card (formIdx 3 2)) * L ∧
      ∀ w : U1, |⟪z, bggSegment.d1 w⟫| ≤
        ((1 + Fintype.card (formIdx 3 1) * 3 + Fintype.card (formIdx 3 2)) * L) * ‖w‖ := by
  have hc1 : (0 : ℝ) ≤ Fintype.card (formIdx 3 1) := Nat.cast_nonneg _
  have hc2 : (0 : ℝ) ≤ Fintype.card (formIdx 3 2) := Nat.cast_nonneg _
  refine ⟨(hz.norm_le hL0).trans (by nlinarith), fun w => (hz.abs_inner_D1_le hL0 w).trans
    (mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _))⟩


set_option maxHeartbeats 4000000 in
theorem cubeFEM_ellipticProjection_rate_trS1 {CR : ℝ} (hCR0 : 0 ≤ CR)
    (hCR : ∀ u : V1, ∃ φ : Vt0, bggD1 (bggS0 φ) = bggD1 u ∧ ‖φ‖ ≤ CR * ‖bggD1 u‖) :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {σ : U0} {φ : Wv U0} {u : Wv U1} {M : W2} {ρ : Wv W2}
      (ℓ : U1 →ₗ[ℝ] ℝ) {L : ℝ}, 0 ≤ L → bggSegment.d0 σ = bggSegment.S0 φ →
      (∀ μ, |ℓ μ| ≤ L * ‖μ‖) → IsSmoothStateTrS1 L σ φ u M ρ →
      ∀ {x : (((cubeFEM hT hB N).V0h × (cubeFEM hT hB N).Vt1h × (cubeFEM hT hB N).W2h ×
          (cubeFEM hT hB N).Wt2h) × (cubeFEM hT hB N).Vt0h) × (cubeFEM hT hB N).V1h},
      Feec.BGG.IsEllipticProjection (cubeFEM hT hB N).toSegmentH
        ((cubeFEM hT hB N).ellipticDataH σ φ u M ρ ℓ) 0 x →
      √(‖σ - x.1.1.1‖ ^ 2 + ‖u - x.1.1.2.1‖ ^ 2 + ‖M - x.1.1.2.2.1‖ ^ 2 +
        ‖ρ - x.1.1.2.2.2‖ ^ 2) ≤ K * L * meshSize N := by
  have hh0 := cubeFEM_happ0 hT hB
  obtain ⟨C0, hh1⟩ := hh0
  have hC00 := hh1.1
  have hhapp := hh1.2
  have hC := hT.two_mul_nonneg
  have hreg := regConst_nonneg hT
  have Capp_ex : ∃ x : ℝ, x = C0 + regConst C := ⟨_, rfl⟩
  obtain ⟨Capp, hCapp_def⟩ := Capp_ex
  have hCapp0 : 0 ≤ Capp := by rw [hCapp_def]; linarith
  have Cp_ex : ∃ x : ℝ, x = (2 * Real.pi)⁻¹ := ⟨_, rfl⟩
  obtain ⟨Cp, hCp⟩ := Cp_ex
  have hCp0 : 0 ≤ Cp := by rw [hCp]; positivity
  have wa_ex : ∃ x : ℝ, x = √(1 + Cp ^ 2) * (1 + 2 * C * (1 + 1 * CR)) := ⟨_, rfl⟩
  obtain ⟨wa, hwa⟩ := wa_ex
  have wb_ex : ∃ x : ℝ, x = (1 + (1 + 2 * C) * Real.sqrt 2) * CR := ⟨_, rfl⟩
  obtain ⟨wb, hwb⟩ := wb_ex
  have hwa0 : 0 ≤ wa := by rw [hwa]; positivity
  have hwb0 : 0 ≤ wb := by rw [hwb]; positivity
  have cM_ex : ∃ x : ℝ,
      x = 1 + Fintype.card (formIdx 3 1) * 3 + Fintype.card (formIdx 3 2) := ⟨_, rfl⟩
  obtain ⟨cM, hcM⟩ := cM_ex
  have hcM0 : 0 ≤ cM := by rw [hcM]; positivity
  have Kd_ex : ∃ x : ℝ,
      x = interpConst C + Capp ^ 2 + (Capp * ((wa + wb) * cM)) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Kd, hKd⟩ := Kd_ex
  have hKd0 : 0 ≤ Kd := by rw [hKd]; have := interpConst_nonneg C; positivity
  have Ks_ex : ∃ x : ℝ, x = √(2 * (Feec.BGG.Discrete.strangConst Cp + 1)) := ⟨_, rfl⟩
  obtain ⟨Ks, hKs⟩ := Ks_ex
  have hKs0 : 0 ≤ Ks := by rw [hKs]; positivity
  refine ⟨Ks * √Kd, by positivity, fun N σ φ u M ρ ℓ L hL0 c3 hℓ hs x hx => ?_⟩
  have hh : 0 ≤ meshSize N := (meshSize_pos N).le
  have H : Feec.BGG.Stability bggSegment Cp CR (Real.sqrt 2) := by
    rw [hCp]; exact bggStability_of hCR0 hCR
  have Bd := cubeFEM_bounded hT hB N
  have h54 := cubeFEM_compatible hT hB N
  have happ : ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
      ‖bggSegment.S0 ψ - (cubeFEM hT hB N).S0h ψ‖ ^ 2 ≤
        (Capp * meshSize N) ^ 2 * Feec.BGG.graphSq bggSegment.dt0 ψ := fun ψ hψ => by
    refine (hhapp N ψ hψ).trans (mul_le_mul_of_nonneg_right ?_ (Feec.BGG.graphSq_nonneg _ _))
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right
      (by rw [hCapp_def]; linarith) hh) 2
  have Rg := cubeFEMReg hT hB N hCR0 hCR (by rw [hCapp_def]; linarith : regConst C ≤ Capp)
  have hK0 : ∀ ℓ : U1 →ₗ[ℝ] ℝ, (∀ μ, |ℓ μ| ≤ L * ‖μ‖) → ∀ ψ ∈ (cubeFEM hT hB N).Vt0h,
      |ℓ ((bggSegment.S0 - (cubeFEM hT hB N).S0h) ψ)| ≤
        (L * Capp * meshSize N) * √(Feec.BGG.graphSq bggSegment.dt0 ψ) := fun ℓ hℓ =>
    Feec.BGG.Discrete.consistency_S0_of_approx hh hCapp0 hL0 ℓ hℓ happ
  have hK1 : ∀ z : W2, IsCsFormTr 0 2 L z → ∀ v ∈ (cubeFEM hT hB N).Vt1h,
      |⟪z, (bggSegment.S1 - (cubeFEM hT hB N).S1h) v⟫| ≤
        (Capp * meshSize N * ((wa + wb) * (cM * L))) * √((cubeFEM hT hB N).gnSq v) := by
    intro z hz v hv
    obtain ⟨hzn, hzd⟩ := hz.bounds_two hL0
    rw [← hcM] at hzn hzd
    have hw := Feec.BGG.Discrete.weakConsistency_of_regularPotential_of_bound H Bd hh hCapp0 Rg
      happ (by positivity) hzd v hv
    have hwc : Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1 CR (‖z‖)
        (cM * L) ≤ (wa + wb) * (cM * L) := by
      have e : Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1 CR (‖z‖)
          (cM * L) = (cM * L) * wa + ‖z‖ * wb := by
        rw [hwa, hwb]; unfold Feec.BGG.Discrete.weakConsistencyConst; ring
      rw [e]; nlinarith
    have hwc0 : 0 ≤ Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1 CR (‖z‖)
        (cM * L) := Feec.BGG.Discrete.weakConsistencyConst_nonneg hCp0 (Real.sqrt_nonneg _) hC
          zero_le_one hCR0 (norm_nonneg _) (by positivity)
    refine hw.trans ?_
    have hg := Feec.BGG.Discrete.sqrt_graphSq_le_sqrt_gnSq (Q := cubeFEM hT hB N) v
    have hm : 0 ≤ Capp * meshSize N := by positivity
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwc hm)
      (Real.sqrt_nonneg (Feec.BGG.graphSq bggSegment.dt1 v))
    have h2 := mul_le_mul_of_nonneg_left hg
      (by positivity : 0 ≤ Capp * meshSize N * ((wa + wb) * (cM * L)))
    exact h1.trans h2
  have hdata : (cubeFEM hT hB N).strangData σ φ u M ρ (L * Capp * meshSize N)
        (Capp * meshSize N * ((wa + wb) * (cM * L))) ≤ (√Kd * L * meshSize N) ^ 2 := by
    refine (cubeFEM_strangData_le_tr hT hB N hL0 hs _ _).trans (le_of_eq ?_)
    rw [show (√Kd * L * meshSize N) ^ 2 = √Kd ^ 2 * (L * meshSize N) ^ 2 by ring,
      Real.sq_sqrt hKd0, hKd]
    ring
  have hS := (Feec.BGG.Discrete.strang_of_isEllipticProjection H h54 c3 ℓ (hK0 ℓ hℓ)
    (hK1 M hs.1.isCsFormTr_M) hx).2
  have hC2 : 0 ≤ 2 * (Feec.BGG.Discrete.strangConst Cp + 1) := by
    unfold Feec.BGG.Discrete.strangConst; positivity
  calc √(‖σ - x.1.1.1‖ ^ 2 + ‖u - x.1.1.2.1‖ ^ 2 + ‖M - x.1.1.2.2.1‖ ^ 2 +
        ‖ρ - x.1.1.2.2.2‖ ^ 2) ≤
        √(2 * (Feec.BGG.Discrete.strangConst Cp + 1) * (√Kd * L * meshSize N) ^ 2) :=
        Real.sqrt_le_sqrt (hS.trans (mul_le_mul_of_nonneg_left hdata hC2))
    _ = Ks * √Kd * L * meshSize N := by
        rw [Real.sqrt_mul hC2, Real.sqrt_sq (by positivity), ← hKs]; ring

set_option maxHeartbeats 1000000 in
theorem cubeFEM_ellipticProjection_rate_tr {CR : ℝ} (hCR0 : 0 ≤ CR)
    (hCR : ∀ u : V1, ∃ φ : Vt0, bggD1 (bggS0 φ) = bggD1 u ∧ ‖φ‖ ≤ CR * ‖bggD1 u‖) :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {σ : U0} {φ : Wv U0} {u : Wv U1} {M : W2} {ρ : Wv W2}
      (ℓ : U1 →ₗ[ℝ] ℝ) {L : ℝ}, 0 ≤ L → bggSegment.d0 σ = bggSegment.S0 φ →
      (∀ μ, |ℓ μ| ≤ L * ‖μ‖) → IsSmoothStateTr L σ φ u M ρ →
      ∀ {x : (((cubeFEM hT hB N).V0h × (cubeFEM hT hB N).Vt1h × (cubeFEM hT hB N).W2h ×
          (cubeFEM hT hB N).Wt2h) × (cubeFEM hT hB N).Vt0h) × (cubeFEM hT hB N).V1h},
      Feec.BGG.IsEllipticProjection (cubeFEM hT hB N).toSegmentH
        ((cubeFEM hT hB N).ellipticDataH σ φ u M ρ ℓ) 0 x →
      √(‖σ - x.1.1.1‖ ^ 2 + ‖u - x.1.1.2.1‖ ^ 2 + ‖M - x.1.1.2.2.1‖ ^ 2 +
        ‖ρ - x.1.1.2.2.2‖ ^ 2) ≤ K * L * meshSize N := by
  have hex := cubeFEM_ellipticProjection_rate_trS1 hT hB hCR0 hCR
  obtain ⟨K, hK⟩ := hex
  have hK0 := hK.1
  replace hK := hK.2
  obtain ⟨c, hc1, hc⟩ := exists_isSmoothStateTrS1
  refine ⟨K * c, mul_nonneg hK0 (by linarith), fun N σ φ u M ρ ℓ L hL0 c3 hℓ hs x hx => ?_⟩
  have hcL : L ≤ c * L := le_mul_of_one_le_left hL0 hc1
  refine (hK N ℓ (L := c * L) (mul_nonneg (by linarith) hL0) c3
    (fun μ => (hℓ μ).trans (mul_le_mul_of_nonneg_right hcL (norm_nonneg _))) (hc hL0 hs)
    hx).trans (le_of_eq ?_)
  ring

set_option maxHeartbeats 1000000 in
/-- **`O(h)` convergence of (6.5)**: given a constant `C_R` of `CurlPotential`, the error is
`K L (1 + t) h_N` for `IsSmoothStateTr L` states with `|ℓ μ| ≤ L ‖μ‖`. -/
theorem cubeWave_rate_tr {CR : ℝ} (hCR0 : 0 ≤ CR)
    (hCR : ∀ u : V1, ∃ φ : Vt0, bggD1 (bggS0 φ) = bggD1 u ∧ ‖φ‖ ≤ CR * ‖bggD1 u‖) :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {T : ℝ} (_hT0 : 0 < T) {f : ℝ → Wv W1}
      (_hf : ContinuousOn f (Icc 0 T)) (s : Feec.BGG.ExactWave bggSegment T (srcFun f)) {L : ℝ},
      0 ≤ L →
      (∀ t ∈ Icc 0 T, IsSmoothStateTr L (s.σ t) (s.φ t) (s.u t) (s.M t) (s.ρ t) ∧
        IsSmoothStateTr L (s.σ' t) (s.φ' t) (s.u' t) (s.M' t) (s.ρ' t)) →
      (∀ t ∈ Icc 0 T, ∀ μ : U1, |s.ℓ t μ| ≤ L * ‖μ‖ ∧ |s.ℓ' t μ| ≤ L * ‖μ‖) →
      ∃ sh : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N f),
        (sh.σ 0, sh.u 0, sh.M 0, sh.ρ 0) =
          (Feec.BGG.ellipticProjection (cubeWave hT hB N) (cubeWave_dt0_injective hT hB N)
            (Feec.BGG.exists_sub_eq_of_surjective (cubeWave_S0_surjective hT hB N))
            (Feec.BGG.ellipticRhs ((cubeFEM hT hB N).ellipticDataH (s.σ 0) (s.φ 0) (s.u 0)
              (s.M 0) (s.ρ 0) (s.ℓ 0)) 0)).1.1 ∧
        ∀ t ∈ Icc 0 T, √(‖s.σ t - sh.σ t‖ ^ 2 + ‖s.u t - sh.u t‖ ^ 2 +
          ‖s.M t - sh.M t‖ ^ 2 + ‖s.ρ t - sh.ρ t‖ ^ 2) ≤ K * L * (1 + t) * meshSize N := by
  have hc := exists_isSmoothStateTrS1
  have hK := cubeWave_rate_of_bounds hT hB hCR0 hCR
  have hcS0 : 0 ≤ hc.choose := by linarith [hc.choose_spec.1]
  refine ⟨hK.choose * hc.choose, mul_nonneg hK.choose_spec.1 hcS0,
    fun N T hT0 f hf s L hL0 hsm hmult => ?_⟩
  have hL0' : 0 ≤ hc.choose * L := mul_nonneg hcS0 hL0
  have hLL : L ≤ hc.choose * L := le_mul_of_one_le_left hL0 hc.choose_spec.1
  have hs := fun t (ht : t ∈ Icc 0 T) =>
    And.intro (hc.choose_spec.2 hL0 (hsm t ht).1) (hc.choose_spec.2 hL0 (hsm t ht).2)
  have H := hK.choose_spec.2 N hT0 hf s hL0'
    (fun t ht K0 K1 => ⟨cubeFEM_strangData_le_tr hT hB N hL0' (hs t ht).1 K0 K1,
      cubeFEM_strangData_le_tr hT hB N hL0' (hs t ht).2 K0 K1⟩)
    (fun t ht => ⟨(hs t ht).1.1.isCsFormTr_M.bounds_two hL0',
      (hs t ht).2.1.isCsFormTr_M.bounds_two hL0'⟩)
    (fun t ht μ => ⟨(hmult t ht μ).1.trans (mul_le_mul_of_nonneg_right hLL (norm_nonneg _)),
      (hmult t ht μ).2.trans (mul_le_mul_of_nonneg_right hLL (norm_nonneg _))⟩)
  exact ⟨H.choose, H.choose_spec.1, fun t ht =>
    (H.choose_spec.2 t ht).trans (le_of_eq (by ring))⟩

set_option maxHeartbeats 1000000 in
theorem cubeWave_rate {CR : ℝ} (hCR0 : 0 ≤ CR)
    (hCR : ∀ u : V1, ∃ φ : Vt0, bggD1 (bggS0 φ) = bggD1 u ∧ ‖φ‖ ≤ CR * ‖bggD1 u‖) :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {T : ℝ} (_hT0 : 0 < T) {f : ℝ → Wv W1}
      (_hf : ContinuousOn f (Icc 0 T)) (s : Feec.BGG.ExactWave bggSegment T (srcFun f)) {L : ℝ},
      0 ≤ L →
      (∀ t ∈ Icc 0 T, IsSmoothState L (s.σ t) (s.φ t) (s.u t) (s.M t) (s.ρ t) ∧
        IsSmoothState L (s.σ' t) (s.φ' t) (s.u' t) (s.M' t) (s.ρ' t)) →
      (∀ t ∈ Icc 0 T, ∀ μ : U1, |s.ℓ t μ| ≤ L * ‖μ‖ ∧ |s.ℓ' t μ| ≤ L * ‖μ‖) →
      ∃ sh : Feec.BGG.DiscreteSolution (cubeWave hT hB N) T (cubeSource hT hB N f),
        (sh.σ 0, sh.u 0, sh.M 0, sh.ρ 0) =
          (Feec.BGG.ellipticProjection (cubeWave hT hB N) (cubeWave_dt0_injective hT hB N)
            (Feec.BGG.exists_sub_eq_of_surjective (cubeWave_S0_surjective hT hB N))
            (Feec.BGG.ellipticRhs ((cubeFEM hT hB N).ellipticDataH (s.σ 0) (s.φ 0) (s.u 0)
              (s.M 0) (s.ρ 0) (s.ℓ 0)) 0)).1.1 ∧
        ∀ t ∈ Icc 0 T, √(‖s.σ t - sh.σ t‖ ^ 2 + ‖s.u t - sh.u t‖ ^ 2 +
          ‖s.M t - sh.M t‖ ^ 2 + ‖s.ρ t - sh.ρ t‖ ^ 2) ≤ K * L * (1 + t) * meshSize N := by
  have h := cubeWave_rate_tr hT hB hCR0 hCR
  refine ⟨h.choose, h.choose_spec.1, fun N T hT0 f hf s L hL0 hsm =>
    h.choose_spec.2 N hT0 hf s hL0 fun t ht =>
      ⟨(hsm t ht).1.isSmoothStateTr, (hsm t ht).2.isSmoothStateTr⟩⟩

end Rate

/-! ### A nontrivial classical solution of (6.2) on the cube (manufactured data) -/

section Manufactured

theorem _root_.Feec.Models.Cube.FEM.IsCsFormMin.smul {j : ℤ} {L : ℝ}
    {x : L2F ℝ (cubeDomain 3) (formIdx 3 j)} (hx : IsCsFormMin 0 j L x) (c : ℝ) :
    IsCsFormMin 0 j (|c| * L) (c • x) := by
  rcases hx with hj | ⟨k, hk, w, hw, hdeg, hsupp, hL, hL', rfl⟩
  · exact Or.inl hj
  · have hw' : ContDiff ℝ ((0 + 2 : ℕ) : WithTop ℕ∞) (c • w) := hw.const_smul c
    have hdw : extDeriv (c • w) = c • extDeriv w := funext fun y =>
      extDeriv_smul_const_apply c ((hw.differentiable (by norm_num)) y)
    have hw1 : ContDiff ℝ (((0 + 1 : ℕ) : WithTop ℕ∞) + 1) w := by exact_mod_cast hw
    have hdwc : ContDiff ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) (extDeriv w) := contDiff_extDeriv hw1
    have hc1 : ContDiff ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) w := hw.of_le (by exact_mod_cast Nat.le_succ 1)
    refine Or.inr ⟨k, hk, c • w, hw', fun y s hs => by simp [hdeg y s hs],
      fun y hy => by simp [hsupp y hy], fun y hy => ?_, fun y hy => ?_, ?_⟩
    · rw [iteratedFDeriv_const_smul_apply hc1.contDiffAt, norm_smul,
        Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hL y hy) (abs_nonneg c)
    · rw [hdw, iteratedFDeriv_const_smul_apply hdwc.contDiffAt, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hL' y hy) (abs_nonneg c)
    · rw [← map_smul]; rfl

/-- The rows of `curl u` of the coupled manufactured `u` (`uₐ = −g dxₐ`). -/
def waveCurlU (a : Fin 3) : formIdx 3 2 → (Fin 3 → ℝ) → ℝ :=
  (extDerivOp ℝ 3 1).apply (coupledU a)

theorem isTestField_waveCurlU (a : Fin 3) : IsTestField (cubeDomain 3) (waveCurlU a) :=
  (extDerivOp ℝ 3 1).isTestField_apply (isTestField_coupledU a)

theorem inner_D1_testField (x : U1) {ψ : formIdx 3 2 → (Fin 3 → ℝ) → ℝ}
    (hψ : IsTestField (cubeDomain 3) ψ) :
    ⟪D1 x, testField hψ⟫ =
      ⟪(x : W1), testField ((extDerivOp ℝ 3 1).formalAdj.isTestField_apply hψ)⟫ :=
  (extDerivOp ℝ 3 1).minimal_green (isOpen_cubeDomain 3) (extDerivOp_isOrderLE 1) x
    (fun r => contDiff_infty.1 (hψ r).contDiff 1) (fun r => (hψ r).memLp)
    (fun r => ((extDerivOp ℝ 3 1).formalAdj.isTestField_apply hψ r).memLp)

/-- `curl* curl u` for the coupled manufactured `u`, a test field in `H̊Λ¹(Q)³`. -/
def waveCurlCurlU : Wv U1 := WithLp.toLp 2 fun a =>
  ⟨testField ((extDerivOp ℝ 3 1).formalAdj.isTestField_apply (isTestField_waveCurlU a)),
    mem_D1_testField _⟩

theorem D1_coupledu (a : Fin 3) : D1 (coupledu a) = testField (isTestField_waveCurlU a) :=
  (extDerivOp ℝ 3 1).minimal_testField (isOpen_cubeDomain 3) (isTestField_coupledU a)

theorem inner_dt1_coupledu (v : Wv U1) :
    ⟪bggSegment.dt1 coupledu, bggSegment.dt1 v⟫ = ⟪waveCurlCurlU, v⟫ := by
  rw [inner_Vt, inner_Vt]
  refine Finset.sum_congr rfl fun a _ => ?_
  change ⟪D1 (coupledu a), D1 (v a)⟫ = ⟪((waveCurlCurlU a : U1) : W1), ((v a : U1) : W1)⟫
  rw [D1_coupledu, real_inner_comm, inner_D1_testField, real_inner_comm]
  rfl

theorem segS1_coupledu_eq_zero : bggSegment.S1 coupledu = 0 := by
  rw [segS1_coupledu]
  have e : wsFields (n := 3) 1 coupledU = 0 := by
    funext t y
    simp only [wsFields, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [wsCoeff_eq]
    by_cases h : p.1 ∈ t.1 ∧ t.1.erase p.1 = p.2.1
    · have hne : p.2.1 ≠ {p.1} := by
        rw [← h.2]; intro h'
        have : p.1 ∈ t.1.erase p.1 := by rw [h']; exact Finset.mem_singleton_self _
        simp at this
      simp [coupledU, hne]
    · simp [h]
  rw [testField_congr _ IsTestField.zero e, testField_zero]

/-- **A nontrivial classical solution of (6.2)**, with `u(t) = (−g dxₐ)ₐ` for a bump `g`. -/
def waveManufactured (T : ℝ) :
    Feec.BGG.ExactWave bggSegment T
      (srcFun fun t => incl1 (t • (bggSegment.dt0 coupledφ + waveCurlCurlU))) where
  σ t := t • coupledσ
  φ t := t • coupledφ
  u _ := coupledu
  M _ := 0
  ρ t := t • bggSegment.dt1 coupledu
  ℓ _ := (innerSL ℝ coupledMult).toLinearMap ∘ₗ D1.domain.subtype
  σ' _ := coupledσ
  φ' _ := coupledφ
  u' _ := 0
  M' _ := 0
  ρ' _ := bggSegment.dt1 coupledu
  ℓ' _ := 0
  cσ := (continuous_id.smul continuous_const).continuousOn
  cu := continuousOn_const
  cM := continuousOn_const
  cρ := (continuous_id.smul continuous_const).continuousOn
  cdφ := by simp only [map_smul]; exact Continuous.continuousOn (by fun_prop)
  cSu := continuousOn_const
  cdu := continuousOn_const
  cℓ _ := continuousOn_const
  cσ' := continuousOn_const
  cu' := continuousOn_const
  cM' := continuousOn_const
  cρ' := continuousOn_const
  cdφ' := continuousOn_const
  cSu' := continuousOn_const
  cdu' := continuousOn_const
  cℓ' _ := continuousOn_const
  dσ t _ := by simpa using ((hasDerivAt_id t).smul_const coupledσ).hasDerivWithinAt
  du t _ := hasDerivWithinAt_const _ _ _
  dM t _ := hasDerivWithinAt_const _ _ _
  dρ t _ := by
    simpa using ((hasDerivAt_id t).smul_const (bggSegment.dt1 coupledu)).hasDerivWithinAt
  ddφ t _ := by
    simpa using ((hasDerivAt_id t).smul_const (bggSegment.dt0 coupledφ)).hasDerivWithinAt
  dSu t _ := by simpa using hasDerivWithinAt_const t (Ici t) (bggSegment.S1 coupledu)
  ddu t _ := by simpa using hasDerivWithinAt_const t (Ici t) (bggSegment.dt1 coupledu)
  dℓ t _ μ := by simpa using hasDerivWithinAt_const t (Ici t) (⟪coupledMult, (μ : W1)⟫)
  ea _ _ τ ψ := coupled_c1 τ ψ
  eb t _ v := by
    rw [srcFun_apply, ← inner_wv_U1]
    simp only [map_smul, inner_smul_left, inner_add_left, inner_zero_left, zero_add,
      RCLike.conj_to_real, inner_dt1_coupledu]
    ring
  ec _ _ N := by simp [segS1_coupledu_eq_zero]
  ed _ _ μ := by simp
  ee t _ := by simp only [map_smul, coupled_c3]
  ee' _ _ := coupled_c3

theorem waveManufactured_mult (T t : ℝ) (μ : U1) :
    |(waveManufactured T).ℓ t μ| ≤ ‖coupledMult‖ * ‖μ‖ ∧
      |(waveManufactured T).ℓ' t μ| ≤ ‖coupledMult‖ * ‖μ‖ := by
  refine ⟨abs_real_inner_le_norm coupledMult (μ : W1), ?_⟩
  simp only [waveManufactured, LinearMap.zero_apply, abs_zero]
  positivity

set_option maxHeartbeats 1000000 in
theorem waveManufactured_hyps {T : ℝ} (hT : 0 < T) : ∃ L, 0 ≤ L ∧
    (∀ t ∈ Icc 0 T, IsSmoothState L ((waveManufactured T).σ t) ((waveManufactured T).φ t)
        ((waveManufactured T).u t) ((waveManufactured T).M t) ((waveManufactured T).ρ t) ∧
      IsSmoothState L ((waveManufactured T).σ' t) ((waveManufactured T).φ' t)
        ((waveManufactured T).u' t) ((waveManufactured T).M' t) ((waveManufactured T).ρ' t)) ∧
    (∀ t ∈ Icc 0 T, ∀ μ : U1, |(waveManufactured T).ℓ t μ| ≤ L * ‖μ‖ ∧
      |(waveManufactured T).ℓ' t μ| ≤ L * ‖μ‖) ∧
    (∀ t ∈ Ioc 0 T, (waveManufactured T).σ t ≠ 0 ∧ (waveManufactured T).φ t ≠ 0) ∧
    (∀ t, (waveManufactured T).u t ≠ 0) ∧ coupledMult ≠ 0 := by
  have ex := exists_coupled_manufactured_solution
  obtain ⟨L0, hL00, -, -, -, -, -, -, -, hσ, hφ, hu, hM, -⟩ := ex
  choose Lc hLc0 hLc using fun a => exists_isCsFormMin_testField (isTestField_waveCurlU a)
  obtain ⟨Lz, hLz0, hLz⟩ := isCsFormMin_zero (k := 2)
  obtain ⟨Lz0, hLz00, hLz0'⟩ := isCsFormMin_zero (k := 0)
  obtain ⟨Lz1, hLz10, hLz1'⟩ := isCsFormMin_zero (k := 1)
  have hc : ∀ a ∈ Finset.univ, 0 ≤ Lc a := fun a _ => hLc0 a
  have sc := Finset.sum_nonneg hc
  have L1_ex : ∃ x : ℝ, x = L0 + ∑ a, Lc a + Lz + Lz0 + Lz1 := ⟨_, rfl⟩
  obtain ⟨L1, hL1⟩ := L1_ex
  have hL10 : 0 ≤ L1 := by rw [hL1]; positivity
  have hle : ∀ a, Lc a ≤ L1 := fun a => by
    have := Finset.single_le_sum hc (Finset.mem_univ a); rw [hL1]; linarith
  have hL0le : L0 ≤ L1 := by rw [hL1]; linarith
  have hLzle : Lz ≤ L1 := by rw [hL1]; linarith
  have hLz1le : Lz1 ≤ L1 := by rw [hL1]; linarith
  have hρc : ∀ a, IsCsFormMin 0 2 L1 ((bggSegment.dt1 coupledu) a) := fun a => by
    change IsCsFormMin 0 2 L1 (D1 (coupledu a))
    rw [D1_coupledu]; exact (hLc a).mono (hle a)
  refine ⟨(1 + T) * L1, by positivity, fun t ht => ?_, fun t ht μ => ?_, fun t ht => ?_,
    fun _ => coupledu_ne_zero, coupledMult_ne_zero⟩
  · have hta : |t| ≤ 1 + T := by rw [abs_of_nonneg ht.1]; linarith [ht.2]
    have hmono : ∀ {j : ℤ} {x : L2F ℝ (cubeDomain 3) (formIdx 3 j)}, IsCsFormMin 0 j L1 x →
        IsCsFormMin 0 j ((1 + T) * L1) (t • x) := fun hx =>
      (hx.smul t).mono (mul_le_mul_of_nonneg_right hta hL10)
    have hmono1 : ∀ {j : ℤ} {x : L2F ℝ (cubeDomain 3) (formIdx 3 j)}, IsCsFormMin 0 j L1 x →
        IsCsFormMin 0 j ((1 + T) * L1) x := fun hx =>
      hx.mono (le_mul_of_one_le_left hL10 (by linarith))
    have hS0 : bggSegment.S1 (0 : Wv U1) = 0 := map_zero _
    refine ⟨⟨hmono (hσ.mono hL0le), fun a => hmono ((hφ a).mono hL0le),
      fun a => hmono1 ((hu a).mono hL0le), ?_, hmono1 (hLz.mono hLzle),
      fun a => hmono (hρc a)⟩, ⟨hmono1 (hσ.mono hL0le),
      fun a => hmono1 ((hφ a).mono hL0le), fun a => ?_, ?_,
      hmono1 (hLz.mono hLzle), fun a => hmono1 (hρc a)⟩⟩
    · change IsCsFormMin 0 2 ((1 + T) * L1) (bggSegment.S1 coupledu)
      rw [segS1_coupledu_eq_zero]; exact hmono1 (hLz.mono hLzle)
    · change IsCsFormMin 0 1 ((1 + T) * L1) (((0 : Wv U1) a : U1) : W1)
      exact hmono1 (hLz1'.mono hLz1le)
    · change IsCsFormMin 0 2 ((1 + T) * L1) (bggSegment.S1 (0 : Wv U1))
      rw [hS0]; exact hmono1 (hLz.mono hLzle)
  · have hm := waveManufactured_mult T t μ
    have h1 := hm.1
    have h2 := hm.2
    have hb : ‖coupledMult‖ ≤ (1 + T) * L1 :=
      hM.trans (hL0le.trans (le_mul_of_one_le_left hL10 (by linarith)))
    exact ⟨h1.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _)),
      h2.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))⟩
  · exact ⟨smul_ne_zero ht.1.ne' coupledσ_ne_zero, smul_ne_zero ht.1.ne' coupledφ_ne_zero⟩

end Manufactured

end Feec.Models.Cube.WeakSymmetry
