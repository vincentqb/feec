module

public import Feec.Models.Cube.Bridge
public import Feec.Models.Cube.Reflection
public import Feec.Legacy.MirrorCube.Pi

/-!
# The cube with tensorial mirror boundary conditions: TSD data propagate

With the thesis' row-wise boundary conditions only stationary TSD data propagate on the cube
(`Feec.Models.Cube.Parity`, `Feec.Models.Cube.Static`): row-wise conditions give `E_{ab}` and
`E_{ba}` different parities. The **mirror conditions** let the reflection `x_i ↦ -x_i` act on
vectors by `D_i = diag(s_i)` and on matrices by `M ↦ ± D_i M D_i`; they preserve symmetry and
trace, so the TSD fibres are permuted by the reflections, the torus constraint
`{0} × L²(TSD) × L²(TSD)` is invariant under the action, and it descends to a reducing subcomplex
of the cube complex (`Feec.Models.Cube.reducingSubcomplex_compSub_fixed`). Constraint propagation,
existence and uniqueness, and `K* = K` then follow from the general theorems
(`Feec.HilbertComplex.ReducingSubcomplex.propagates`, `.existsUnique_mem`, `.invariantCore_eq`).

Three realizations are treated:

* the **parity model** `Mirror.complex`: the subcomplex of the torus complex fixed by the mirror
  action (the method of images);
* the **cube `Q = (0, ½)³`** `Mirror.complexQ`: genuine real fields on `Q`
  (`L²(Q; ℝ³) → L²(Q; ℝ³ˣ³) → L²(Q; ℝ³ˣ³)` with `σ · n = 0`, `E_{nτ} = 0`; its differentials are
  the weak gradient and curl on `Q`, `Feec.Legacy.MirrorCube.mirrorCxQ_d0_weakGrad`,
  `Feec.Legacy.MirrorCube.mirrorCxQ_d1_eq`), embedded in the torus complex by the mirror extensions
  (`Mirror.embeddingQ`, a scaled embedding with scale `8`);
* **every open cube** `∏ (bᵢ, bᵢ + s)` (`Mirror.complexCube`), embedded in `complexQ` by the
  pull-back along `x ↦ 2 s x + b` (`Mirror.embeddingCube`).

In each case the constraint is the pull-back of the torus TSD constraint, and propagation is one
application of `Feec.HilbertComplex.ScaledEmbedding.reducingSubcomplex_comap`. The constraint
spaces on `Q` are TSD fields with the wall conditions `E_{τn} = 0`, `B_{nn} = 0`
(`Feec.Legacy.MirrorCube.TSDmE_le_TSD`). A non-stationary TSD datum, `E₀ = 2 cos(2π x₃) diag(1, -1, 0)`,
shows that the constraint has dynamical content in every realization.

## Main definitions

* `Feec.Models.Cube.comprEmbedding`, `Feec.Models.Cube.scaleEmbedding`: compressions and
  rescalings of short complexes as scaled embeddings.
* `Feec.Models.Cube.Mirror.action`, `Mirror.complex`, `Mirror.complexQ`, `Mirror.complexCube`.

## Main results

* `reducingSubcomplex_tsd_torus`: `{0} × L²(TSD) × L²(TSD)` reduces the torus complex.
* **`Mirror.reducingSubcomplex`**, `Mirror.propagates`, `Mirror.existsUnique_mem`,
  `Mirror.invariantCore_eq`, `Mirror.exists_nonstationary`.
* **`Mirror.reducingSubcomplexQ`**, `Mirror.propagatesQ`, `Mirror.existsUnique_memQ`,
  `Mirror.invariantCore_eqQ`, `Mirror.exists_nonstationaryQ`.
* **`Mirror.reducingSubcomplexCube`**, `Mirror.propagatesCube`, `Mirror.existsUnique_memCube`,
  `Mirror.invariantCore_eqCube`, `Mirror.exists_nonstationaryCube`.

## References

* [QuennevilleBelair2015], §4.10 (Prop 4.17)
* [Brezis2011], §9.2 (extension by reflection)
-/

open Feec.Legacy

open scoped RealInnerProductSpace
open Set LinearPMap

@[expose] public noncomputable section

universe u

namespace Feec.Models.Cube

open Feec.Legacy.HilbertComplex2 Feec.ShortHilbertComplex Feec.Legacy.Constraints Feec.Legacy.Torus Feec.Legacy.Box
open Feec.HilbertComplex (ScaledEmbedding totalSub ReducingSubcomplex)

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3

/-! ### Compressions and rescalings of short complexes as scaled embeddings -/

section Embeddings

open Feec.Legacy.MirrorCube

variable {c : ℝ} {W0 W1 W2 W0' W1' W2' : Type u}
  [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
  [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
  [NormedAddCommGroup W0'] [InnerProductSpace ℝ W0'] [CompleteSpace W0']
  [NormedAddCommGroup W1'] [InnerProductSpace ℝ W1'] [CompleteSpace W1']
  [NormedAddCommGroup W2'] [InnerProductSpace ℝ W2'] [CompleteSpace W2']

/-- Three maps as a family on `Fin 3`. -/
def map3 (J0 : W0' →L[ℝ] W0) (J1 : W1' →L[ℝ] W1) (J2 : W2' →L[ℝ] W2) :
    ∀ i : Fin 3, W3 W0' W1' W2' i →L[ℝ] W3 W0 W1 W2 i
  | 0 => J0
  | 1 => J1
  | 2 => J2

variable (H : HilbertComplex2 W0 W1 W2) (A0 : Compr c W0' W0) (A1 : Compr c W1' W1)
  (A2 : Compr c W2' W2) (h0 : ComprComm H.d0 A0 A1) (h1 : ComprComm H.d1 A1 A2)

/-- **A compression is a scaled embedding**: the embeddings `J` of the compression data map the
compressed complex into `H`, scaling inner products by `c` and commuting with the
differentials. -/
def comprEmbedding (hc : 0 < c) :
    ScaledEmbedding (comprComplex H A0 A1 A2 h0 h1).toShort.toHilbertComplex
      H.toShort.toHilbertComplex where
  J := map3 A0.J A1.J A2.J
  scale _ := c
  scale_pos _ := hc
  inner_J i x y := by
    fin_cases i
    exacts [A0.inner_J x y, A1.inner_J x y, A2.inner_J x y]
  dScale _ _ := 1
  dScale_ne_zero _ _ := one_ne_zero
  mapsTo i j x := by
    fin_cases i <;> fin_cases j
    all_goals first
      | exact Submodule.mem_top
      | exact (mem_compr_domain (T := H.d0) (A := A0) (B := A1)).1 x.2
      | exact (mem_compr_domain (T := H.d1) (A := A1) (B := A2)).1 x.2
  comm i j x := by
    fin_cases i <;> fin_cases j
    all_goals first
      | exact (by rw [one_smul]; exact (J_compr h0 x).symm)
      | exact (by rw [one_smul]; exact (J_compr h1 x).symm)
      | exact comm_of_eq_zero rfl rfl _ _ _ x _
  mem_domain_of_map i j x h := by
    fin_cases i <;> fin_cases j
    all_goals first
      | exact Submodule.mem_top
      | exact h

@[simp] theorem comprEmbedding_J_one (hc : 0 < c) (x : W1') :
    (comprEmbedding H A0 A1 A2 h0 h1 hc).J 1 x = A1.J x := rfl

@[simp] theorem comprEmbedding_J_two (hc : 0 < c) (x : W2') :
    (comprEmbedding H A0 A1 A2 h0 h1 hc).J 2 x = A2.J x := rfl

/-- The projection onto `S` preserves the range of `J` when it commutes with `P`. -/
theorem exists_J_eq_starProjection {W' W : Type*} [NormedAddCommGroup W']
    [InnerProductSpace ℝ W'] [NormedAddCommGroup W] [InnerProductSpace ℝ W] (A : Compr c W' W)
    (S : Submodule ℝ W) [S.HasOrthogonalProjection]
    (hP : ∀ z, S.starProjection (A.P z) = A.P (S.starProjection z)) (x : W') :
    ∃ y, A.J y = S.starProjection (A.J x) :=
  ⟨A.R (A.P (S.starProjection (A.J x))), by rw [A.JRP, ← hP, A.PJ]⟩

/-- The constraint `{0} × S₁ × S₂` pulls back along a compression to `{0} × J⁻¹ S₁ × J⁻¹ S₂`. -/
theorem comap_sub3 (hc : 0 < c) (S1 : Submodule ℝ W1) (S2 : Submodule ℝ W2) :
    (fun i => (sub3 (⊥ : Submodule ℝ W0) S1 S2 i).comap
      ((comprEmbedding H A0 A1 A2 h0 h1 hc).J i : W3 W0' W1' W2' i →ₗ[ℝ] W3 W0 W1 W2 i)) =
      sub3 (⊥ : Submodule ℝ W0') (S1.comap (A1.J : W1' →ₗ[ℝ] W1))
        (S2.comap (A2.J : W2' →ₗ[ℝ] W2)) := by
  funext i
  fin_cases i
  · change (⊥ : Submodule ℝ W0).comap (A0.J : W0' →ₗ[ℝ] W0) = ⊥
    rw [Submodule.comap_bot]
    exact LinearMap.ker_eq_bot.2 A0.J_injective
  · rfl
  · rfl

/-- **Constraint propagation transfers to compressions**: if `{0} × S₁ × S₂` reduces `H` and the
projections onto `S₁`, `S₂` commute with the projections `P` of the compression data, then
`{0} × J⁻¹ S₁ × J⁻¹ S₂` reduces the compressed complex. -/
theorem reducingSubcomplex_compr (hc : 0 < c) {S1 : Submodule ℝ W1} {S2 : Submodule ℝ W2}
    [S1.HasOrthogonalProjection] [S2.HasOrthogonalProjection]
    (hS : H.toShort.toHilbertComplex.ReducingSubcomplex (sub3 (⊥ : Submodule ℝ W0) S1 S2))
    (hP1 : ∀ z, S1.starProjection (A1.P z) = A1.P (S1.starProjection z))
    (hP2 : ∀ z, S2.starProjection (A2.P z) = A2.P (S2.starProjection z)) :
    (comprComplex H A0 A1 A2 h0 h1).toShort.toHilbertComplex.ReducingSubcomplex
      (sub3 (⊥ : Submodule ℝ W0') (S1.comap (A1.J : W1' →ₗ[ℝ] W1))
        (S2.comap (A2.J : W2' →ₗ[ℝ] W2))) := by
  have h := (comprEmbedding H A0 A1 A2 h0 h1 hc).reducingSubcomplex_comap hS fun i x => by
    fin_cases i
    · exact ⟨0, by
        change A0.J 0 = (⊥ : Submodule ℝ W0).starProjection (A0.J x)
        rw [Submodule.starProjection_bot, _root_.map_zero]; rfl⟩
    · exact exists_J_eq_starProjection A1 S1 hP1 x
    · exact exists_J_eq_starProjection A2 S2 hP2 x
  convert h using 1
  exact (comap_sub3 H A0 A1 A2 h0 h1 hc S1 S2).symm

variable (s : ℝ) (hs : s ≠ 0)

/-- **A rescaling is a scaled embedding**: the identity maps `s • d` to `d` with chain-rule
factor `s⁻¹`. -/
def scaleEmbedding :
    ScaledEmbedding (scaleComplex H s hs).toShort.toHilbertComplex H.toShort.toHilbertComplex where
  J i := ContinuousLinearMap.id ℝ _
  scale _ := 1
  scale_pos _ := one_pos
  inner_J i x y := by simp
  dScale _ _ := s⁻¹
  dScale_ne_zero _ _ := inv_ne_zero hs
  mapsTo i j x := by
    fin_cases i <;> fin_cases j
    all_goals first
      | exact Submodule.mem_top
      | exact x.2
  comm i j x := by
    fin_cases i <;> fin_cases j
    · exact comm_of_eq_zero rfl rfl _ _ _ x _
    · change H.d0 ⟨x.1, x.2⟩ = s⁻¹ • (s • H.d0 ⟨x.1, x.2⟩)
      rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
    · exact comm_of_eq_zero rfl rfl _ _ _ x _
    · exact comm_of_eq_zero rfl rfl _ _ _ x _
    · exact comm_of_eq_zero rfl rfl _ _ _ x _
    · change H.d1 ⟨x.1, x.2⟩ = s⁻¹ • (s • H.d1 ⟨x.1, x.2⟩)
      rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
    · exact comm_of_eq_zero rfl rfl _ _ _ x _
    · exact comm_of_eq_zero rfl rfl _ _ _ x _
    · exact comm_of_eq_zero rfl rfl _ _ _ x _
  mem_domain_of_map i j x h := by
    fin_cases i <;> fin_cases j
    all_goals first
      | exact Submodule.mem_top
      | exact h

end Embeddings

/-! ### The torus constraint -/

theorem isReducingPair_grad_tsd :
    periodicComplex.d0.IsReducingPair (⊥ : Submodule ℝ L2V) L2TSD := by
  refine isReducingPair_of_le_ker bot_le fun x => ?_
  rw [Submodule.mem_orthogonal]
  intro y hy
  obtain ⟨z, hz, hz0⟩ := mem_ker_iff.1 (L2TSD_le_ker hy)
  have h := adjoint_isFormalAdjoint periodicComplex.dense0 z x
  rw [hz0, inner_zero_left] at h
  rw [hz]; exact h.symm

theorem isReducingPair_curl_tsd : periodicComplex.d1.IsReducingPair L2TSD L2TSD :=
  ⟨fun x => projTSD_mem_Hcurl x.2, fun x => curlT_projTSD x⟩

/-- **`{0} × L²(TSD) × L²(TSD)` reduces the torus complex**: `R(grad) ⊥ L²(TSD)` and `curl`
commutes with the TSD projection (Fourier side: `curl_ξ` preserves `tsd(ξ)`).
Thesis: Prop 4.17 -/
theorem reducingSubcomplex_tsd_torus :
    torus.ReducingSubcomplex (sub3 (⊥ : Submodule ℝ L2V) L2TSD L2TSD) :=
  reducingSubcomplex_sub3 _ isReducingPair_grad_tsd isReducingPair_curl_tsd

namespace Mirror

/-! ### The parity model -/

/-- **The mirror action of `(ℤ/2)³` on the torus complex**: `σ(R_i x) = D_i σ(x)`,
`E(R_i x) = D_i E(x) D_i`, `B(R_i x) = -D_i B(x) D_i`. -/
def action : torus.Action ReflGroup :=
  reflAction periodicComplex.toShort Feec.Legacy.Box.intertwines_grad Feec.Legacy.Box.intertwines_curl

/-- **The cube complex with tensorial mirror boundary conditions** (`σ · n = 0`, `E_{nτ} = 0`),
as the subcomplex of the torus complex fixed by the mirror action.
Thesis: §4.10 -/
abbrev complex := action.fixedComplex

/-- The torus constraint `{0} × L²(TSD) × L²(TSD)`. -/
abbrev tsd : ∀ i : Fin 3, Submodule ℝ (W3 L2V L2M L2M i) := sub3 (⊥ : Submodule ℝ L2V) L2TSD L2TSD

theorem act_mem_tsd (g : ReflGroup) (i : Fin 3) (x : W3 L2V L2M L2M i) (hx : x ∈ tsd i) :
    action.act g i x ∈ tsd i := by
  fin_cases i
  · have hx' : x = (0 : L2V) := (Submodule.mem_bot ℝ).1 hx
    change reflAct mirrorV g x ∈ (⊥ : Submodule ℝ L2V)
    rw [hx', _root_.map_zero]; exact Submodule.zero_mem _
  · exact reflAct_mem (mirrorM 1 one_mul_one) (fun k A hA => mirrorM_mem_L2TSD 1 one_mul_one k hA)
      g hx
  · exact reflAct_mem (mirrorM (-1) neg_one_mul_neg_one)
      (fun k A hA => mirrorM_mem_L2TSD (-1) neg_one_mul_neg_one k hA) g hx

/-- **TSD with mirror parities reduces the mirror cube complex.**
Thesis: Prop 4.17 (corrected) -/
theorem reducingSubcomplex : complex.ReducingSubcomplex (compSub action.fixed tsd) :=
  reducingSubcomplex_compSub_fixed action reducingSubcomplex_tsd_torus act_mem_tsd

/-- **Prop 4.17 on the cube with mirror boundary conditions**: strong solutions of the Hodge wave
equation with data and forcing in `{0} × L²(TSD) × L²(TSD)` (mirror parities) stay there.
Thesis: Prop 4.17 (corrected) -/
theorem propagates {a b : ℝ} {F U : ℝ → PiLp 2 fun i => action.fixed i}
    (hU : Evolution.IsStrongSolution complex.wave (Icc a b) F U)
    (h0 : U a ∈ totalSub (compSub action.fixed tsd))
    (hF : ∀ t ∈ Icc a b, F t ∈ totalSub (compSub action.fixed tsd)) :
    ∀ t ∈ Icc a b, U t ∈ totalSub (compSub action.fixed tsd) :=
  reducingSubcomplex.propagates hU h0 hF

/-- Prop 4.17 on the mirror cube with existence and uniqueness.
Thesis: Prop 4.17 (corrected) -/
theorem existsUnique_mem {U₀ : PiLp 2 fun i => action.fixed i} (hU₀ : U₀ ∈ complex.wave.domain)
    (hU₀S : U₀ ∈ totalSub (compSub action.fixed tsd)) {F : ℝ → PiLp 2 fun i => action.fixed i}
    {a b : ℝ} (hF : Evolution.ForcingClass.admissible complex.wave a b F)
    (hFS : ∀ t ∈ Icc a b, F t ∈ totalSub (compSub action.fixed tsd)) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution complex.wave (Icc a b) F U ∧
      (∀ t ∈ Icc a b, U t ∈ totalSub (compSub action.fixed tsd)) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution complex.wave (Icc a b) F V → EqOn V U (Icc a b) :=
  reducingSubcomplex.existsUnique_mem hU₀ hU₀S hF hFS

/-- `K* = K` on the mirror cube.
Thesis: Prop 4.17 (corrected) -/
theorem invariantCore_eq :
    complex.waveGroup.invariantCore (totalSub (compSub action.fixed tsd)) =
      totalSub (compSub action.fixed tsd) :=
  reducingSubcomplex.invariantCore_eq

/-- The datum `(0, cos-field, 0)` on the torus. -/
def cosState : Tot L2V L2M L2M := ini L2V cosE 0

theorem cosState_mem_domL : cosState ∈ periodicComplex.domL := by
  rw [HilbertComplex2.mem_domL, cosState, tot_ini]
  refine ⟨Submodule.zero_mem _, ⟨cosE_mem_Hcurl, ?_⟩, Submodule.zero_mem _⟩
  change cosE ∈ gradT†.domain
  rw [adjoint_gradT_domain]
  exact L2TSD_le_Hdiv cosE_mem_L2TSD

theorem waveOp_cosState_ne : periodicComplex.waveOp ⟨cosState, cosState_mem_domL⟩ ≠ 0 := by
  intro h
  have h2 := congrArg (fun x => (tot L2V L2M L2M x).2.2) h
  simp only [HilbertComplex2.tot_waveOp, _root_.map_zero, Prod.snd_zero, neg_eq_zero] at h2
  apply curlSym_cosE_ne
  have e : periodicComplex.d1 (periodicComplex.prV1 ⟨cosState, cosState_mem_domL⟩) =
      curlT ⟨cosE, cosE_mem_Hcurl⟩ := by
    change curlT _ = curlT _
    congr 1
  rw [e] at h2
  exact congrArg (fun A : L2M => A k0) h2

theorem totEquiv_cosState_mem_fixed (i : Fin 3) : totEquiv cosState i ∈ action.fixed i := by
  fin_cases i
  · change -(tot L2V L2M L2M cosState).1 ∈ action.fixed 0
    rw [cosState, tot_ini, neg_zero]; exact Submodule.zero_mem _
  · change (tot L2V L2M L2M cosState).2.1 ∈ action.fixed 1
    rw [cosState, tot_ini]
    exact (mem_fixed_reflAction_one _ _ _).2 cosE_mem_fix
  · change (tot L2V L2M L2M cosState).2.2 ∈ action.fixed 2
    rw [cosState, tot_ini]; exact Submodule.zero_mem _

/-- The cos datum in the mirror cube complex. -/
def cosStateFixed : PiLp 2 fun i => action.fixed i :=
  WithLp.toLp 2 fun i => ⟨_, totEquiv_cosState_mem_fixed i⟩

theorem totalIncl_cosStateFixed :
    ReducingSubcomplex.totalIncl action.fixed cosStateFixed = totEquiv cosState := rfl

/-- **A non-stationary TSD datum propagates on the mirror cube**: `E₀ = 2 cos(2π x₃) diag(1, -1, 0)`
lies in `D(L) ∩ K` and is not stationary.
Thesis: Prop 4.17 (corrected) -/
theorem exists_nonstationary :
    ∃ y ∈ complex.wave.domain, y ∈ totalSub (compSub action.fixed tsd) ∧
      y ∉ complex.waveGroup.stationary := by
  have hdom := (mem_domL_iff periodicComplex).1 cosState_mem_domL
  refine ⟨cosStateFixed, ?_, ?_, ?_⟩
  · rw [mem_wave_domain_compress_iff, totalIncl_cosStateFixed]
    exact hdom
  · intro i
    change totEquiv cosState i ∈ tsd i
    fin_cases i
    · change -(tot L2V L2M L2M cosState).1 ∈ (⊥ : Submodule ℝ L2V)
      rw [cosState, tot_ini, neg_zero]; exact Submodule.zero_mem _
    · change (tot L2V L2M L2M cosState).2.1 ∈ L2TSD
      rw [cosState, tot_ini]; exact cosE_mem_L2TSD
    · change (tot L2V L2M L2M cosState).2.2 ∈ L2TSD
      rw [cosState, tot_ini]; exact Submodule.zero_mem _
  · rw [mem_stationary_compSub_iff, totalIncl_cosStateFixed]
    exact totEquiv_not_mem_stationary periodicComplex cosState_mem_domL waveOp_cosState_ne

/-! ### The cube `Q = (0, ½)³` -/

open Feec.Legacy.MirrorCube

/-- **The mirror complex of genuine fields on `Q`**: `L²(Q; ℝ³) → L²(Q; ℝ³ˣ³) → L²(Q; ℝ³ˣ³)`,
`grad` and `curl` with `σ · n = 0`, `E_{nτ} = 0` (`Feec.Legacy.MirrorCube.mirrorCxQ`). -/
abbrev complexQ := mirrorCxQ.toShort.toHilbertComplex

/-- The mirror extensions embed the cube complex in the torus complex (scale `8`). -/
def embeddingQ : ScaledEmbedding complexQ torus :=
  comprEmbedding periodicComplex comprV (comprM 1 one_mul_one) (comprM (-1) neg_one_mul_neg_one)
    comprComm_grad comprComm_curl eight_pos

/-- The constraint on `Q`: `{0} × TSDmE × TSDmB` (TSD with the wall conditions). -/
abbrev tsdQ : ∀ i : Fin 3, Submodule ℝ (W3 VQ MQ MQ i) := sub3 (⊥ : Submodule ℝ VQ) TSDmE TSDmB

/-- **TSD reduces the mirror complex on `Q`** (pull-back of the torus constraint along the
mirror extensions).
Thesis: Prop 4.17 (corrected) -/
theorem reducingSubcomplexQ : complexQ.ReducingSubcomplex tsdQ :=
  reducingSubcomplex_compr periodicComplex comprV (comprM 1 one_mul_one)
    (comprM (-1) neg_one_mul_neg_one) comprComm_grad comprComm_curl eight_pos
    reducingSubcomplex_tsd_torus (starProjection_Pm 1 one_mul_one)
    (starProjection_Pm (-1) neg_one_mul_neg_one)

/-- **Prop 4.17 on `Q` with mirror boundary conditions**: TSD data and forcing give TSD
solutions.
Thesis: Prop 4.17 (corrected) -/
theorem propagatesQ {a b : ℝ} {F U : ℝ → PiLp 2 (W3 VQ MQ MQ)}
    (hU : Evolution.IsStrongSolution complexQ.wave (Icc a b) F U) (h0 : U a ∈ totalSub tsdQ)
    (hF : ∀ t ∈ Icc a b, F t ∈ totalSub tsdQ) : ∀ t ∈ Icc a b, U t ∈ totalSub tsdQ :=
  reducingSubcomplexQ.propagates hU h0 hF

/-- Prop 4.17 on `Q` with existence and uniqueness.
Thesis: Prop 4.17 (corrected) -/
theorem existsUnique_memQ {U₀ : PiLp 2 (W3 VQ MQ MQ)} (hU₀ : U₀ ∈ complexQ.wave.domain)
    (hU₀S : U₀ ∈ totalSub tsdQ) {F : ℝ → PiLp 2 (W3 VQ MQ MQ)} {a b : ℝ}
    (hF : Evolution.ForcingClass.admissible complexQ.wave a b F)
    (hFS : ∀ t ∈ Icc a b, F t ∈ totalSub tsdQ) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution complexQ.wave (Icc a b) F U ∧
      (∀ t ∈ Icc a b, U t ∈ totalSub tsdQ) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution complexQ.wave (Icc a b) F V → EqOn V U (Icc a b) :=
  reducingSubcomplexQ.existsUnique_mem hU₀ hU₀S hF hFS

/-- `K* = K` on `Q`.
Thesis: Prop 4.17 (corrected) -/
theorem invariantCore_eqQ : complexQ.waveGroup.invariantCore (totalSub tsdQ) = totalSub tsdQ :=
  reducingSubcomplexQ.invariantCore_eq

/-- A non-stationary TSD datum on `Q`.
Thesis: Prop 4.17 (corrected) -/
theorem exists_nonstationaryQ :
    ∃ y ∈ complexQ.wave.domain, y ∈ totalSub tsdQ ∧ y ∉ complexQ.waveGroup.stationary :=
  ⟨totEquiv cosStateQ, (mem_domL_iff mirrorCxQ).1 cosStateQ_mem_domL,
    (mem_Kc_iff TSDmE TSDmB cosStateQ).1 cosStateQ_mem_Kc,
    totEquiv_not_mem_stationary mirrorCxQ cosStateQ_mem_domL cosStateQ_waveOp_ne⟩

/-! ### Every open cube -/

open Feec.Legacy.BoundedDomain (R3)
open Feec.Legacy.BoxIdent (openCube mem_Qr_iff_openCube)

variable {b : R3} {s : ℝ} (hs : 0 < s)

/-- **The mirror complex on the open cube** `∏ (bᵢ, bᵢ + s)` (`Feec.Legacy.MirrorCube.mirrorCxCube`). -/
abbrev complexCube (b : R3) (s : ℝ) (hs : 0 < s) := (mirrorCxCube b s hs).toShort.toHilbertComplex

/-- The pull-back along `x ↦ 2 s x + b` embeds the cube complex in the complex on `Q` (with
chain-rule factor `(2s)⁻¹`). -/
def embeddingCube : ScaledEmbedding (complexCube b s hs) complexQ :=
  (scaleEmbedding mirrorCxQ (2 * s)⁻¹ (inv_ne_zero (two_s_ne hs))).comp
    (comprEmbedding (scaleComplex mirrorCxQ (2 * s)⁻¹ (inv_ne_zero (two_s_ne hs)))
      (comprPullV (two_s_ne hs) (mem_Qr_iff_openCube hs b))
      (comprPullM (two_s_ne hs) (mem_Qr_iff_openCube hs b))
      (comprPullM (two_s_ne hs) (mem_Qr_iff_openCube hs b))
      (comprComm_id _ _ _ (fun _ => rfl) (fun _ => rfl))
      (comprComm_id _ _ _ (fun _ => rfl) (fun _ => rfl)) (pos_c (two_s_ne hs)))

/-- The constraint on the cube: the pull-back of `{0} × TSDmE × TSDmB` along the cube
embedding (`{0} × TSDmECube × TSDmBCube`). -/
abbrev tsdCube (b : R3) (s : ℝ) (hs : 0 < s) :
    ∀ i : Fin 3, Submodule ℝ (W3 (Feec.Legacy.BoundedDomain.L2V (openCube b s))
      (Feec.Legacy.BoundedDomain.L2M (openCube b s)) (Feec.Legacy.BoundedDomain.L2M (openCube b s)) i) :=
  fun i => (tsdQ i).comap ((embeddingCube (b := b) hs).J i : _ →ₗ[ℝ] _)

/-- **TSD reduces the mirror complex on every open cube.**
Thesis: Prop 4.17 (corrected) -/
theorem reducingSubcomplexCube : (complexCube b s hs).ReducingSubcomplex (tsdCube b s hs) :=
  (embeddingCube hs).reducingSubcomplex_comap reducingSubcomplexQ fun i x => by
    fin_cases i
    · exact ⟨_, (comprPullV (two_s_ne hs) (mem_Qr_iff_openCube hs b)).JRP _⟩
    · exact ⟨_, (comprPullM (two_s_ne hs) (mem_Qr_iff_openCube hs b)).JRP _⟩
    · exact ⟨_, (comprPullM (two_s_ne hs) (mem_Qr_iff_openCube hs b)).JRP _⟩

/-- **Prop 4.17 on every open cube with mirror boundary conditions**, in particular on `(0, π)³`
and on the unit cube `(0, 1)³`.
Thesis: Prop 4.17 (corrected) -/
theorem propagatesCube {a c : ℝ} {F U : ℝ → PiLp 2 (W3 (Feec.Legacy.BoundedDomain.L2V (openCube b s))
      (Feec.Legacy.BoundedDomain.L2M (openCube b s)) (Feec.Legacy.BoundedDomain.L2M (openCube b s)))}
    (hU : Evolution.IsStrongSolution (complexCube b s hs).wave (Icc a c) F U)
    (h0 : U a ∈ totalSub (tsdCube b s hs)) (hF : ∀ t ∈ Icc a c, F t ∈ totalSub (tsdCube b s hs)) :
    ∀ t ∈ Icc a c, U t ∈ totalSub (tsdCube b s hs) :=
  (reducingSubcomplexCube hs).propagates hU h0 hF

/-- Prop 4.17 on every open cube, with existence and uniqueness.
Thesis: Prop 4.17 (corrected) -/
theorem existsUnique_memCube {U₀ : PiLp 2 (W3 (Feec.Legacy.BoundedDomain.L2V (openCube b s))
      (Feec.Legacy.BoundedDomain.L2M (openCube b s)) (Feec.Legacy.BoundedDomain.L2M (openCube b s)))}
    (hU₀ : U₀ ∈ (complexCube b s hs).wave.domain) (hU₀S : U₀ ∈ totalSub (tsdCube b s hs))
    {F : ℝ → PiLp 2 (W3 (Feec.Legacy.BoundedDomain.L2V (openCube b s))
      (Feec.Legacy.BoundedDomain.L2M (openCube b s))
      (Feec.Legacy.BoundedDomain.L2M (openCube b s)))} {a c : ℝ}
    (hF : Evolution.ForcingClass.admissible (complexCube b s hs).wave a c F)
    (hFS : ∀ t ∈ Icc a c, F t ∈ totalSub (tsdCube b s hs)) :
    ∃ U, U a = U₀ ∧ Evolution.IsClassicalSolution (complexCube b s hs).wave (Icc a c) F U ∧
      (∀ t ∈ Icc a c, U t ∈ totalSub (tsdCube b s hs)) ∧
      ∀ V, V a = U₀ → Evolution.IsStrongSolution (complexCube b s hs).wave (Icc a c) F V →
        EqOn V U (Icc a c) :=
  (reducingSubcomplexCube hs).existsUnique_mem hU₀ hU₀S hF hFS

/-- `K* = K` on every open cube.
Thesis: Prop 4.17 (corrected) -/
theorem invariantCore_eqCube :
    (complexCube b s hs).waveGroup.invariantCore (totalSub (tsdCube b s hs)) =
      totalSub (tsdCube b s hs) :=
  (reducingSubcomplexCube hs).invariantCore_eq

theorem waveOp_cosStateCube_ne :
    (mirrorCxCube b s hs).waveOp ⟨_, cosStateCube_mem_domL hs⟩ ≠ 0 := by
  intro h0
  have hi := totJ_waveOp (h0 := comprComm_id _ _ _ (fun _ => rfl) (fun _ => rfl))
    (h1 := comprComm_id _ _ _ (fun _ => rfl) (fun _ => rfl)) (pos_c (two_s_ne hs))
    (cosStateCube b s hs) (cosStateCube_mem_domL hs)
  change totJ _ _ _ ((mirrorCxCube b s hs).waveOp ⟨_, cosStateCube_mem_domL hs⟩) = _ at hi
  rw [h0, _root_.map_zero, waveOp_scale] at hi
  have h1 := (smul_eq_zero.1 hi.symm).resolve_left (inv_ne_zero (two_s_ne hs))
  apply cosStateQ_waveOp_ne
  rw [← h1]
  exact lpmap_congr' _ _ _ (totJ_cosStateCube hs).symm

theorem cosStateCube_mem_tsdCube : totEquiv (cosStateCube b s hs) ∈ totalSub (tsdCube b s hs) := by
  have hK := (mem_Kc.1 (cosStateCube_mem_Kc (b := b) hs))
  intro i
  fin_cases i
  · change (embeddingCube (b := b) hs).J 0 (-(tot _ _ _ (cosStateCube b s hs)).1) ∈
      (⊥ : Submodule ℝ VQ)
    rw [hK.1, neg_zero]
    exact (Submodule.mem_bot ℝ (M := VQ)).2 (_root_.map_zero ((embeddingCube (b := b) hs).J 0))
  · exact hK.2.1
  · exact hK.2.2

/-- A non-stationary TSD datum on every open cube.
Thesis: Prop 4.17 (corrected) -/
theorem exists_nonstationaryCube :
    ∃ y ∈ (complexCube b s hs).wave.domain, y ∈ totalSub (tsdCube b s hs) ∧
      y ∉ (complexCube b s hs).waveGroup.stationary :=
  ⟨totEquiv (cosStateCube b s hs),
    (mem_domL_iff (mirrorCxCube b s hs)).1 (cosStateCube_mem_domL hs),
    cosStateCube_mem_tsdCube hs,
    totEquiv_not_mem_stationary (mirrorCxCube b s hs) (cosStateCube_mem_domL hs)
      (waveOp_cosStateCube_ne hs)⟩

end Mirror

end Feec.Models.Cube
