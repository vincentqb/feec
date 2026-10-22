module

public import Feec.Instances.EinsteinBianchiFEMGenerator
public import Feec.HilbertComplex.Approximation.ApproxOrthogonal
public import Feec.Models.Cube.MirrorWaveRegularity

/-!
# The mirror scheme (6.5) as an approximating FEEC discretization

The finite element scheme (6.5) of [QuennevilleBelair2015], §6.3, with mirror boundary conditions
(`Feec.Models.Cube.MirrorWeakSymmetry.mirrorWave`) computes real forms states
`(σₕ, uₕ, Mₕ, ρₕ)` on the cube `Q`; the continuous problem is the Hodge wave equation of the
complex mirror BGG complex `Feec.Models.Cube.MirrorBGG.complexQ` (complex matrix fields), read
over `ℝ` (`complexQℝ`). The scheme is not a subcomplex discretization: its discrete complex has
`S₀,ₕ = π¹S⁰ ≠ S⁰` (a variational crime). It is an **approximating FEEC discretization**
(`Feec.HilbertComplex.ApproxFEEC`):

* `Xₙ` = the hidden-constraint space of (6.5) at level `N`
  (`Feec.Instances.EinsteinBianchi.FEM.HiddenState`), `Lₙ` = the generator of (6.5) without
  source (`waveGen`, skew in the energy inner product), so `e^{tLₙ}` is the scheme
  (`mirrorFEMReal_sol_eq`);
* `ιₙ` = `mirrorEmb`: the forms state as a real-valued matrix field (rows of `E`, `B` through the
  Hodge star), isometric; `πₙ = ιₙ*`;
* complex data: real and imaginary parts each run (6.5)
  (`mirrorFEMApprox = mirrorFEMReal.complexify mulI`).

The real-part maps `Re` (componentwise `re0`, `rowsW1L`, `reM`, `rowsW2L`) and the embedding
`Rt = mirrorReEmb` satisfy the **error identity** `norm_sq_sub_mirrorReEmb`:
`‖y - Rt a - i Rt b‖² = ‖Re y - a‖² + ‖Re(-i y) - b‖²`; for a TSD state `y` the two terms are
the error quantities of `Feec.Models.Cube.MirrorWeakSymmetry.mirror_waveFEM` for the data `y` and
`-i y`.

**Faithfulness caveat.** The instance is faithful to `mirrorWave` (the scheme (6.5) of
`Feec.Models.Cube.MirrorWeakSymmetry`, with `S₀,ₕ = π¹S⁰` for the parity-smoothed cochain
projections), not to the variant with the canonical interpolant `Π`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §6.2 ((6.3), (6.4)), §6.3 ((6.5))
* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  Thm 3.9, Thm 3.10 (elliptic analogue)

Bibliography: [references.bib](../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology MeasureTheory

@[expose] public noncomputable section

namespace Feec.Instances.EinsteinBianchi.FEM

open Feec.HilbertComplex Feec.Models.Cube.MirrorWeakSymmetry Feec.Models.Cube.RowWise
open Feec.Models.Cube.MirrorBGG (SpaceQ W2Q complexQ tsdQ)
open Feec.Models.Cube.Mirror (MQ VQ)
open Feec.Models.Cube.MirrorSym (RQ)
open Feec.Models.Cube.WeakSymmetry (W0 W1 W2 Wv)
open Feec.Domain (L2F L2 formIdx)
open Feec.Models.Cube.Geometry (Q)

/-! ### Real and imaginary parts of complex `L²` fields -/

section ReIm

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- `f = Re f + i Re(-i f)`. -/
theorem ofRealL_reL_add_I_smul (f : Lp ℂ 2 μ) :
    ofRealL μ (reL μ f) + Complex.I • ofRealL μ (reL μ (-Complex.I • f)) = f := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (ofRealL μ (reL μ f))
      (Complex.I • ofRealL μ (reL μ (-Complex.I • f))),
    Lp.coeFn_smul Complex.I (ofRealL μ (reL μ (-Complex.I • f))), coeFn_ofRealL (reL μ f),
    coeFn_ofRealL (reL μ (-Complex.I • f)), coeFn_reL f, coeFn_reL (-Complex.I • f),
    Lp.coeFn_smul (-Complex.I) f] with x h1 h2 h3 h4 h5 h6 h7
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, h5, h6, h7, Pi.smul_apply, smul_eq_mul,
    smul_eq_mul]
  apply Complex.ext <;> simp

theorem reL_I_smul_ofRealL (g : Lp ℝ 2 μ) : reL μ (Complex.I • ofRealL μ g) = 0 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_reL (Complex.I • ofRealL μ g), Lp.coeFn_smul Complex.I (ofRealL μ g),
    coeFn_ofRealL g, Lp.coeFn_zero ℝ 2 μ] with x h1 h2 h3 h4
  rw [h1, h2, Pi.smul_apply, h3, h4, smul_eq_mul]
  simp

theorem reL_ofReal_smul_ofRealL (r : ℝ) (g : Lp ℝ 2 μ) :
    reL μ ((r : ℂ) • ofRealL μ g) = r • g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_reL ((r : ℂ) • ofRealL μ g), Lp.coeFn_smul (r : ℂ) (ofRealL μ g),
    coeFn_ofRealL g, Lp.coeFn_smul r g] with x h1 h2 h3 h4
  rw [h1, h2, Pi.smul_apply, h3, h4, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  simp

theorem reL_I_smul_ofReal_smul_ofRealL (r : ℝ) (g : Lp ℝ 2 μ) :
    reL μ (Complex.I • (r : ℂ) • ofRealL μ g) = 0 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_reL (Complex.I • (r : ℂ) • ofRealL μ g),
    Lp.coeFn_smul Complex.I ((r : ℂ) • ofRealL μ g), Lp.coeFn_smul (r : ℂ) (ofRealL μ g),
    coeFn_ofRealL g, Lp.coeFn_zero ℝ 2 μ] with x h1 h2 h3 h4 h5
  rw [h1, h2, Pi.smul_apply, h3, Pi.smul_apply, h4, h5, smul_eq_mul, smul_eq_mul]
  simp

/-- **Real/imaginary Parseval**: `‖f‖² = ‖Re f‖² + ‖Re(-i f)‖²`. -/
theorem norm_sq_eq_reL (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ‖reL μ f‖ ^ 2 + ‖reL μ (-Complex.I • f)‖ ^ 2 := by
  conv_lhs => rw [← ofRealL_reL_add_I_smul f]
  rw [@norm_add_sq ℂ, inner_smul_right, inner_ofRealL, norm_smul, Complex.norm_I, one_mul,
    Models.Cube.MirrorWeakSymmetry.norm_ofRealL, Models.Cube.MirrorWeakSymmetry.norm_ofRealL]
  simp

end ReIm

/-! ### Real parts of the components of the mirror state space -/

section Components

local notation "cQ" => Feec.Models.Cube.MirrorWeakSymmetry.cQ

/-- The unique `0`-form index. -/
def i0 : formIdx 3 0 := ⟨∅, by simp⟩

theorem eq_i0 (s : formIdx 3 0) : s = i0 := Feec.Models.Cube.ParitySmoother.eq_idx₀ s

scoped instance : Subsingleton (formIdx 3 0) := ⟨fun a b => (eq_i0 a).trans (eq_i0 b).symm⟩

/-- The real part of a scalar field as a `0`-form on the cube. -/
def re0 : RQ →L[ℝ] W0 :=
  (cQ (formIdx 3 0)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : formIdx 3 0 => L2 ℝ (Q (Fin 3)))).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun _ => reL _

/-- A real `0`-form on the cube as a (real-valued) complex scalar field. -/
def emb0 : W0 →L[ℝ] RQ :=
  ofRealL _ ∘L (PiLp.proj (𝕜 := ℝ) 2 (fun _ : formIdx 3 0 => L2 ℝ (Q (Fin 3))) i0) ∘L
    (cQ (formIdx 3 0)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem re0_apply (f : RQ) (s : formIdx 3 0) : cQ _ (re0 f) s = reL _ f := by
  simp [re0]

theorem emb0_apply (g : W0) : emb0 g = ofRealL _ (cQ _ g i0) := rfl

theorem norm_sq_re0 (f : RQ) : ‖re0 f‖ ^ 2 = ‖reL _ f‖ ^ 2 := by
  rw [← LinearIsometryEquiv.norm_map (cQ _) (re0 f), PiLp.norm_sq_eq_of_L2,
    Fintype.sum_subsingleton _ i0, re0_apply]

theorem re0_emb0 (g : W0) : re0 (emb0 g) = g := by
  apply (cQ (formIdx 3 0)).injective
  refine PiLp.ext fun s => ?_
  rw [re0_apply, emb0_apply, reL_ofRealL, eq_i0 s]

theorem re0_I_emb0 (g : W0) : re0 (Complex.I • emb0 g) = 0 := by
  apply (cQ (formIdx 3 0)).injective
  refine PiLp.ext fun s => ?_
  rw [re0_apply, emb0_apply, reL_I_smul_ofRealL, map_zero]
  rfl

/-- The real part of a vector field as a `2`-form on the cube (`i ↦ ⋆dxᵢ`). -/
def reM : VQ →L[ℝ] W2 :=
  (cQ (formIdx 3 2)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : formIdx 3 2 => L2 ℝ (Q (Fin 3)))).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun s => reL _ ∘L
      ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 => L2 ℂ (Q (Fin 3))) (eq2.symm s)).restrictScalars ℝ)

/-- A real `2`-form on the cube as a (real-valued) complex vector field. -/
def embM : W2 →L[ℝ] VQ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => L2 ℂ (Q (Fin 3)))).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun i => ofRealL _ ∘L
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : formIdx 3 2 => L2 ℝ (Q (Fin 3))) (eq2 i)) ∘L
      (cQ (formIdx 3 2)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem reM_apply (v : VQ) (s : formIdx 3 2) :
    cQ _ (reM v) s = reL _ (v (eq2.symm s)) := by
  simp [reM]

@[simp] theorem embM_apply (g : W2) (i : Fin 3) : embM g i = ofRealL _ (cQ _ g (eq2 i)) := rfl

theorem norm_sq_reM (v : VQ) : ‖reM v‖ ^ 2 = ∑ i, ‖reL _ (v i)‖ ^ 2 := by
  rw [← LinearIsometryEquiv.norm_map (cQ _) (reM v), PiLp.norm_sq_eq_of_L2]
  refine (Fintype.sum_equiv eq2.symm _ _ fun s => ?_)
  rw [reM_apply]

theorem reM_embM (g : W2) : reM (embM g) = g := by
  apply (cQ (formIdx 3 2)).injective
  refine PiLp.ext fun s => ?_
  rw [reM_apply, embM_apply, reL_ofRealL, Equiv.apply_symm_apply]

theorem reM_I_embM (g : W2) : reM (Complex.I • embM g) = 0 := by
  apply (cQ (formIdx 3 2)).injective
  refine PiLp.ext fun s => ?_
  rw [reM_apply, PiLp.smul_apply, embM_apply, reL_I_smul_ofRealL, map_zero]
  rfl

/-- Real `1`-form rows on the cube as a (real-valued) complex matrix field:
`E_{ab} = (w_a)_{dx_b}`. -/
def emb1 : Wv W1 →L[ℝ] MQ :=
  (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin 3 × Fin 3 => L2 ℂ (Q (Fin 3)))).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun p => ofRealL _ ∘L
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : formIdx 3 ((1 : ℕ) : ℤ) => L2 ℝ (Q (Fin 3))) (eq1 p.2)) ∘L
      (cQ (formIdx 3 ((1 : ℕ) : ℤ))).toContinuousLinearEquiv.toContinuousLinearMap ∘L
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => W1) p.1)

@[simp] theorem emb1_apply (w : Wv W1) (p : Fin 3 × Fin 3) :
    emb1 w p = ofRealL _ (cQ _ (w p.1) (eq1 p.2)) := rfl

/-- Real `2`-form rows on the cube as a (real-valued) complex matrix field (Hodge star):
`B_{ai} = ± (w_a)_{⋆dxᵢ}` (`matB`). -/
def emb2 : Wv W2 →L[ℝ] MQ :=
  (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin 3 × Fin 3 => L2 ℂ (Q (Fin 3)))).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun p =>
      ((sg2 p.2 : ℂ) • ContinuousLinearMap.id ℂ (L2 ℂ (Q (Fin 3)))).restrictScalars ℝ ∘L
      ofRealL _ ∘L
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : formIdx 3 ((2 : ℕ) : ℤ) => L2 ℝ (Q (Fin 3))) (eq2 p.2)) ∘L
      (cQ (formIdx 3 ((2 : ℕ) : ℤ))).toContinuousLinearEquiv.toContinuousLinearMap ∘L
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => W2) p.1)

@[simp] theorem emb2_apply (w : Wv W2) (p : Fin 3 × Fin 3) :
    emb2 w p = (sg2 p.2 : ℂ) • ofRealL _ (cQ _ (w p.1) (eq2 p.2)) := rfl

theorem norm_sq_rowsW1L (E : MQ) : ‖rowsW1L E‖ ^ 2 = ∑ p, ‖reL _ (E p)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rowsW1L_apply, LinearIsometryEquiv.norm_map, PiLp.norm_sq_eq_of_L2]
  refine (Fintype.sum_equiv eq1 (fun b => ‖rowRe E a (eq1 b)‖ ^ 2) _ fun b => rfl).symm.trans ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [rowRe_eq1]

theorem norm_sq_rowsW2L (B : MQ) : ‖rowsW2L B‖ ^ 2 = ∑ p, ‖reL _ (B p)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rowsW2L_apply, LinearIsometryEquiv.norm_map, PiLp.norm_sq_eq_of_L2]
  refine (Fintype.sum_equiv eq2 (fun i => ‖rowRe2 B a (eq2 i)‖ ^ 2) _ fun i => rfl).symm.trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rowRe2_eq2, norm_smul]
  have : ‖sg2 i‖ = 1 := by unfold sg2; split_ifs <;> simp
  rw [this, one_mul]

theorem rowsW1L_emb1 (w : Wv W1) : rowsW1L (emb1 w) = w := by
  refine PiLp.ext fun a => ?_
  rw [rowsW1L_apply, LinearIsometryEquiv.symm_apply_eq]
  refine PiLp.ext fun s => ?_
  obtain ⟨b, rfl⟩ := eq1.surjective s
  rw [rowRe_eq1, emb1_apply, reL_ofRealL]
  rfl

theorem rowsW1L_I_emb1 (w : Wv W1) : rowsW1L (Complex.I • emb1 w) = 0 := by
  refine PiLp.ext fun a => ?_
  rw [rowsW1L_apply, PiLp.zero_apply, LinearIsometryEquiv.map_eq_zero_iff]
  refine PiLp.ext fun s => ?_
  obtain ⟨b, rfl⟩ := eq1.surjective s
  rw [rowRe_eq1, PiLp.smul_apply, emb1_apply, reL_I_smul_ofRealL]
  rfl

theorem rowsW2L_emb2 (w : Wv W2) : rowsW2L (emb2 w) = w := by
  refine PiLp.ext fun a => ?_
  rw [rowsW2L_apply, LinearIsometryEquiv.symm_apply_eq]
  refine PiLp.ext fun s => ?_
  obtain ⟨i, rfl⟩ := eq2.surjective s
  rw [rowRe2_eq2, emb2_apply, reL_ofReal_smul_ofRealL, smul_smul, sg2_mul_self, one_smul]
  rfl

theorem rowsW2L_I_emb2 (w : Wv W2) : rowsW2L (Complex.I • emb2 w) = 0 := by
  refine PiLp.ext fun a => ?_
  rw [rowsW2L_apply, PiLp.zero_apply, LinearIsometryEquiv.map_eq_zero_iff]
  refine PiLp.ext fun s => ?_
  obtain ⟨i, rfl⟩ := eq2.surjective s
  rw [rowRe2_eq2, PiLp.smul_apply, emb2_apply, reL_I_smul_ofReal_smul_ofRealL, smul_zero]
  rfl

end Components

/-! ### The error identity of real and imaginary parts -/

/-- **Real and imaginary parts**: for maps `R`, `Rt` with `‖z‖² = ‖R z‖² + ‖R (-i z)‖²`,
`R (Rt w) = w` and `R (i Rt w) = 0`: `‖z - Rt a - i Rt b‖² = ‖R z - a‖² + ‖R (-i z) - b‖²`. -/
theorem norm_sq_sub_emb {C E : Type*} [NormedAddCommGroup C] [Module ℂ C] [NormedAddCommGroup E]
    (R : C →+ E) (Rt : E →+ C) (hP : ∀ z, ‖z‖ ^ 2 = ‖R z‖ ^ 2 + ‖R (-Complex.I • z)‖ ^ 2)
    (hQ : ∀ w, R (Rt w) = w) (hR : ∀ w, R (Complex.I • Rt w) = 0) (z : C) (a b : E) :
    ‖z - Rt a - Complex.I • Rt b‖ ^ 2 = ‖R z - a‖ ^ 2 + ‖R (-Complex.I • z) - b‖ ^ 2 := by
  have h1 : R (z - Rt a - Complex.I • Rt b) = R z - a := by rw [map_sub, map_sub, hQ, hR, sub_zero]
  have h2 : R (-Complex.I • (z - Rt a - Complex.I • Rt b)) = R (-Complex.I • z) - b := by
    rw [smul_sub, smul_sub, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul,
      neg_smul Complex.I (Rt a), map_sub, map_sub, map_neg, hR, neg_zero, sub_zero, hQ]
  rw [hP, h1, h2]

attribute [-instance] ShortHilbertComplex.instNormedSpaceRealW3
  ShortHilbertComplex.instIsScalarTowerRealW3

/-- Degreewise scalar towers of the mirror state spaces (the real structure is the one of the
real inner products). -/
scoped instance instIsScalarTowerSpaceQ : ∀ i, IsScalarTower ℝ ℂ (SpaceQ i)
  | 0 => inferInstanceAs (IsScalarTower ℝ ℂ RQ)
  | 1 => inferInstanceAs (IsScalarTower ℝ ℂ MQ)
  | 2 => inferInstanceAs (IsScalarTower ℝ ℂ W2Q)

/-- Shortcut instances for the finite element spaces (synthesis under binders is expensive). -/
scoped instance instIPS_TU0 : InnerProductSpace ℝ TU0 := inferInstance
scoped instance instIPS_TU1 : InnerProductSpace ℝ TU1 := inferInstance
scoped instance instIPS_W2 : InnerProductSpace ℝ W2 := inferInstance
scoped instance instIPS_BU0 : InnerProductSpace ℝ BU0 := inferInstance
scoped instance instIPS_BU1 : InnerProductSpace ℝ BU1 := inferInstance
scoped instance instIPS_WvW2 : InnerProductSpace ℝ (Wv W2) := inferInstance

/-- The real continuous energy space `L²Λ⁰ × (L²Λ¹)³ × L²Λ² × (L²Λ²)³` of the mirror forms model. -/
abbrev REnergy : Type := EState W0 (Wv W1) W2 (Wv W2)

/-- The slots of a mirror state, as real-linear maps. -/
def slot0 : PiLp 2 SpaceQ →L[ℝ] RQ := PiLp.proj (𝕜 := ℝ) 2 SpaceQ 0
/-- The electric slot. -/
def slot1 : PiLp 2 SpaceQ →L[ℝ] MQ := PiLp.proj (𝕜 := ℝ) 2 SpaceQ 1
/-- The multiplier slot `M`. -/
def slotM : PiLp 2 SpaceQ →L[ℝ] VQ :=
  WithLp.fstL 2 ℝ VQ MQ ∘L (PiLp.proj (𝕜 := ℝ) 2 SpaceQ 2 : PiLp 2 SpaceQ →L[ℝ] W2Q)
/-- The magnetic slot `B`. -/
def slotB : PiLp 2 SpaceQ →L[ℝ] MQ :=
  WithLp.sndL 2 ℝ VQ MQ ∘L (PiLp.proj (𝕜 := ℝ) 2 SpaceQ 2 : PiLp 2 SpaceQ →L[ℝ] W2Q)

/-- **A real forms state as a real-valued mirror state.** -/
def mirrorReEmb : REnergy →L[ℝ] PiLp 2 SpaceQ :=
  (PiLp.continuousLinearEquiv 2 ℝ SpaceQ).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun i => match i with
      | 0 => emb0 ∘L (show REnergy →L[ℝ] W0 from
          (ContinuousLinearMap.fst ℝ W0 _) ∘L EState.mkL.symm.toContinuousLinearMap)
      | 1 => emb1 ∘L (show REnergy →L[ℝ] Wv W1 from
          (ContinuousLinearMap.fst ℝ (Wv W1) _) ∘L (ContinuousLinearMap.snd ℝ W0 _) ∘L
            EState.mkL.symm.toContinuousLinearMap)
      | 2 => (WithLp.prodContinuousLinearEquiv 2 ℝ VQ MQ).symm.toContinuousLinearMap ∘L
          ((embM ∘L (show REnergy →L[ℝ] W2 from
            (ContinuousLinearMap.fst ℝ W2 (Wv W2)) ∘L (ContinuousLinearMap.snd ℝ (Wv W1) _) ∘L
              (ContinuousLinearMap.snd ℝ W0 _) ∘L EState.mkL.symm.toContinuousLinearMap)).prod
          (emb2 ∘L (show REnergy →L[ℝ] Wv W2 from
            (ContinuousLinearMap.snd ℝ W2 (Wv W2)) ∘L (ContinuousLinearMap.snd ℝ (Wv W1) _) ∘L
              (ContinuousLinearMap.snd ℝ W0 _) ∘L EState.mkL.symm.toContinuousLinearMap)))

theorem norm_sq_spaceQ (y : PiLp 2 SpaceQ) :
    ‖y‖ ^ 2 = ‖slot0 y‖ ^ 2 + ‖slot1 y‖ ^ 2 + ‖slotM y‖ ^ 2 + ‖slotB y‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  have h2 : ‖(y 2 : W2Q)‖ ^ 2 = ‖slotM y‖ ^ 2 + ‖slotB y‖ ^ 2 :=
    WithLp.prod_norm_sq_eq_of_L2 _
  change ‖slot0 y‖ ^ 2 + ‖slot1 y‖ ^ 2 + ‖(y 2 : W2Q)‖ ^ 2 = _
  rw [h2]; ring

theorem slot0_smul (c : ℂ) (y : PiLp 2 SpaceQ) : slot0 (c • y) = c • slot0 y := rfl
theorem slot1_smul (c : ℂ) (y : PiLp 2 SpaceQ) : slot1 (c • y) = c • slot1 y := rfl
theorem slotM_smul (c : ℂ) (y : PiLp 2 SpaceQ) : slotM (c • y) = c • slotM y := rfl
theorem slotB_smul (c : ℂ) (y : PiLp 2 SpaceQ) : slotB (c • y) = c • slotB y := rfl
@[simp] theorem slot0_mirrorReEmb (z : REnergy) : slot0 (mirrorReEmb z) = emb0 z.σ := rfl
@[simp] theorem slot1_mirrorReEmb (z : REnergy) : slot1 (mirrorReEmb z) = emb1 z.u := rfl
@[simp] theorem slotM_mirrorReEmb (z : REnergy) : slotM (mirrorReEmb z) = embM z.M := rfl
@[simp] theorem slotB_mirrorReEmb (z : REnergy) : slotB (mirrorReEmb z) = emb2 z.ρ := rfl

theorem norm_sq_re0_add (f : RQ) : ‖f‖ ^ 2 = ‖re0 f‖ ^ 2 + ‖re0 (-Complex.I • f)‖ ^ 2 := by
  rw [norm_sq_re0, norm_sq_re0, norm_sq_eq_reL]

theorem norm_sq_reM_add (v : VQ) : ‖v‖ ^ 2 = ‖reM v‖ ^ 2 + ‖reM (-Complex.I • v)‖ ^ 2 := by
  rw [norm_sq_reM, norm_sq_reM, PiLp.norm_sq_eq_of_L2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_sq_eq_reL, PiLp.smul_apply]

theorem norm_sq_rowsW1L_add (E : MQ) :
    ‖E‖ ^ 2 = ‖rowsW1L E‖ ^ 2 + ‖rowsW1L (-Complex.I • E)‖ ^ 2 := by
  rw [norm_sq_rowsW1L, norm_sq_rowsW1L, PiLp.norm_sq_eq_of_L2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [norm_sq_eq_reL, PiLp.smul_apply]

theorem norm_sq_rowsW2L_add (B : MQ) :
    ‖B‖ ^ 2 = ‖rowsW2L B‖ ^ 2 + ‖rowsW2L (-Complex.I • B)‖ ^ 2 := by
  rw [norm_sq_rowsW2L, norm_sq_rowsW2L, PiLp.norm_sq_eq_of_L2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [norm_sq_eq_reL, PiLp.smul_apply]

set_option maxHeartbeats 1000000 in
/-- **The error identity**: `‖y - Rt a - i Rt b‖² = ‖Re y - a‖² + ‖Re(-i y) - b‖²` for every
mirror state `y` and real forms states `a`, `b`. -/
theorem norm_sq_sub_mirrorReEmb (y : PiLp 2 SpaceQ) (a b : REnergy) :
    ‖y - mirrorReEmb a - Complex.I • mirrorReEmb b‖ ^ 2 =
      ‖re0 (slot0 y) - a.σ‖ ^ 2 + ‖rowsW1L (slot1 y) - a.u‖ ^ 2 + ‖reM (slotM y) - a.M‖ ^ 2 +
        ‖rowsW2L (slotB y) - a.ρ‖ ^ 2 +
      (‖re0 (-Complex.I • slot0 y) - b.σ‖ ^ 2 + ‖rowsW1L (-Complex.I • slot1 y) - b.u‖ ^ 2 +
        ‖reM (-Complex.I • slotM y) - b.M‖ ^ 2 + ‖rowsW2L (-Complex.I • slotB y) - b.ρ‖ ^ 2) := by
  have e0 := norm_sq_sub_emb re0.toLinearMap.toAddMonoidHom emb0.toLinearMap.toAddMonoidHom
    norm_sq_re0_add re0_emb0 re0_I_emb0 (slot0 y) a.σ b.σ
  have e1 := norm_sq_sub_emb rowsW1L.toLinearMap.toAddMonoidHom emb1.toLinearMap.toAddMonoidHom
    norm_sq_rowsW1L_add rowsW1L_emb1 rowsW1L_I_emb1 (slot1 y) a.u b.u
  have eM := norm_sq_sub_emb reM.toLinearMap.toAddMonoidHom embM.toLinearMap.toAddMonoidHom
    norm_sq_reM_add reM_embM reM_I_embM (slotM y) a.M b.M
  have e2 := norm_sq_sub_emb rowsW2L.toLinearMap.toAddMonoidHom emb2.toLinearMap.toAddMonoidHom
    norm_sq_rowsW2L_add rowsW2L_emb2 rowsW2L_I_emb2 (slotB y) a.ρ b.ρ
  simp only [LinearMap.toAddMonoidHom_coe, ContinuousLinearMap.coe_coe] at e0 e1 eM e2
  have h0 : slot0 (y - mirrorReEmb a - Complex.I • mirrorReEmb b) =
      slot0 y - emb0 a.σ - Complex.I • emb0 b.σ := by
    rw [map_sub, map_sub, slot0_smul, slot0_mirrorReEmb, slot0_mirrorReEmb]
  have h1 : slot1 (y - mirrorReEmb a - Complex.I • mirrorReEmb b) =
      slot1 y - emb1 a.u - Complex.I • emb1 b.u := by
    rw [map_sub, map_sub, slot1_smul, slot1_mirrorReEmb, slot1_mirrorReEmb]
  have hM : slotM (y - mirrorReEmb a - Complex.I • mirrorReEmb b) =
      slotM y - embM a.M - Complex.I • embM b.M := by
    rw [map_sub, map_sub, slotM_smul, slotM_mirrorReEmb, slotM_mirrorReEmb]
  have h2 : slotB (y - mirrorReEmb a - Complex.I • mirrorReEmb b) =
      slotB y - emb2 a.ρ - Complex.I • emb2 b.ρ := by
    rw [map_sub, map_sub, slotB_smul, slotB_mirrorReEmb, slotB_mirrorReEmb]
  rw [norm_sq_spaceQ, h0, h1, hM, h2, e0, e1, eM, e2]
  ring

set_option maxHeartbeats 1000000 in
/-- `‖Rt a + i Rt b‖² = ‖a‖² + ‖b‖²`. -/
theorem norm_sq_mirrorReEmb_add (a b : REnergy) :
    ‖mirrorReEmb a + Complex.I • mirrorReEmb b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have h := norm_sq_sub_mirrorReEmb 0 a b
  simp only [map_zero, smul_zero, zero_sub, norm_neg] at h
  rw [EState.norm_sq a, EState.norm_sq b]
  have e : -mirrorReEmb a - Complex.I • mirrorReEmb b =
      -(mirrorReEmb a + Complex.I • mirrorReEmb b) := by abel
  rw [e, norm_neg] at h
  rw [h]

theorem norm_mirrorReEmb (a : REnergy) : ‖mirrorReEmb a‖ = ‖a‖ := by
  have h := norm_sq_mirrorReEmb_add a 0
  rw [map_zero, smul_zero, add_zero, norm_zero] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)

/-- Real states and imaginary states are orthogonal: `⟪Rt a, i Rt b⟫_ℝ = 0`. -/
theorem inner_mirrorReEmb_I (a b : REnergy) :
    ⟪mirrorReEmb a, Complex.I • mirrorReEmb b⟫_ℝ = 0 := by
  have h := norm_sq_mirrorReEmb_add a b
  have hb : ‖Complex.I • mirrorReEmb b‖ = ‖b‖ := by rw [norm_smul, Complex.norm_I, one_mul,
    norm_mirrorReEmb]
  rw [norm_add_sq_real, norm_mirrorReEmb, hb] at h
  linarith

/-! ### The forms states of the mirror scheme -/

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : Feec.Models.Cube.FEM.ParitySmoothingEstimates 3 ∅
    Feec.FiniteElement.PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3,
    Feec.Models.Cube.FEM.ParitySmoothingEstimates 3 {a} Feec.FiniteElement.PolySeq.lagrangeP2 ρ C)

/-- The hidden space of the mirror scheme (6.5) at level `N`. -/
abbrev mirrorHidden (N : ℕ) := HiddenState (mirrorWave hT hB N)

/-- The discrete forms state as a continuous forms state (isometric). -/
def mirrorFE (N : ℕ) : mirrorHidden hT hB N →L[ℝ] REnergy :=
  EState.mapL ((TD0.domain.subtypeL) ∘L (mirrorFEM hT hB N).V0h.subtypeL)
    (bIncl1CLM ∘L (mirrorFEM hT hB N).Vt1h.subtypeL) (mirrorFEM hT hB N).W2h.subtypeL
    (mirrorFEM hT hB N).Wt2h.subtypeL ∘L HiddenState.subtypeL _

theorem norm_mirrorFE0 (N : ℕ) (x : (mirrorFEM hT hB N).V0h) :
    ‖((TD0.domain.subtypeL) ∘L (mirrorFEM hT hB N).V0h.subtypeL) x‖ = ‖x‖ := rfl

theorem norm_mirrorFE1 (N : ℕ) (x : (mirrorFEM hT hB N).Vt1h) :
    ‖(bIncl1CLM ∘L (mirrorFEM hT hB N).Vt1h.subtypeL) x‖ = ‖x‖ := norm_bIncl1 (x : BU1)

theorem norm_mirrorFE2 (N : ℕ) (x : (mirrorFEM hT hB N).W2h) :
    ‖(mirrorFEM hT hB N).W2h.subtypeL x‖ = ‖x‖ := rfl

theorem norm_mirrorFE3 (N : ℕ) (x : (mirrorFEM hT hB N).Wt2h) :
    ‖(mirrorFEM hT hB N).Wt2h.subtypeL x‖ = ‖x‖ := rfl

theorem norm_mirrorFE (N : ℕ) (v : mirrorHidden hT hB N) : ‖mirrorFE hT hB N v‖ = ‖v‖ :=
  (EState.norm_mapL (norm_mirrorFE0 hT hB N) (norm_mirrorFE1 hT hB N) (norm_mirrorFE2 hT hB N)
    (norm_mirrorFE3 hT hB N) v.toEState).trans (HiddenState.norm_toEState v)


/-- **The reading map of the mirror scheme**: real discrete forms states as real-valued matrix
fields (rows of `E`, `B` through the Hodge star), isometric. -/
def mirrorEmb (N : ℕ) : mirrorHidden hT hB N →L[ℝ] PiLp 2 SpaceQ :=
  mirrorReEmb ∘L mirrorFE hT hB N

theorem mirrorEmb_apply (N : ℕ) (v : mirrorHidden hT hB N) :
    mirrorEmb hT hB N v = mirrorReEmb (mirrorFE hT hB N v) := rfl

theorem norm_mirrorEmb (N : ℕ) (v : mirrorHidden hT hB N) : ‖mirrorEmb hT hB N v‖ = ‖v‖ :=
  (norm_mirrorReEmb (mirrorFE hT hB N v)).trans (norm_mirrorFE hT hB N v)

theorem inner_mirrorEmb (N : ℕ) (v w : mirrorHidden hT hB N) :
    ⟪mirrorEmb hT hB N v, mirrorEmb hT hB N w⟫_ℝ = ⟪v, w⟫_ℝ :=
  LinearIsometry.inner_map_map (⟨(mirrorEmb hT hB N).toLinearMap, norm_mirrorEmb hT hB N⟩ :
    mirrorHidden hT hB N →ₗᵢ[ℝ] PiLp 2 SpaceQ) v w

theorem adjoint_mirrorEmb_apply (N : ℕ) (v : mirrorHidden hT hB N) :
    (mirrorEmb hT hB N).adjoint (mirrorEmb hT hB N v) = v :=
  ext_inner_left ℝ fun w =>
    (ContinuousLinearMap.adjoint_inner_right (mirrorEmb hT hB N) w (mirrorEmb hT hB N v)).trans
      (inner_mirrorEmb hT hB N w v)

/-! ### The real mirror complex and the scheme as an approximating FEEC discretization -/

/-- The complex inner products of the mirror state spaces restrict to the real ones. -/
theorem real_inner_eq_re_inner_spaceQ (i : Fin 3) (x y : SpaceQ i) :
    ⟪x, y⟫_ℝ = RCLike.re ⟪x, y⟫_ℂ := by
  have hC : ∀ v w : ℂ, ⟪v, w⟫_ℝ = RCLike.re ⟪v, w⟫_ℂ := fun v w => by
    rw [Complex.inner, RCLike.inner_apply, mul_comm]; rfl
  have hRQ : ∀ f g : RQ, ⟪f, g⟫_ℝ = RCLike.re ⟪f, g⟫_ℂ := fun f g =>
    MeasureTheory.L2.real_inner_eq_re_inner hC f g
  have hL2F : ∀ {P : Type} [Fintype P] (f g : L2F ℂ (Q (Fin 3)) P),
      ⟪f, g⟫_ℝ = RCLike.re ⟪f, g⟫_ℂ := fun f g => by
    rw [PiLp.inner_apply, PiLp.inner_apply, map_sum]
    exact Finset.sum_congr rfl fun p _ => hRQ (f p) (g p)
  have hW2 : ∀ x y : W2Q, ⟪x, y⟫_ℝ = RCLike.re ⟪x, y⟫_ℂ := fun x y => by
    rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply, map_add,
      hL2F (P := Fin 3) (WithLp.ofLp x).1, hL2F (P := Fin 3 × Fin 3) (WithLp.ofLp x).2]
  fin_cases i
  · exact hRQ x y
  · exact hL2F (P := Fin 3 × Fin 3) x y
  · exact hW2 x y

/-- **The real mirror BGG complex**: `complexQ` over `ℝ` (same domains, same wave operator). -/
abbrev complexQℝ : HilbertComplex ℝ ComplexShape.fin3 SpaceQ := complexQ.restrictScalars

theorem wave_complexQℝ : complexQℝ.wave = complexQ.wave.restrictScalars :=
  wave_restrictScalars real_inner_eq_re_inner_spaceQ

theorem mem_complexQℝ_domain {x : PiLp 2 SpaceQ} :
    x ∈ complexQℝ.wave.domain ↔ x ∈ complexQ.wave.domain := by
  rw [wave_complexQℝ]; exact Iff.rfl

private theorem apply_eq_of_eq_pmap {A B : PiLp 2 SpaceQ →ₗ.[ℝ] PiLp 2 SpaceQ} (h : A = B)
    (x : A.domain) (y : B.domain) (hxy : (x : PiLp 2 SpaceQ) = y) : A x = B y := by
  subst h; rw [Subtype.ext hxy]

theorem complexQℝ_wave_apply (x : complexQℝ.wave.domain) :
    complexQℝ.wave x = complexQ.wave ⟨x, mem_complexQℝ_domain.1 x.2⟩ :=
  apply_eq_of_eq_pmap wave_complexQℝ x ⟨x, mem_complexQℝ_domain.1 x.2⟩ rfl

/-- Strong solutions of the complex wave equation are strong solutions of the real one. -/
theorem isStrongSolution_complexQℝ {I : Set ℝ} {U : ℝ → PiLp 2 SpaceQ}
    (h : Evolution.IsStrongSolution complexQ.wave I 0 U) :
    Evolution.IsStrongSolution complexQℝ.wave I 0 U :=
  ⟨h.continuousOn, fun t ht => by
    obtain ⟨v, hv, hd⟩ := h.deriv t ht
    refine ⟨v, ?_, hd⟩
    rw [wave_complexQℝ]
    exact (LinearPMap.mem_graph_restrictScalars _).2 hv⟩

/-- **The real and the complex wave groups agree** (forward in time). -/
theorem complexQℝ_waveGroup {t : ℝ} (ht : 0 ≤ t) (x : PiLp 2 SpaceQ) :
    complexQℝ.waveGroup.S t x = complexQ.waveGroup.S t x := by
  have hdom : ∀ y ∈ complexQℝ.wave.domain,
      complexQℝ.waveGroup.S t y = complexQ.waveGroup.S t y := fun y hy => by
    have hc := isClassicalSolution_waveGroup_orbit complexQ (mem_complexQℝ_domain.1 hy) t
    have hs := isStrongSolution_complexQℝ hc.toIsStrongSolution
    have e := (constrainedFEEC_wellPosed hy t).2.1 _ (by simp) hs ⟨ht, le_rfl⟩
    exact e.symm
  have hd : Dense (complexQℝ.wave.domain : Set (PiLp 2 SpaceQ)) := complexQℝ.dense_wave_domain
  have hc1 : Continuous fun y => complexQℝ.waveGroup.S t y := (complexQℝ.waveGroup.S t).continuous
  have hc2 : Continuous fun y => complexQ.waveGroup.S t y := (complexQ.waveGroup.S t).continuous
  exact congrFun (hc1.ext_on hd hc2 fun y hy => hdom y hy) x

/-- **The real TSD constraint**. -/
abbrev tsdQℝ : Submodule ℝ (PiLp 2 SpaceQ) := totalSub fun i => (tsdQ i).restrictScalars ℝ

/-- **The TSD constraint reduces the real mirror wave operator.** [QuennevilleBelair2015],
Prop 4.17 (corrected) -/
theorem isReducing_tsdQℝ : complexQℝ.wave.IsReducing tsdQℝ :=
  (Feec.Models.Cube.MirrorBGG.reducingSubcomplexQ.restrictScalars
    real_inner_eq_re_inner_spaceQ).isReducing_wave

theorem norm_mirrorEmb_le (N : ℕ) : ‖mirrorEmb hT hB N‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v =>
    (norm_mirrorEmb hT hB N v).trans_le (one_mul _).ge

/-- **The mirror scheme (6.5) on real fields as an approximating FEEC discretization**:
`X_N` = the hidden space, `L_N` = the generator of (6.5) without source (`waveGen`), `ι_N` =
`mirrorEmb`, `π_N = ι_N*`; the instance fields are the `HiddenState` constants. -/
def mirrorFEMReal : ApproxFEEC complexQℝ ℕ where
  K := tsdQℝ
  isClosed_K := isClosed_totalSub
  l := atTop
  X N := mirrorHidden hT hB N
  normedAddCommGroup _ := HiddenState.instNormedAddCommGroup _
  innerProductSpace _ := HiddenState.instInnerProductSpace _
  completeSpace _ := HiddenState.instCompleteSpace _
  normedSpaceReal _ := (HiddenState.instInnerProductSpace _).toNormedSpace
  isScalarTower _ := IsScalarTower.left _
  L N := waveGen (mirrorWave hT hB N) (mirrorWave_dt0_injective hT hB N)
    (mirrorWave_S0_surjective hT hB N)
  skew _ := waveGen_skew _ _ _
  incl := mirrorEmb hT hB
  proj N := (mirrorEmb hT hB N).adjoint
  proj_incl := adjoint_mirrorEmb_apply hT hB
  bound := ⟨1, fun N => ⟨norm_mirrorEmb_le hT hB N,
    (ContinuousLinearMap.adjoint.norm_map (mirrorEmb hT hB N)).trans_le
      (norm_mirrorEmb_le hT hB N)⟩⟩

theorem mirrorFEMReal_isOrthogonal : ApproxFEEC.IsOrthogonal (mirrorFEMReal hT hB) where
  inner_incl N a b := inner_mirrorEmb hT hB N a b
  inner_incl_left _ a y := (ContinuousLinearMap.adjoint_inner_right _ a y).symm

/-- Multiplication by `i` on mirror states, as a real-linear map. -/
def mulI : PiLp 2 SpaceQ →L[ℝ] PiLp 2 SpaceQ :=
  (Complex.I • ContinuousLinearMap.id ℂ (PiLp 2 SpaceQ)).restrictScalars ℝ

theorem mulI_apply (y : PiLp 2 SpaceQ) : mulI y = Complex.I • y := rfl

theorem mulI_mulI (y : PiLp 2 SpaceQ) : mulI (mulI y) = -y := by
  rw [mulI_apply, mulI_apply, smul_smul, Complex.I_mul_I, neg_one_smul]

theorem norm_mulI (y : PiLp 2 SpaceQ) : ‖mulI y‖ = ‖y‖ := by
  rw [mulI_apply, norm_smul, Complex.norm_I, one_mul]

theorem inner_mirrorEmb_mulI (N : ℕ) (a b : mirrorHidden hT hB N) :
    ⟪mirrorEmb hT hB N a, mulI (mirrorEmb hT hB N b)⟫_ℝ = 0 :=
  inner_mirrorReEmb_I (mirrorFE hT hB N a) (mirrorFE hT hB N b)

theorem adjoint_mirrorEmb_mulI (N : ℕ) (b : mirrorHidden hT hB N) :
    (mirrorEmb hT hB N).adjoint (mulI (mirrorEmb hT hB N b)) = 0 :=
  ext_inner_left ℝ fun w =>
    ((ContinuousLinearMap.adjoint_inner_right _ w _).trans (inner_mirrorEmb_mulI hT hB N w b)).trans
      (inner_zero_right w).symm

/-- **The mirror scheme (6.5) for complex data**: real and imaginary parts each run (6.5)
(`ApproxFEEC.complexify` with `J` = multiplication by `i`). -/
def mirrorFEMApprox : ApproxFEEC complexQℝ ℕ :=
  (mirrorFEMReal hT hB).complexify mulI mulI_mulI norm_mulI (adjoint_mirrorEmb_mulI hT hB)
    (inner_mirrorEmb_mulI hT hB)

theorem mirrorFEMApprox_isOrthogonal : ApproxFEEC.IsOrthogonal (mirrorFEMApprox hT hB) :=
  (mirrorFEMReal_isOrthogonal hT hB).complexify mulI mulI_mulI norm_mulI
    (adjoint_mirrorEmb_mulI hT hB) (inner_mirrorEmb_mulI hT hB)

/-- The complexified solution is the real solution of the real part plus `i` times the real
solution of the imaginary part. -/
theorem mirrorFEMApprox_sol (N : ℕ) (a b : mirrorHidden hT hB N) (t : ℝ) :
    (mirrorFEMApprox hT hB).sol N (WithLp.toLp 2 (a, b)) t =
      (mirrorFEMReal hT hB).sol N a t + mulI ((mirrorFEMReal hT hB).sol N b t) :=
  ApproxFEEC.complexify_sol (mirrorFEMReal hT hB) mulI mulI_mulI norm_mulI
    (adjoint_mirrorEmb_mulI hT hB) (inner_mirrorEmb_mulI hT hB) N a b t

/-- The discrete forms state of a solution of (6.5) read as a continuous forms state. -/
abbrev dState (N : ℕ) {T : ℝ} (s : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T 0) (t : ℝ) :
    REnergy :=
  EState.mk ((s.σ t : TU0) : W0) (bIncl1 (s.u t : BU1)) (s.M t : W2) (s.ρ t : Wv W2)

/-- **The real discrete solution of `mirrorFEMReal` is (6.5)**: from the initial state of a
solution `s` of (6.5) without source, `ιₙ e^{tLₙ} v = Rt(σₕ, uₕ, Mₕ, ρₕ)(t)` on `[0, T]`. -/
theorem mirrorFEMReal_sol_eq (N : ℕ) {T : ℝ} (hT0 : 0 ≤ T)
    (s : Feec.BGG.DiscreteSolution (mirrorWave hT hB N) T 0) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (mirrorFEMReal hT hB).sol N (DiscreteSolution.hiddenInit hT0 s) t =
      mirrorReEmb (dState hT hB N s t) :=
  congrArg mirrorReEmb (congrArg (EState.mapL ((TD0.domain.subtypeL) ∘L
    (mirrorFEM hT hB N).V0h.subtypeL) (bIncl1CLM ∘L (mirrorFEM hT hB N).Vt1h.subtypeL)
    (mirrorFEM hT hB N).W2h.subtypeL (mirrorFEM hT hB N).Wt2h.subtypeL)
    (DiscreteSolution.eq_group (mirrorWave_dt0_injective hT hB N)
      (mirrorWave_S0_surjective hT hB N) hT0 s t ht))

end Feec.Instances.EinsteinBianchi.FEM
