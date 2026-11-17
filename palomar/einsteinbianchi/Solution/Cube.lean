module

public import Solution.Abstract
public import Solution.Forms
public import Solution.Regularity
public import Feec.Models.Cube.WeakSymmetryFEM

/-!
# The BGG data (4.16) of the challenge on the cube are those of `Feec`

`cubeData` is `cubeDataOf D0 D1` for `Feec`'s minimal realizations `D0`, `D1` on the cube
(`cubeData_eq`, from `dMin_eq`), the connecting map `wedge` is `Feec.FiniteElement.wsL2`
(`wedge_eq`), and the domain of the componentwise operator is isometric to `Feec`'s vectors of
domain elements (`vecEquiv`). Through these, `IsBGG` and `IsStable` follow from
`Feec.Models.Cube.WeakSymmetry.bggStability_of` with the constant of
`Feec.Models.Cube.WeakSymmetry.exists_curlPotential_bound`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.1, §5.3

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace RealInnerProductSpace
open Set MeasureTheory

@[expose] public noncomputable section

namespace FEEC

open Feec.Domain Feec.FiniteElement Feec.Models.Cube.FEM Feec.Models.Cube.WeakSymmetry

variable {n : ℕ}

/-- The coefficients of `S(eₐ ⊗ dx_r) = dxₐ ∧ dx_r`. -/
theorem wsCoeff_eq {k : ℤ} (t : FormIdx n (k + 1)) (a : Fin n) (r : FormIdx n k) :
    wsCoeff k t (a, r) = if a ∈ t.1 ∧ r.1 = t.1.erase a then sgn a t.1 else 0 := by
  rw [wsCoeff, coordWedgeSum_apply]
  simp only [Pi.single_apply]
  rw [Finset.sum_eq_single a (fun i _ hia => by simp [hia]) (by simp)]
  simp only [ite_true]
  split_ifs with h
  · rw [Finset.sum_eq_single a (fun j _ hja => by simp [hja]) (fun ha => absurd h.1 ha)]
    simp [h.2, sgn_eq]
  · refine Finset.sum_eq_zero fun j hj => ?_
    by_cases hja : j = a
    · subst hja
      have : ¬ t.1.erase j = r.1 := fun e => h ⟨hj, e.symm⟩
      simp [this]
    · simp [hja]

theorem card_erase_of_mem {k : ℤ} (t : FormIdx n (k + 1)) {a : Fin n} (ha : a ∈ t.1) :
    ((t.1.erase a).card : ℤ) = k := by
  rw [Finset.card_erase_of_mem ha, Nat.cast_sub (Finset.card_pos.2 ⟨a, ha⟩), t.2]
  ring

/-- **The connecting map of the challenge is `Feec`'s `wsL2`.** -/
theorem wedge_eq (Ω : Set (Fin n → ℝ)) (k : ℤ) : wedge Ω k = wsL2 (Ω := Ω) k := by
  ext v t : 2
  rw [wsL2_apply, Fintype.sum_prod_type]
  simp only [wedge, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, PiLp.continuousLinearEquiv_symm_apply, PiLp.toLp_apply,
    ContinuousLinearMap.pi_apply, _root_.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : a ∈ t.1
  · rw [dite_eq_left ha, Finset.sum_eq_single ⟨t.1.erase a, card_erase_of_mem t ha⟩]
    · simp [wsCoeff_eq, ha]
    · intro r _ hr
      rw [wsCoeff_eq, ite_eq_right_iff.2 (fun h => absurd (Subtype.ext h.2) hr), zero_smul]
    · simp
  · rw [dite_eq_right ha]
    change (0 : _) = _
    exact (Finset.sum_eq_zero fun r _ => by
      rw [wsCoeff_eq, ite_eq_right_iff.2 (fun h => absurd h.1 ha), zero_smul]).symm

/-! ### `D(T)ⁿ` and `Feec`'s vectors of domain elements -/

section Vec

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] (T : E →ₗ.[ℝ] F)

/-- `D(T)ⁿ` (the domain of `vecOpC T`) as `Feec`'s vectors of elements of `D(T)`. -/
def vecEquiv : (vecOpC (n := n) T).domain ≃ₗᵢ[ℝ] PiLp 2 (fun _ : Fin n => T.domain) where
  toFun v := WithLp.toLp 2 fun a => ⟨(v : PiLp 2 fun _ : Fin n => E) a, v.2 a⟩
  invFun w := ⟨WithLp.toLp 2 fun a => (w a : E), fun a => (w a).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' v := by
    change ‖(WithLp.toLp 2 fun a => (⟨(v : PiLp 2 fun _ : Fin n => E) a, v.2 a⟩ : T.domain) :
      PiLp 2 (fun _ : Fin n => T.domain))‖ = ‖(v : PiLp 2 fun _ : Fin n => E)‖
    rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
    rfl

@[simp] theorem coe_vecEquiv_apply (v : (vecOpC (n := n) T).domain) (a : Fin n) :
    ((vecEquiv T v a : T.domain) : E) = (v : PiLp 2 fun _ : Fin n => E) a := rfl

@[simp] theorem coe_vecEquiv_symm_apply (w : PiLp 2 (fun _ : Fin n => T.domain)) (a : Fin n) :
    (((vecEquiv T).symm w : (vecOpC (n := n) T).domain) : PiLp 2 fun _ : Fin n => E) a =
      (w a : E) := rfl

end Vec

/-! ### The cube data -/

/-- **The cube data in `Feec`'s types and operators**: `cubeData` with `D0`, `D1`, `wsL2`
(`cubeData_eq`). -/
abbrev 𝒟 : WeakSymmetryData W0 W1 W2 (Wv W0) (Wv W1) (Wv W2) :=
  ⟨D0, D1, vecOpC D0, vecOpC D1, wsL2 (Ω := cubeDomain 3) 0, wsL2 (Ω := cubeDomain 3) 1⟩

/-- **`cubeData` is the data of `Feec`'s minimal realizations.** -/
theorem cubeData_eq : cubeData = (𝒟 : WeakSymmetryData (L2Form (cube 3) 0) (L2Form (cube 3) 1)
    (L2Form (cube 3) 2) (L2Vec (cube 3) 0) (L2Vec (cube 3) 1) (L2Vec (cube 3) 2)) := by
  change (⟨dMin (cube 3) 0, dMin (cube 3) 1, vecOpC (dMin (cube 3) 0), vecOpC (dMin (cube 3) 1),
    wedge (cube 3) 0, wedge (cube 3) 1⟩ : WeakSymmetryData (L2Form (cube 3) 0) (L2Form (cube 3) 1)
      (L2Form (cube 3) 2) (L2Vec (cube 3) 0) (L2Vec (cube 3) 1) (L2Vec (cube 3) 2)) = _
  rw [dMin_eq, dMin_eq, wedge_eq, wedge_eq]
  rfl

/-- `D(d̃⁰)` as `Feec`'s `H̊Λ⁰(Q)³`. -/
abbrev e0 : 𝒟.dt0.domain ≃ₗᵢ[ℝ] Wv U0 := vecEquiv D0
/-- `D(d̃¹)` as `Feec`'s `H̊Λ¹(Q)³`. -/
abbrev e1 : 𝒟.dt1.domain ≃ₗᵢ[ℝ] Wv U1 := vecEquiv D1

theorem incl0_e0 (φ : 𝒟.dt0.domain) : incl0 (e0 φ) = (φ : Wv W0) := rfl
theorem incl1_e1 (u : 𝒟.dt1.domain) : incl1 (e1 u) = (u : Wv W1) := rfl

theorem dt0_e0 (φ : 𝒟.dt0.domain) : incl1 (bggSegment.dt0 (e0 φ)) = 𝒟.dt0 φ := rfl
theorem dt1_e1 (u : 𝒟.dt1.domain) : bggSegment.dt1 (e1 u) = 𝒟.dt1 u := rfl

theorem S0_e0 (φ : 𝒟.dt0.domain) : ((bggSegment.S0 (e0 φ) : U1) : W1) = 𝒟.S0 φ := rfl

theorem S1_e1 (u : 𝒟.dt1.domain) : bggSegment.S1 (e1 u) = 𝒟.S1 u := rfl

theorem norm_dt0_e0 (φ : 𝒟.dt0.domain) : ‖bggSegment.dt0 (e0 φ)‖ = ‖𝒟.dt0 φ‖ :=
  (norm_incl1 (bggSegment.dt0 (e0 φ))).symm

theorem dt0_e0_symm (φ : Wv U0) : 𝒟.dt0 (e0.symm φ) = incl1 (bggSegment.dt0 φ) := rfl

theorem norm_dt0_e0_symm (φ : Wv U0) : ‖𝒟.dt0 (e0.symm φ)‖ = ‖bggSegment.dt0 φ‖ :=
  norm_incl1 (bggSegment.dt0 φ)

theorem S0_e0_symm (φ : Wv U0) : 𝒟.S0 (e0.symm φ) = ((bggSegment.S0 φ : U1) : W1) := rfl

/-- A vector of `H̊Λ¹(Q)` elements as an element of `D(d̃¹)`. -/
def ofWv1 (x : Wv U1) : 𝒟.dt1.domain := ⟨incl1 x, fun a => (x a).2⟩

theorem coe_ofWv1 (x : Wv U1) : ((ofWv1 x : 𝒟.dt1.domain) : Wv W1) = incl1 x := rfl

theorem norm_ofWv1 (x : Wv U1) : ‖((ofWv1 x : 𝒟.dt1.domain) : Wv W1)‖ = ‖x‖ :=
  norm_incl1 x

theorem dt1_ofWv1 (x : Wv U1) : 𝒟.dt1 (ofWv1 x) = bggSegment.dt1 x := rfl

theorem S1_ofWv1 (x : Wv U1) : 𝒟.S1 (ofWv1 x) = bggSegment.S1 x := rfl

/-- **The cube data are BGG data.** -/
theorem isBGG_𝒟 : 𝒟.IsBGG := by
  refine ⟨fun x => ⟨D0_mem_D1 x, D1_D0 x⟩, fun x => ⟨fun a => D0_mem_D1 ⟨_, x.2 a⟩,
    PiLp.ext fun a => D1_D0 ⟨_, x.2 a⟩⟩, fun ψ => ?_⟩
  exact wsL2_mem_minimal (isOpen_cubeDomain 3) 0 (v := (ψ : Wv W0)) fun a => ψ.2 a

/-- `‖S⁰‖ ≤ √2`, `‖S¹‖ ≤ √2` (`‖S v‖² ≤ (k + 1) ‖v‖²`). -/
theorem norm_wsL2_le (k : ℕ) (hk : k ≤ 1) : ‖wsL2 (Ω := cubeDomain 3) (n := 3) (k : ℤ)‖ ≤ √2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
  have h := norm_wsL2_sq_le (Ω := cubeDomain 3) (n := 3) (k : ℤ) v
  have hk' : ((k : ℤ) : ℝ) + 1 ≤ 2 := by
    have : (k : ℝ) ≤ 1 := by exact_mod_cast hk
    push_cast; linarith
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [mul_pow, Real.sq_sqrt (by norm_num)]
  exact h.trans (mul_le_mul_of_nonneg_right hk' (sq_nonneg _))

end FEEC
