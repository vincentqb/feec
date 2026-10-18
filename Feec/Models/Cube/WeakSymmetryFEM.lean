module

public import Feec.Models.Cube.WeakSymmetryEstimates
public import Feec.Models.Cube.PolyRate
public import Feec.HilbertComplex.BGG.WeakConsistency

/-!
# The finite element method for the BGG complex with weak symmetries on the cube

WIP
-/

open scoped InnerProductSpace RealInnerProductSpace
open MeasureTheory Set Filter

@[expose] public noncomputable section

/-! ### Weak consistency against a functional bound -/

namespace Feec.BGG.Discrete

variable {V0 V1 W2 Vt0 Vt1 Wt2 : Type*}
  [NormedAddCommGroup V0] [InnerProductSpace ℝ V0]
  [NormedAddCommGroup V1] [InnerProductSpace ℝ V1]
  [NormedAddCommGroup W2] [InnerProductSpace ℝ W2]
  [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0]
  [NormedAddCommGroup Vt1] [InnerProductSpace ℝ Vt1]
  [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2]
  {D : Feec.BGG.Segment ℝ V0 V1 W2 Vt0 Vt1 Wt2} {Q : Feec.BGG.Discrete D}

/-- **Weak consistency from regular potentials, `d¹*`-regularity as a functional bound**: the
variant of `weakConsistency_of_regularPotential` with the hypothesis `⟪z, d w⟫ = ⟪z', w⟫`
(`z' ∈ V¹`) replaced by `|⟪z, d w⟫| ≤ M ‖w‖` for all `w ∈ V¹`. This is the form that applies
when `V¹` carries the `W`-norm but is not complete (as `H̊Λ¹(Q) ⊆ L²Λ¹(Q)`), where
`d¹* z ∈ L²` has no representative in `V¹`. -/
theorem weakConsistency_of_regularPotential_of_bound {Cp CR CS CP : ℝ}
    (H : Feec.BGG.Stability D Cp CR CS) (B : Q.Bounded CP) {Xr : Type*} [NormedAddCommGroup Xr]
    [NormedSpace ℝ Xr] {Cinc Creg h Capp : ℝ} (hh : 0 ≤ h) (hCapp : 0 ≤ Capp)
    (Rg : Q.RegularPotential Xr Cinc Creg Capp h)
    (happ0 : ∀ ψ ∈ Q.Vt0h, ‖D.S0 ψ - Q.S0h ψ‖ ^ 2 ≤ (Capp * h) ^ 2 * Feec.BGG.graphSq D.dt0 ψ)
    {z : W2} {M : ℝ} (hM : 0 ≤ M) (hz : ∀ w, |⟪z, D.d1 w⟫| ≤ M * ‖w‖) :
    ∀ v ∈ Q.Vt1h, |⟪z, (D.S1 - Q.S1h) v⟫| ≤
      Capp * h * weakConsistencyConst Cp CS CP Cinc Creg ‖z‖ M *
        √(Feec.BGG.graphSq D.dt1 v) := by
  intro v hv
  have hp := H.Cp_nonneg; have hS := H.CS_nonneg; have hP := B.CP_nonneg
  have hι := Rg.Cinc_nonneg; have hr := Rg.Creg_nonneg
  obtain ⟨y, hy1, hy2⟩ := Rg.exists_potential v hv
  set w := Rg.R y with hw
  set G := √(Feec.BGG.graphSq D.dt1 v) with hG
  have hvG : ‖v‖ ≤ G := (Real.le_sqrt (norm_nonneg _) (Feec.BGG.graphSq_nonneg _ _)).2 (by
    unfold Feec.BGG.graphSq; nlinarith [sq_nonneg ‖D.dt1 v‖])
  have hdG : ‖D.dt1 v‖ ≤ G := (Real.le_sqrt (norm_nonneg _) (Feec.BGG.graphSq_nonneg _ _)).2 (by
    unfold Feec.BGG.graphSq; nlinarith [sq_nonneg ‖v‖])
  have hdv : D.dt1 v ∈ Q.Wt2h := Q.dt1_mem v hv
  have hdPw : D.dt1 (Q.Pt1 w) = D.dt1 v := by rw [Q.commt1, hy1, Q.Pt2_id _ hdv]
  have hker : D.dt1 (v - Q.Pt1 w) = 0 := by rw [map_sub, hdPw, sub_self]
  obtain ⟨ψ, hψ, hψeq⟩ := exact_bot_h H (Submodule.sub_mem _ hv (Q.Pt1_mem w)) hker
  have hsplit : (D.S1 - Q.S1h) v = D.d1 (Q.S0h ψ - D.S0 ψ) +
      ((D.S1 - Q.S1h) w - (D.S1 - Q.S1h) (w - Q.Pt1 w)) := by
    calc (D.S1 - Q.S1h) v = (D.S1 - Q.S1h) (D.dt0 ψ + w - (w - Q.Pt1 w)) := by
          congr 1; rw [hψeq]; abel
      _ = _ := by rw [map_sub, map_add, S1_sub_S1h_dt0]; abel
  have hgrad : |⟪z, D.d1 (Q.S0h ψ - D.S0 ψ)⟫| ≤
      M * (Capp * h * √(Feec.BGG.graphSq D.dt0 ψ)) := by
    refine (hz _).trans (mul_le_mul_of_nonneg_left ?_ hM)
    rw [norm_sub_rev]
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    rw [mul_pow, Real.sq_sqrt (Feec.BGG.graphSq_nonneg _ _)]; exact happ0 ψ hψ
  have hψg : √(Feec.BGG.graphSq D.dt0 ψ) ≤ √(1 + Cp ^ 2) * ‖D.dt0 ψ‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (D.dt0 ψ)), ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    have := pow_le_pow_left₀ (norm_nonneg _) (H.poinct0 ψ) 2
    unfold Feec.BGG.graphSq; nlinarith
  have hwn : ‖w‖ ≤ Cinc * Creg * ‖D.dt1 v‖ := (Rg.norm_R_le y).trans (by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hy2 hι)
  have hPw : ‖Q.Pt1 w‖ ≤ CP * (1 + Cinc * Creg) * ‖D.dt1 v‖ := by
    have hg := B.Pt1 w
    have hgw : Feec.BGG.graphSq D.dt1 w ≤ ((1 + Cinc * Creg) * ‖D.dt1 v‖) ^ 2 := by
      unfold Feec.BGG.graphSq; rw [hy1]
      have := pow_le_pow_left₀ (norm_nonneg _) hwn 2
      nlinarith [norm_nonneg (D.dt1 v), mul_nonneg (mul_nonneg hι hr) (norm_nonneg (D.dt1 v))]
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    calc ‖Q.Pt1 w‖ ^ 2 ≤ Feec.BGG.graphSq D.dt1 (Q.Pt1 w) := by
          unfold Feec.BGG.graphSq; nlinarith [sq_nonneg ‖D.dt1 (Q.Pt1 w)‖]
      _ ≤ CP ^ 2 * Feec.BGG.graphSq D.dt1 w := hg
      _ ≤ CP ^ 2 * ((1 + Cinc * Creg) * ‖D.dt1 v‖) ^ 2 := by gcongr
      _ = _ := by ring
  have hdψ : ‖D.dt0 ψ‖ ≤ (1 + CP * (1 + Cinc * Creg)) * G := by
    rw [hψeq]
    calc ‖v - Q.Pt1 w‖ ≤ ‖v‖ + ‖Q.Pt1 w‖ := norm_sub_le _ _
      _ ≤ G + CP * (1 + Cinc * Creg) * G :=
          add_le_add hvG (hPw.trans (mul_le_mul_of_nonneg_left hdG (by positivity)))
      _ = _ := by ring
  have hx : D.dt1 (w - Q.Pt1 w) = 0 := by rw [map_sub, hdPw, hy1, sub_self]
  have hSx : ‖(D.S1 - Q.S1h) (w - Q.Pt1 w)‖ ≤ (1 + CP) * CS * (Capp * h * ‖y‖) := by
    have hS1x : ‖D.S1 (w - Q.Pt1 w)‖ ≤ CS * ‖w - Q.Pt1 w‖ := by
      have := H.boundS1 (w - Q.Pt1 w)
      unfold Feec.BGG.graphSq at this; rw [hx, norm_zero] at this
      refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
      rw [mul_pow]; simpa using this
    rw [LinearMap.sub_apply, S1h_apply]
    calc ‖D.S1 (w - Q.Pt1 w) - Q.P2 (D.S1 (w - Q.Pt1 w))‖
        ≤ ‖D.S1 (w - Q.Pt1 w)‖ + ‖Q.P2 (D.S1 (w - Q.Pt1 w))‖ := norm_sub_le _ _
      _ ≤ ‖D.S1 (w - Q.Pt1 w)‖ + CP * ‖D.S1 (w - Q.Pt1 w)‖ := add_le_add le_rfl (B.P2 _)
      _ = (1 + CP) * ‖D.S1 (w - Q.Pt1 w)‖ := by ring
      _ ≤ (1 + CP) * (CS * ‖w - Q.Pt1 w‖) :=
          mul_le_mul_of_nonneg_left hS1x (by linarith)
      _ ≤ (1 + CP) * (CS * (Capp * h * ‖y‖)) := by
          gcongr; exact Rg.approx_Pt1 y
      _ = _ := by ring
  have hco : ‖(D.S1 - Q.S1h) w - (D.S1 - Q.S1h) (w - Q.Pt1 w)‖ ≤
      (1 + (1 + CP) * CS) * (Capp * h) * (Creg * G) := by
    have hyG : ‖y‖ ≤ Creg * G := hy2.trans (mul_le_mul_of_nonneg_left hdG hr)
    calc _ ≤ ‖(D.S1 - Q.S1h) w‖ + ‖(D.S1 - Q.S1h) (w - Q.Pt1 w)‖ := norm_sub_le _ _
      _ ≤ Capp * h * ‖y‖ + (1 + CP) * CS * (Capp * h * ‖y‖) := add_le_add (Rg.approx_S1 y) hSx
      _ = (1 + (1 + CP) * CS) * (Capp * h) * ‖y‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hyG (by positivity)
  rw [hsplit, inner_add_right]
  calc |⟪z, D.d1 (Q.S0h ψ - D.S0 ψ)⟫ + ⟪z, (D.S1 - Q.S1h) w - (D.S1 - Q.S1h) (w - Q.Pt1 w)⟫|
      ≤ |⟪z, D.d1 (Q.S0h ψ - D.S0 ψ)⟫|
        + |⟪z, (D.S1 - Q.S1h) w - (D.S1 - Q.S1h) (w - Q.Pt1 w)⟫| := abs_add_le _ _
    _ ≤ M * (Capp * h * √(Feec.BGG.graphSq D.dt0 ψ))
        + ‖z‖ * ((1 + (1 + CP) * CS) * (Capp * h) * (Creg * G)) :=
        add_le_add hgrad ((abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left hco (norm_nonneg _)))
    _ ≤ M * (Capp * h * (√(1 + Cp ^ 2) * ((1 + CP * (1 + Cinc * Creg)) * G)))
        + ‖z‖ * ((1 + (1 + CP) * CS) * (Capp * h) * (Creg * G)) := by
        gcongr
        exact hψg.trans (mul_le_mul_of_nonneg_left hdψ (Real.sqrt_nonneg _))
    _ = _ := by unfold weakConsistencyConst; ring

end Feec.BGG.Discrete

namespace Feec.Models.Cube.WeakSymmetry

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex Feec.Models.Cube.FEM

/-! ### `d_min` of the cube complex in degrees `0`, `1` -/

section Dmin

variable {S' : (complexMin 3).Subcomplex}

theorem mem_D0_domain {x : W0} (hx : x ∈ ((complexMin 3).d 0 1).domain) : x ∈ D0.domain :=
  complexMin_d01 ▸ hx

theorem mem_D1_domain {x : W1} (hx : x ∈ ((complexMin 3).d 1 2).domain) : x ∈ D1.domain :=
  complexMin_d12 ▸ hx

theorem mem_dom01 {x : W0} (hx : x ∈ D0.domain) : x ∈ ((complexMin 3).d 0 1).domain :=
  complexMin_d01.symm ▸ hx

theorem mem_dom12 {x : W1} (hx : x ∈ D1.domain) : x ∈ ((complexMin 3).d 1 2).domain :=
  complexMin_d12.symm ▸ hx

theorem d01_apply (x : ((complexMin 3).d 0 1).domain) :
    (complexMin 3).d 0 1 x = D0 ⟨x, mem_D0_domain x.2⟩ :=
  LinearPMap.apply_eq_of_eq' complexMin_d01 x

theorem d12_apply (x : ((complexMin 3).d 1 2).domain) :
    (complexMin 3).d 1 2 x = D1 ⟨x, mem_D1_domain x.2⟩ :=
  LinearPMap.apply_eq_of_eq' complexMin_d12 x

theorem mem_D0_of_mem_V {x : W0} (hx : x ∈ S'.V 0) : x ∈ D0.domain :=
  mem_D0_domain (S'.le_domain 0 1 hx)

theorem mem_D1_of_mem_V {x : W1} (hx : x ∈ S'.V 1) : x ∈ D1.domain :=
  mem_D1_domain (S'.le_domain 1 2 hx)

theorem D0_mem_V (x : U0) (hx : (x : W0) ∈ S'.V 0) : D0 x ∈ S'.V 1 := by
  have h := S'.mapsTo 0 1 x hx
  rwa [d01_apply] at h

theorem D1_mem_V (x : U1) (hx : (x : W1) ∈ S'.V 1) : D1 x ∈ S'.V 2 := by
  have h := S'.mapsTo 1 2 x hx
  rwa [d12_apply] at h

/-- `d π = π d` in degree `0`. -/
theorem D0_π (P : S'.CochainProjection) (x : U0) :
    D0 ⟨P.π 0 x, mem_D0_of_mem_V (P.mem 0 x)⟩ = P.π 1 (D0 x) := by
  have h := P.comm 0 1 ⟨x, mem_dom01 x.2⟩
  rw [d01_apply, d01_apply] at h
  exact h

/-- `d π = π d` in degree `1`. -/
theorem D1_π (P : S'.CochainProjection) (x : U1) :
    D1 ⟨P.π 1 x, mem_D1_of_mem_V (P.mem 1 x)⟩ = P.π 2 (D1 x) := by
  have h := P.comm 1 2 ⟨x, mem_dom12 x.2⟩
  rw [d12_apply, d12_apply] at h
  exact h

end Dmin

/-! ### The discrete spaces and projections -/

section Discretization

/-- The `ℝ³`-valued fields with components in `P`. -/
def tsub {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (P : Submodule ℝ V) :
    Submodule ℝ (Wv V) where
  carrier := {x | ∀ a, x a ∈ P}
  add_mem' hx hy a := P.add_mem (hx a) (hy a)
  zero_mem' := fun _ => P.zero_mem
  smul_mem' c _ hx a := P.smul_mem c (hx a)

theorem mem_tsub {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {P : Submodule ℝ V}
    {x : Wv V} : x ∈ tsub P ↔ ∀ a, x a ∈ P := Iff.rfl

variable {S' : (complexMin 3).Subcomplex}

/-- A cochain projection in degree `0`, on `H̊Λ⁰(Q)`. -/
def projU0 (P : S'.CochainProjection) : U0 →ₗ[ℝ] U0 :=
  LinearMap.codRestrict D0.domain (P.π 0 ∘ₗ D0.domain.subtype)
    fun x => mem_D0_of_mem_V (P.mem 0 x)

/-- A cochain projection in degree `1`, on `H̊Λ¹(Q)`. -/
def projU1 (P : S'.CochainProjection) : U1 →ₗ[ℝ] U1 :=
  LinearMap.codRestrict D1.domain (P.π 1 ∘ₗ D1.domain.subtype)
    fun x => mem_D1_of_mem_V (P.mem 1 x)

@[simp] theorem coe_projU0 (P : S'.CochainProjection) (x : U0) :
    ((projU0 P x : U0) : W0) = P.π 0 x := rfl

@[simp] theorem coe_projU1 (P : S'.CochainProjection) (x : U1) :
    ((projU1 P x : U1) : W1) = P.π 1 x := rfl

variable (ST SB : (complexMin 3).Subcomplex)

/-- **The discretization of the BGG data (4.16) on the cube** by a pair of subcomplexes `ST`
(top row) and `SB` (bottom row, componentwise) of `H̊Λ(Q)`, with cochain projections `PT`, `PB`
(componentwise on the bottom row). -/
def bggDiscrete (PT : ST.CochainProjection) (PB : SB.CochainProjection) :
    Feec.BGG.Discrete bggSegment where
  V0h := (ST.V 0).comap D0.domain.subtype
  V1h := (ST.V 1).comap D1.domain.subtype
  W2h := ST.V 2
  Vt0h := tsub ((SB.V 0).comap D0.domain.subtype)
  Vt1h := tsub ((SB.V 1).comap D1.domain.subtype)
  Wt2h := tsub (SB.V 2)
  d0_mem x hx := D0_mem_V x hx
  d1_mem x hx := D1_mem_V x hx
  dt0_mem x hx a := D0_mem_V (x a) (hx a)
  dt1_mem x hx a := D1_mem_V (x a) (hx a)
  P0 := projU0 PT
  P1 := projU1 PT
  P2 := PT.π 2
  Pt0 := piMap (projU0 PB)
  Pt1 := piMap (projU1 PB)
  Pt2 := piMap (PB.π 2)
  P0_mem x := PT.mem 0 x
  P1_mem x := PT.mem 1 x
  P2_mem x := PT.mem 2 x
  Pt0_mem x a := PB.mem 0 (x a)
  Pt1_mem x a := PB.mem 1 (x a)
  Pt2_mem x a := PB.mem 2 (x a)
  P0_id x hx := Subtype.ext (PT.proj 0 x hx)
  P1_id x hx := Subtype.ext (PT.proj 1 x hx)
  P2_id x hx := PT.proj 2 x hx
  Pt0_id x hx := PiLp.ext fun a => Subtype.ext (PB.proj 0 (x a) (hx a))
  Pt1_id x hx := PiLp.ext fun a => Subtype.ext (PB.proj 1 (x a) (hx a))
  Pt2_id x hx := PiLp.ext fun a => PB.proj 2 (x a) (hx a)
  comm0 x := Subtype.ext (D0_π PT x)
  comm1 x := D1_π PT x
  commt0 x := PiLp.ext fun a => Subtype.ext (D0_π PB (x a))
  commt1 x := PiLp.ext fun a => D1_π PB (x a)

variable {ST SB}

theorem norm_sq_wv {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (x : Wv V) :
    ‖x‖ ^ 2 = ∑ a, ‖x a‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ x

/-- **Uniform bounds of the discrete projections** from graph-norm bounds of `PT`, `PB` in degree
`1 → 2` and `L²` bounds in degree `2`. -/
theorem bggDiscrete_bounded {PT : ST.CochainProjection} {PB : SB.CochainProjection} {C : ℝ}
    (hC0 : 0 ≤ C) (hT : ∀ x, ‖PT.π 2 x‖ ≤ C * ‖x‖) (hTg : PT.IsGraphBounded 1 2 C)
    (hBg : PB.IsGraphBounded 1 2 C) : (bggDiscrete ST SB PT PB).Bounded C where
  CP_nonneg := hC0
  P1 x := by
    have h := hTg ⟨x, mem_dom12 x.2⟩
    rw [d12_apply, d12_apply] at h
    exact h
  P2 z := hT z
  Pt1 v := by
    have e : ∀ w : Wv U1, Feec.BGG.graphSq bggSegment.dt1 w =
        ∑ a, (‖w a‖ ^ 2 + ‖segD1 (w a)‖ ^ 2) := by
      intro w
      unfold Feec.BGG.graphSq
      rw [norm_sq_wv w, norm_sq_wv (bggSegment.dt1 w), ← Finset.sum_add_distrib]
      rfl
    rw [e, e, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have h := hBg ⟨v a, mem_dom12 (v a).2⟩
    rw [d12_apply, d12_apply] at h
    exact h

theorem finiteDimensional_comap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P K : Submodule ℝ E) [FiniteDimensional ℝ P] : FiniteDimensional ℝ (P.comap K.subtype) := by
  let f : P.comap K.subtype →ₗ[ℝ] P :=
    { toFun := fun x => ⟨((x : K) : E), x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective f fun x y h => Subtype.ext (Subtype.ext ?_)
  have h' := congrArg Subtype.val h
  exact h'

theorem finiteDimensional_tsub {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : Submodule ℝ V) [FiniteDimensional ℝ P] : FiniteDimensional ℝ (tsub P) := by
  let f : tsub P →ₗ[ℝ] (Fin 3 → P) :=
    { toFun := fun x a => ⟨(x : Wv V) a, x.2 a⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective f fun x y h => Subtype.ext (PiLp.ext fun a => ?_)
  exact congrArg Subtype.val (congrFun h a)

theorem bggDiscrete_Pt1 (PT : ST.CochainProjection) (PB : SB.CochainProjection) :
    (bggDiscrete ST SB PT PB).Pt1 = piMap (projU1 PB) := rfl

theorem bggDiscrete_Pt0 (PT : ST.CochainProjection) (PB : SB.CochainProjection) :
    (bggDiscrete ST SB PT PB).Pt0 = piMap (projU0 PB) := rfl

theorem bggSegment_dt1 : bggSegment.dt1 = piMap segD1 := rfl

theorem bggSegment_dt0 : bggSegment.dt0 = piMap segD0 := rfl

theorem graphSq_piMap {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] (f : V →ₗ[ℝ] W) (x : Wv V) :
    Feec.BGG.graphSq (piMap f) x = ∑ a, Feec.BGG.graphSq f (x a) := by
  unfold Feec.BGG.graphSq
  rw [norm_sq_wv, norm_sq_wv, ← Finset.sum_add_distrib]
  rfl

end Discretization

/-! ### Compatibility (5.4) of the smoothed projections -/

section Compatibility

open PolySeq

variable (M : SimplicialMesh 3) (p : SmoothingParam (Fin 3 → ℝ)) (hΩ : MeasurableSet M.domain)

/-- The smoothed components `R̃ yₐ` of an `ℝ³`-valued `0`-form, as continuous forms. -/
def smoothVec (y : PiLp 2 (fun _ : Fin 3 => L2F ℝ M.domain (formIdx 3 0))) :
    Fin 3 → contForms 3 :=
  fun a => Submodule.inclusion c1Forms_le_contForms (smoothForm p hΩ ((0 : ℕ) : ℤ) (y a))

/-- `R S⁰ y = c S⁰ R̃ y` on continuous forms. -/
theorem smoothForm_wsL2_zero (y : PiLp 2 (fun _ : Fin 3 => L2F ℝ M.domain (formIdx 3 0))) :
    Submodule.inclusion c1Forms_le_contForms
        (smoothForm p hΩ (((0 : ℕ) : ℤ) + 1) (wsL2 (Ω := M.domain) ((0 : ℕ) : ℤ) y)) =
      p.factor • coordWedgeC (smoothVec M p hΩ y) :=
  Subtype.ext (smoothForm_wsL2 p hΩ 0 y)

/-- **The smoothed interpolant of `S⁰ y`** is `c Π¹ S⁰ Π̃⁰ R̃ y`: it only depends on the
canonical interpolants `Π̃⁰ R̃ yₐ` of the bottom row (corrected Prop 5.7). -/
theorem smoothedInterp_wsL2_zero (y : PiLp 2 (fun _ : Fin 3 => L2F ℝ M.domain (formIdx 3 0))) :
    (polyElement 3 lowestOrder).smoothedInterp M p hΩ (((0 : ℕ) : ℤ) + 1)
        (wsL2 (Ω := M.domain) ((0 : ℕ) : ℤ) y) =
      (polyElement 3 lowestOrder).glue M ((1 : ℕ) : ℤ)
        ((p.factor • bggS0h M ((polyElement 3 lagrangeP2).tensorInterp M 3 0
          (smoothVec M p hΩ y)) : (polyElement 3 lowestOrder).globalSpace M 1) :
          (polyElement 3 lowestOrder).Piecewise M 1) := by
  change (polyElement 3 lowestOrder).glue M ((1 : ℕ) : ℤ)
      ((polyElement 3 lowestOrder).globalInterp M 1 (Submodule.inclusion c1Forms_le_contForms
        (smoothForm p hΩ (((0 : ℕ) : ℤ) + 1) (wsL2 (Ω := M.domain) ((0 : ℕ) : ℤ) y))) :
          (polyElement 3 lowestOrder).Piecewise M 1) = _
  rw [smoothForm_wsL2_zero, map_smul, bggS0h_tensorInterp]

/-- **Compatibility of the smoothed interpolants (mesh level)**: if the bottom-row smoothed
interpolants of `y`, `y'` agree componentwise, so do the top-row smoothed interpolants of
`S⁰ y`, `S⁰ y'`. -/
theorem smoothedInterp_wsL2_zero_eq (hM : IsOpen M.domain)
    {y y' : PiLp 2 (fun _ : Fin 3 => L2F ℝ M.domain (formIdx 3 0))}
    (h : ∀ a, (polyElement 3 lagrangeP2).smoothedInterp M p hΩ ((0 : ℕ) : ℤ) (y a) =
      (polyElement 3 lagrangeP2).smoothedInterp M p hΩ ((0 : ℕ) : ℤ) (y' a)) :
    (polyElement 3 lowestOrder).smoothedInterp M p hΩ (((0 : ℕ) : ℤ) + 1)
        (wsL2 (Ω := M.domain) ((0 : ℕ) : ℤ) y) =
      (polyElement 3 lowestOrder).smoothedInterp M p hΩ (((0 : ℕ) : ℤ) + 1)
        (wsL2 (Ω := M.domain) ((0 : ℕ) : ℤ) y') := by
  rw [smoothedInterp_wsL2_zero, smoothedInterp_wsL2_zero]
  have ht : (polyElement 3 lagrangeP2).tensorInterp M 3 0 (smoothVec M p hΩ y) =
      (polyElement 3 lagrangeP2).tensorInterp M 3 0 (smoothVec M p hΩ y') := by
    funext a
    exact Subtype.ext ((polyElement 3 lagrangeP2).glue_injective M hM 0 (h a))
  rw [ht]

/-- The mesh-level compatibility, transported along `M.domain = Θ`. -/
theorem commutingMapOfEqMin_wsL2_zero_eq (hM : IsOpen M.domain) (hb : Bornology.IsBounded M.domain)
    {x₀ : Fin 3 → ℝ} {s₀ : ℝ}
    (hstar : ∀ y ∈ M.domain, ∀ z ∈ Metric.ball x₀ s₀, segment ℝ z y ⊆ M.domain)
    (hp : p.IsMinimal x₀ s₀) (y₀ : Fin 3 → ℝ)
    (hstar' : ∀ x ∈ closure M.domain, ∀ t : ℝ, 0 ≤ t → t < 1 → y₀ + t • (x - y₀) ∈ M.domain)
    {Θ : Set (Fin 3 → ℝ)} (e : M.domain = Θ) (hΘ : IsOpen Θ)
    {y y' : PiLp 2 (fun _ : Fin 3 => L2F ℝ Θ (formIdx 3 0))}
    (h : ∀ a, ((deRham ℝ 3).commutingMapOfEqMin e hM hΘ
        ((polyElement 3 lagrangeP2).smoothedCommutingMapMin M p hM hb hstar hp y₀ hstar')).Q 0
          (y a) = ((deRham ℝ 3).commutingMapOfEqMin e hM hΘ
        ((polyElement 3 lagrangeP2).smoothedCommutingMapMin M p hM hb hstar hp y₀ hstar')).Q 0
          (y' a)) :
    ((deRham ℝ 3).commutingMapOfEqMin e hM hΘ
        ((polyElement 3 lowestOrder).smoothedCommutingMapMin M p hM hb hstar hp y₀ hstar')).Q 1
          (wsL2 (Ω := Θ) 0 y) = ((deRham ℝ 3).commutingMapOfEqMin e hM hΘ
        ((polyElement 3 lowestOrder).smoothedCommutingMapMin M p hM hb hstar hp y₀ hstar')).Q 1
          (wsL2 (Ω := Θ) 0 y') := by
  subst e
  exact smoothedInterp_wsL2_zero_eq M p hM.measurableSet hM h

end Compatibility

/-! ### Prop 5.9(1) on the vanishing-DOF spaces -/

section Prop59One

open PolySeq

/-- `S⁰ = wsL2 0`, with target `L²(Ω; Λ¹)`. -/
abbrev wsZero {Ω : Set (Fin 3 → ℝ)} :
    PiLp 2 (fun _ : Fin 3 => L2F ℝ Ω (formIdx 3 0)) →L[ℝ] L2F ℝ Ω (formIdx 3 1) :=
  wsL2 (Ω := Ω) 0

/-- **Prop 5.9(1) with vanishing boundary DOFs (mesh level)**: for `ψ ∈ P₂Λ̊⁰ ⊗ ℝ³` there is
`w ∈ P₁⁻Λ̊¹` (the canonical `Π¹S⁰ψ`) with `‖S⁰ψ − w‖ ≤ C h ‖∇ψ‖`, `C` independent of `N`. -/
theorem exists_sub_wsL2_le_mesh : ∃ C, 0 ≤ C ∧ ∀ (N : ℕ)
    (ψ : PiLp 2 (fun _ : Fin 3 => L2F ℝ (mesh 3 N).domain (formIdx 3 0)))
    (_ : ∀ a, ψ a ∈ (polyElement 3 lagrangeP2).V₀ (mesh 3 N) 0)
    (hd : ∀ a, ψ a ∈ ((extDerivOp ℝ 3 0).minimal (mesh 3 N).domain).domain),
    ∃ w ∈ (polyElement 3 lowestOrder).V₀ (mesh 3 N) 1,
      ‖wsZero ψ - w‖ ≤ C * hN N *
        ‖(WithLp.toLp 2 fun a => (extDerivOp ℝ 3 0).minimal (mesh 3 N).domain ⟨ψ a, hd a⟩ :
          PiLp 2 (fun _ : Fin 3 => L2F ℝ (mesh 3 N).domain (formIdx 3 1)))‖ := by
  obtain ⟨C, hC0, hC⟩ := norm_sub_glue_bggS0h_le
  refine ⟨C, hC0, fun N ψ hψ hd => ?_⟩
  have hψ' : ∀ a, ∃ v : (polyElement 3 lagrangeP2).globalSpace₀ (mesh 3 N) 0,
      (polyElement 3 lagrangeP2).glue (mesh 3 N) ((0 : ℕ) : ℤ)
        (v : (polyElement 3 lagrangeP2).Piecewise (mesh 3 N) 0) = ψ a := fun a => hψ a
  choose u hu using hψ'
  set u' : Fin 3 → (polyElement 3 lagrangeP2).globalSpace (mesh 3 N) 0 :=
    fun a => ⟨(u a : (polyElement 3 lagrangeP2).Piecewise (mesh 3 N) 0), (u a).2.1⟩
  have hψe : ψ = (polyElement 3 lagrangeP2).tensorGlue (mesh 3 N) 3 ((0 : ℕ) : ℤ)
      fun a => ((u' a : (polyElement 3 lagrangeP2).globalSpace (mesh 3 N) 0) :
        (polyElement 3 lagrangeP2).Piecewise (mesh 3 N) 0) :=
    PiLp.ext fun a => (hu a).symm
  have hmem : ((bggS0h (mesh 3 N) u' : (polyElement 3 lowestOrder).globalSpace (mesh 3 N) 1) :
      (polyElement 3 lowestOrder).Piecewise (mesh 3 N) 1) ∈
        (polyElement 3 lowestOrder).globalSpace₀ (mesh 3 N) 1 :=
    wsPiecewise_mem_globalSpace₀ lagrangeP2_constOneTest_zero fun a => (u a).2
  refine ⟨(polyElement 3 lowestOrder).glue (mesh 3 N) (((0 : ℕ) : ℤ) + 1)
    ((bggS0h (mesh 3 N) u' : (polyElement 3 lowestOrder).globalSpace (mesh 3 N) 1) :
      (polyElement 3 lowestOrder).Piecewise (mesh 3 N) 1), ⟨⟨_, hmem⟩, rfl⟩, ?_⟩
  have hd' : (WithLp.toLp 2 fun a => (extDerivOp ℝ 3 0).minimal (mesh 3 N).domain ⟨ψ a, hd a⟩ :
      PiLp 2 (fun _ : Fin 3 => L2F ℝ (mesh 3 N).domain (formIdx 3 1))) =
      (polyElement 3 lagrangeP2).tensorGlue (mesh 3 N) 3 ((0 + 1 : ℕ) : ℤ)
        fun a => (polyElement 3 lagrangeP2).dPiecewise (mesh 3 N) 0
          ((u' a : (polyElement 3 lagrangeP2).globalSpace (mesh 3 N) 0) :
            (polyElement 3 lagrangeP2).Piecewise (mesh 3 N) 0) := by
    refine PiLp.ext fun a => ?_
    obtain ⟨h, hval⟩ := (polyElement 3 lagrangeP2).glue_mem_minimal (mesh 3 N)
      (isOpen_mesh_domain 3 N) (center 3) (strictStar_mesh 3 N) 0 (u a)
    have e : (⟨ψ a, hd a⟩ : ((extDerivOp ℝ 3 0).minimal (mesh 3 N).domain).domain) = ⟨_, h⟩ :=
      Subtype.ext (hu a).symm
    change (extDerivOp ℝ 3 0).minimal (mesh 3 N).domain ⟨ψ a, hd a⟩ = _
    rw [e]
    exact hval
  rw [hd', hψe]
  exact hC N u'

/-- `Prop 5.9(1)` transported to a domain `Θ = (mesh 3 N).domain`. -/
theorem exists_sub_wsL2_le_of_eq {C : ℝ} (N : ℕ)
    (hC : ∀ (ψ : PiLp 2 (fun _ : Fin 3 => L2F ℝ (mesh 3 N).domain (formIdx 3 0)))
      (_ : ∀ a, ψ a ∈ (polyElement 3 lagrangeP2).V₀ (mesh 3 N) 0)
      (hd : ∀ a, ψ a ∈ ((extDerivOp ℝ 3 0).minimal (mesh 3 N).domain).domain),
      ∃ w ∈ (polyElement 3 lowestOrder).V₀ (mesh 3 N) 1,
        ‖wsZero ψ - w‖ ≤ C * hN N *
          ‖(WithLp.toLp 2 fun a => (extDerivOp ℝ 3 0).minimal (mesh 3 N).domain ⟨ψ a, hd a⟩ :
            PiLp 2 (fun _ : Fin 3 => L2F ℝ (mesh 3 N).domain (formIdx 3 1)))‖)
    {Θ : Set (Fin 3 → ℝ)} (e : (mesh 3 N).domain = Θ) (hΘ : IsOpen Θ)
    (ψ : PiLp 2 (fun _ : Fin 3 => L2F ℝ Θ (formIdx 3 0)))
    (hψ : ∀ a, ψ a ∈ ((deRham ℝ 3).minimalSubcomplexOfEq e (isOpen_mesh_domain 3 N) hΘ
      (lagrangeP2.subcomplexMin (mesh 3 N) (isOpen_mesh_domain 3 N) (center 3)
        (strictStar_mesh 3 N))).V 0)
    (hd : ∀ a, ψ a ∈ ((extDerivOp ℝ 3 0).minimal Θ).domain) :
    ∃ w ∈ ((deRham ℝ 3).minimalSubcomplexOfEq e (isOpen_mesh_domain 3 N) hΘ
      (lowestOrder.subcomplexMin (mesh 3 N) (isOpen_mesh_domain 3 N) (center 3)
        (strictStar_mesh 3 N))).V 1,
      ‖wsZero ψ - @id (L2F ℝ Θ (formIdx 3 1)) w‖ ≤ C * hN N *
        ‖(WithLp.toLp 2 fun a => (extDerivOp ℝ 3 0).minimal Θ ⟨ψ a, hd a⟩ :
          PiLp 2 (fun _ : Fin 3 => L2F ℝ Θ (formIdx 3 1)))‖ := by
  subst e
  exact hC ψ hψ hd

end Prop59One

/-! ### Fields with `H̊¹(Q)` coefficients -/

section H1Coeff

/-- `f ↦ f` as a `0`-form (the linear `coeffForm`). -/
def coeffFormₗ : L2 ℝ (cubeDomain 3) →ₗ[ℝ] W0 where
  toFun f := coeffForm f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The coefficients in `H̊¹(Q)`: `f` with `f` (as a `0`-form) in `D(grad_min)`. -/
def H1c : Submodule ℝ (L2 ℝ (cubeDomain 3)) := D0.domain.comap coeffFormₗ

/-- The gradient of an `H̊¹(Q)` coefficient. -/
def gradc : H1c →ₗ[ℝ] W1 :=
  D0.toFun ∘ₗ coeffFormₗ.restrict (p := H1c) (q := D0.domain) fun _ hx => hx

theorem gradc_apply (f : H1c) : gradc f = D0 ⟨coeffForm (f : L2 ℝ (cubeDomain 3)), f.2⟩ := rfl

theorem norm_le_sum_wv {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (x : Wv V) :
    ‖x‖ ≤ ∑ a, ‖x a‖ := by
  have h : ‖x‖ ^ 2 ≤ (∑ a, ‖x a‖) ^ 2 := by
    rw [norm_sq_wv]
    exact Finset.sum_sq_le_sq_sum_of_nonneg fun a _ => norm_nonneg _
  exact le_of_pow_le_pow_left₀ two_ne_zero (Finset.sum_nonneg fun _ _ => norm_nonneg _) h

/-- Finite combinations of `H̊¹` coefficients with coefficients of size `≤ 1`. -/
theorem H1c_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (hc : ∀ i, |c i| ≤ 1)
    (f : ι → L2 ℝ (cubeDomain 3)) (hf : ∀ i, f i ∈ H1c) {B : ℝ}
    (hB : ∀ i, ‖gradc ⟨f i, hf i⟩‖ ≤ B) :
    ∃ h : ∑ i ∈ s, c i • f i ∈ H1c, ‖gradc ⟨_, h⟩‖ ≤ s.card * B := by
  have hmem : ∑ i ∈ s, c i • f i ∈ H1c :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hf i)
  refine ⟨hmem, ?_⟩
  have e : (⟨_, hmem⟩ : H1c) = ∑ i ∈ s, c i • (⟨f i, hf i⟩ : H1c) := by
    refine Subtype.ext ?_
    simp
  rw [e, map_sum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ s, ‖gradc (c i • (⟨f i, hf i⟩ : H1c))‖ ≤ ∑ _i ∈ s, B := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [map_smul, norm_smul, Real.norm_eq_abs]
        have h0 : 0 ≤ ‖gradc ⟨f i, hf i⟩‖ := norm_nonneg _
        calc |c i| * ‖gradc ⟨f i, hf i⟩‖ ≤ 1 * ‖gradc ⟨f i, hf i⟩‖ :=
              mul_le_mul_of_nonneg_right (hc i) h0
          _ ≤ B := by rw [one_mul]; exact hB i
    _ = s.card * B := by rw [Finset.sum_const, nsmul_eq_mul]

theorem coeffForm_apply_empty (z : W0) (h : ((∅ : Finset (Fin 3)).card : ℤ) = 0) :
    coeffForm (z ⟨∅, h⟩) = z := by
  refine PiLp.ext fun s => ?_
  have : s = ⟨∅, h⟩ := Subtype.ext (Finset.card_eq_zero.1 (by exact_mod_cast s.2))
  rw [this]
  rfl

/-- **The components of `S⁰ψ`, `ψ ∈ H̊Λ⁰(Q)³`, are `H̊¹(Q)` coefficients** with gradient bounded by
the graph norm of `ψ` (`(S⁰ψ)_{{j}} = ψⱼ`). -/
theorem wsZero_apply_mem_H1c (ψ : Vt0) (s : formIdx 3 1) :
    ∃ h : wsZero (ιt0 ψ) s ∈ H1c, ‖gradc ⟨_, h⟩‖ ≤ ‖ψ‖ := by
  obtain ⟨t, ht⟩ := s
  obtain ⟨j, rfl⟩ : ∃ j, t = {j} := Finset.card_eq_one.1 (by exact_mod_cast ht)
  have e : wsZero (ιt0 ψ) ⟨{j}, ht⟩ = (ιt0 ψ) j ⟨∅, by simp⟩ := wsL2_zero_apply (ιt0 ψ) j
  have hc : coeffForm ((ιt0 ψ) j ⟨∅, by simp⟩) = D0.graphFst (ψ j) :=
    coeffForm_apply_empty _ _
  have hmem : wsZero (ιt0 ψ) ⟨{j}, ht⟩ ∈ H1c := by
    change coeffForm (wsZero (ιt0 ψ) ⟨{j}, ht⟩) ∈ D0.domain
    rw [e, hc]
    exact graphFst_mem_domain D0 (ψ j)
  refine ⟨hmem, ?_⟩
  have hg : gradc ⟨_, hmem⟩ = D0.graphSnd (ψ j) := by
    rw [gradc_apply, ← apply_graphDom]
    congr 1
    exact Subtype.ext (by
      change coeffForm (wsZero (ιt0 ψ) ⟨{j}, ht⟩) = D0.graphFst (ψ j)
      rw [e, hc])
  rw [hg]
  have h1 : ‖D0.graphSnd (ψ j)‖ ≤ ‖ψ j‖ := by
    have := norm_sq_graphSpace D0 (ψ j)
    refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
    nlinarith [sq_nonneg ‖D0.graphFst (ψ j)‖]
  exact h1.trans (PiLp.norm_apply_le ψ j)

/-- `H̊Λ⁰(Q)` with the graph norm, mapped to the domain. -/
def graphDomₗ : V0 →ₗ[ℝ] U0 where
  toFun := graphDom D0
  map_add' := graphDom_add D0
  map_smul' := graphDom_smul D0

/-- `H̊Λ⁰(Q)³` with the graph norm, mapped to the domains. -/
def rp : Vt0 →ₗ[ℝ] Wv U0 := piMap graphDomₗ

theorem incl0_rp (ψ : Vt0) : incl0 (rp ψ) = ιt0 ψ := PiLp.ext fun _ => rfl

/-- **The regular potentials** `y = (yₐ)ₐ ∈ (H̊Λ⁰(Q)³)³ ↦ (S⁰ yₐ)ₐ ∈ H̊Λ¹(Q)³`: the matrix fields with
rows in `H̊¹(Q; ℝ³)`. -/
def regR : Wv Vt0 →ₗ[ℝ] Wv U1 := piMap (segS0 ∘ₗ rp)

theorem coe_regR (y : Wv Vt0) (a : Fin 3) : ((regR y a : U1) : W1) = wsZero (ιt0 (y a)) := by
  change wsL2 (Ω := cubeDomain 3) 0 (incl0 (rp (y a))) = _
  rw [incl0_rp]

theorem norm_regR_le (y : Wv Vt0) : ‖regR y‖ ≤ 1 * ‖y‖ := by
  refine norm_piMap_le _ zero_le_one (fun ψ => ?_) y
  have h2 : ‖rp ψ‖ ≤ ‖ψ‖ := by
    refine (norm_piMap_le graphDomₗ zero_le_one (fun v => ?_) ψ).trans_eq (one_mul _)
    rw [one_mul]
    change ‖D0.graphFst v‖ ≤ ‖v‖
    have := norm_sq_graphSpace D0 v
    refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
    nlinarith [sq_nonneg ‖D0.graphSnd v‖]
  rw [one_mul]
  change ‖segS0 (rp ψ)‖ ≤ ‖ψ‖
  have h3 : ‖segS0 (rp ψ)‖ ≤ ‖rp ψ‖ := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
    rw [norm_segS0]
    exact norm_wsL2_zero_incl0_sq_le (rp ψ)
  exact h3.trans h2

/-- The components of `S¹ (S⁰ yₐ)ₐ` are `H̊¹(Q)` coefficients. -/
theorem segS1_regR_mem_H1c (y : Wv Vt0) (t : formIdx 3 2) :
    ∃ h : segS1 (regR y) t ∈ H1c,
      ‖gradc ⟨_, h⟩‖ ≤ (Fintype.card (Fin 3 × formIdx 3 1) : ℝ) * ‖y‖ := by
  have e : segS1 (regR y) t = ∑ q : Fin 3 × formIdx 3 1, wsCoeff 1 t q •
      wsZero (ιt0 (y q.1)) q.2 := by
    change wsL2 (Ω := cubeDomain 3) 1 (incl1 (regR y)) t = _
    rw [wsL2_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
  have hc : ∀ q : Fin 3 × formIdx 3 1, |wsCoeff 1 t q| ≤ 1 := fun q => by
    rw [abs_wsCoeff]; split_ifs <;> norm_num
  have hf : ∀ q : Fin 3 × formIdx 3 1, wsZero (ιt0 (y q.1)) q.2 ∈ H1c :=
    fun q => (wsZero_apply_mem_H1c (y q.1) q.2).1
  obtain ⟨h, hle⟩ := H1c_sum Finset.univ (fun q => wsCoeff 1 t q) hc
    (fun q => wsZero (ιt0 (y q.1)) q.2) hf (B := ‖y‖)
    (fun q => (wsZero_apply_mem_H1c (y q.1) q.2).2.trans (PiLp.norm_apply_le y q.1))
  rw [← e] at h
  refine ⟨h, ?_⟩
  rw [Finset.card_univ] at hle
  convert hle using 3
  exact Subtype.ext e

end H1Coeff

/-! ### Projection errors of smooth fields -/

section ProjError

variable {S' : (complexMin 3).Subcomplex}

/-- Interpolation of a `C²` scalar field vanishing outside `Q` (degree `0`), in the graph norm. -/
theorem exists_approx_zero {S : PolySeq} {L : ℝ} (hL0 : 0 ≤ L) (N : ℕ) (σ : U0)
    (hσ : IsCsFormMin 0 0 L (σ : W0)) :
    ∃ v, ∃ hv : v ∈ (polyMin 3 S N).V 0,
      ‖(σ : W0) - v‖ ≤ polyInterpBound 3 S 0 * L * meshSize N ∧
      ‖D0 ⟨(σ : W0) - v, D0.domain.sub_mem σ.2 (mem_D0_of_mem_V hv)⟩‖ ≤
        polyInterpBound 3 S 0 * L * meshSize N := by
  obtain ⟨v, hv, h1, h2⟩ := hσ.exists_mem_polyMin_le ((polyOrder_zero S).polyOrderAt 0) hL0 N
  refine ⟨v, hv, by simpa using h1, ?_⟩
  have h := h2 1 (mem_dom01 σ.2)
  rw [d01_apply] at h
  simpa using h

/-- Interpolation of a `C²` `1`-form vanishing outside `Q`, in the graph norm. -/
theorem exists_approx_one {S : PolySeq} {L : ℝ} (hL0 : 0 ≤ L) (N : ℕ) (u : U1)
    (hu : IsCsFormMin 0 1 L (u : W1)) :
    ∃ v, ∃ hv : v ∈ (polyMin 3 S N).V 1,
      ‖(u : W1) - v‖ ≤ polyInterpBound 3 S 1 * L * meshSize N ∧
      ‖D1 ⟨(u : W1) - v, D1.domain.sub_mem u.2 (mem_D1_of_mem_V hv)⟩‖ ≤
        polyInterpBound 3 S 1 * L * meshSize N := by
  obtain ⟨v, hv, h1, h2⟩ := hu.exists_mem_polyMin_le ((polyOrder_zero S).polyOrderAt 1) hL0 N
  refine ⟨v, hv, by simpa using h1, ?_⟩
  have h := h2 2 (mem_dom12 u.2)
  rw [d12_apply] at h
  simpa using h

/-- Graph-norm error of a cochain projection in degree `0` from an approximation. -/
theorem graphSq_projU0_sub_le (P : S'.CochainProjection) {C : ℝ}
    (hP1 : ∀ x, ‖P.π 1 x‖ ≤ 2 * C * ‖x‖) (hP0 : ∀ x, ‖P.π 0 x‖ ≤ 2 * C * ‖x‖) (σ : U0)
    {v : W0} (hv : v ∈ S'.V 0) {B : ℝ} (h1 : ‖(σ : W0) - v‖ ≤ B)
    (h2 : ‖D0 ⟨(σ : W0) - v, D0.domain.sub_mem σ.2 (mem_D0_of_mem_V hv)⟩‖ ≤ B)
    (hC : 0 ≤ 1 + 2 * C) :
    Feec.BGG.graphSq segD0 (projU0 P σ - σ) ≤ 2 * ((1 + 2 * C) * B) ^ 2 := by
  have hB : 0 ≤ B := (norm_nonneg _).trans h1
  have e1 : ‖projU0 P σ - σ‖ = ‖(σ : W0) - P.π 0 σ‖ := by
    rw [norm_sub_rev]; rfl
  have a1 : ‖projU0 P σ - σ‖ ≤ (1 + 2 * C) * B := by
    rw [e1]
    exact (norm_sub_π_le_of_mem P hP0 hv).trans (mul_le_mul_of_nonneg_left h1 hC)
  have hdv : D0 ⟨v, mem_D0_of_mem_V hv⟩ ∈ S'.V 1 := D0_mem_V ⟨v, mem_D0_of_mem_V hv⟩ hv
  have e2 : ‖segD0 (projU0 P σ - σ)‖ = ‖D0 σ - P.π 1 (D0 σ)‖ := by
    rw [map_sub, norm_sub_rev]
    change ‖D0 σ - D0 ⟨P.π 0 σ, mem_D0_of_mem_V (P.mem 0 σ)⟩‖ = _
    rw [D0_π]
  have e3 : D0 σ - D0 ⟨v, mem_D0_of_mem_V hv⟩ =
      D0 ⟨(σ : W0) - v, D0.domain.sub_mem σ.2 (mem_D0_of_mem_V hv)⟩ := by
    rw [← LinearPMap.map_sub]; rfl
  have a2 : ‖segD0 (projU0 P σ - σ)‖ ≤ (1 + 2 * C) * B := by
    rw [e2]
    refine (norm_sub_π_le_of_mem P hP1 hdv).trans (mul_le_mul_of_nonneg_left ?_ hC)
    rw [e3]; exact h2
  unfold Feec.BGG.graphSq
  have := pow_le_pow_left₀ (norm_nonneg _) a1 2
  have := pow_le_pow_left₀ (norm_nonneg _) a2 2
  linarith

/-- Graph-norm error of a cochain projection in degree `1` from an approximation. -/
theorem graphSq_projU1_sub_le (P : S'.CochainProjection) {C : ℝ}
    (hP2 : ∀ x, ‖P.π 2 x‖ ≤ 2 * C * ‖x‖) (hP1 : ∀ x, ‖P.π 1 x‖ ≤ 2 * C * ‖x‖) (u : U1)
    {v : W1} (hv : v ∈ S'.V 1) {B : ℝ} (h1 : ‖(u : W1) - v‖ ≤ B)
    (h2 : ‖D1 ⟨(u : W1) - v, D1.domain.sub_mem u.2 (mem_D1_of_mem_V hv)⟩‖ ≤ B)
    (hC : 0 ≤ 1 + 2 * C) :
    Feec.BGG.graphSq segD1 (projU1 P u - u) ≤ 2 * ((1 + 2 * C) * B) ^ 2 := by
  have e1 : ‖projU1 P u - u‖ = ‖(u : W1) - P.π 1 u‖ := by
    rw [norm_sub_rev]; rfl
  have a1 : ‖projU1 P u - u‖ ≤ (1 + 2 * C) * B := by
    rw [e1]
    exact (norm_sub_π_le_of_mem P hP1 hv).trans (mul_le_mul_of_nonneg_left h1 hC)
  have hdv : D1 ⟨v, mem_D1_of_mem_V hv⟩ ∈ S'.V 2 := D1_mem_V ⟨v, mem_D1_of_mem_V hv⟩ hv
  have e2 : ‖segD1 (projU1 P u - u)‖ = ‖D1 u - P.π 2 (D1 u)‖ := by
    rw [map_sub, norm_sub_rev]
    change ‖D1 u - D1 ⟨P.π 1 u, mem_D1_of_mem_V (P.mem 1 u)⟩‖ = _
    rw [D1_π]
  have e3 : D1 u - D1 ⟨v, mem_D1_of_mem_V hv⟩ =
      D1 ⟨(u : W1) - v, D1.domain.sub_mem u.2 (mem_D1_of_mem_V hv)⟩ := by
    rw [← LinearPMap.map_sub]; rfl
  have a2 : ‖segD1 (projU1 P u - u)‖ ≤ (1 + 2 * C) * B := by
    rw [e2]
    refine (norm_sub_π_le_of_mem P hP2 hdv).trans (mul_le_mul_of_nonneg_left ?_ hC)
    rw [e3]; exact h2
  unfold Feec.BGG.graphSq
  have := pow_le_pow_left₀ (norm_nonneg _) a1 2
  have := pow_le_pow_left₀ (norm_nonneg _) a2 2
  linarith

end ProjError

/-! ### The smoothed projections of Table 5.1 -/

section Table51

variable {p : ℕ → SmoothingParam (Fin 3 → ℝ)} {C : ℝ}
  (hT : PolySmoothingEstimatesMin 3 PolySeq.lowestOrder p C)
  (hB : PolySmoothingEstimatesMin 3 PolySeq.lagrangeP2 p C)

/-- **The smoothed projections of the two rows satisfy (5.4)**: `π¹ S⁰ π̃⁰ = π¹ S⁰` (common
smoother `p`; `π̃⁰` componentwise). -/
theorem proj_wsL2_piMap_proj (N : ℕ) (x : PiLp 2 (fun _ : Fin 3 => W0)) :
    (hT.proj N).π 1 (wsL2 (Ω := cubeDomain 3) 0 (piMap ((hB.proj N).π 0) x)) =
      (hT.proj N).π 1 (wsL2 (Ω := cubeDomain 3) 0 x) := by
  change ((polySmoothedMin 3 PolySeq.lowestOrder N (p N) (hT.isMinimal N)).toCochainProjection
      (θ := 1 / 2) (by norm_num) (hT.close N)).π 1 _ =
    ((polySmoothedMin 3 PolySeq.lowestOrder N (p N) (hT.isMinimal N)).toCochainProjection
      (θ := 1 / 2) (by norm_num) (hT.close N)).π 1 _
  rw [Subcomplex.CommutingMap.toCochainProjection_π,
    Subcomplex.CommutingMap.toCochainProjection_π]
  congr 3
  refine commutingMapOfEqMin_wsL2_zero_eq (mesh 3 N) (p N) _ _ _ (hT.isMinimal N) _ _
    (mesh_domain 3 N) (isOpen_cubeDomain 3) fun a => ?_
  have h := (polySmoothedMin 3 PolySeq.lagrangeP2 N (p N) (hB.isMinimal N)).Q_restrictVEquiv_symm
    (θ := 1 / 2) (by norm_num) (hB.close N) 0
    ⟨(polySmoothedMin 3 PolySeq.lagrangeP2 N (p N) (hB.isMinimal N)).Q 0 (x a),
      (polySmoothedMin 3 PolySeq.lagrangeP2 N (p N) (hB.isMinimal N)).mem 0 (x a)⟩
  exact h

/-- **The discretization of Table 5.1** on the level-`(N + 1)` mesh: top row `P₁Λ̊⁰ → P₁⁻Λ̊¹ →
P₁⁻Λ̊²`, bottom row `P₂Λ̊⁰ ⊗ ℝ³ → P₂⁻Λ̊¹ ⊗ ℝ³ → P₁Λ̊² ⊗ ℝ³` (vanishing boundary DOFs), with the
smoothed projections `π = J⁻¹ Π_h R` of one common smoother. -/
def table51 (N : ℕ) : Feec.BGG.Discrete bggSegment :=
  bggDiscrete (polyMin 3 PolySeq.lowestOrder N) (polyMin 3 PolySeq.lagrangeP2 N) (hT.proj N)
    (hB.proj N)

/-- **(5.4) holds for the discretization of Table 5.1** (`Feec.BGG.Discrete.Compatible`). -/
theorem table51_compatible (N : ℕ) : (table51 hT hB N).Compatible := fun ψ => by
  refine Subtype.ext ?_
  change (hT.proj N).π 1 (wsL2 (Ω := cubeDomain 3) 0 (incl0 (piMap (projU0 (hB.proj N)) ψ))) =
    (hT.proj N).π 1 (wsL2 (Ω := cubeDomain 3) 0 (incl0 ψ))
  have e : incl0 (piMap (projU0 (hB.proj N)) ψ) = piMap ((hB.proj N).π 0) (incl0 ψ) :=
    PiLp.ext fun a => rfl
  rw [e, proj_wsL2_piMap_proj]

/-- **Uniform bounds of the projections of Table 5.1**: `Discrete.Bounded (2C)` for every `N`. -/
theorem table51_bounded (N : ℕ) : (table51 hT hB N).Bounded (2 * C) :=
  bggDiscrete_bounded hT.two_mul_nonneg (hT.norm_proj_le N 2) (hT.isGraphBounded_proj N 1 2)
    (hB.isGraphBounded_proj N 1 2)

/-- **Consistency of `S₀,ₕ = π¹S⁰`** ([QuennevilleBelair2015], Prop 5.9(1), transferred to the
smoothed projection): `‖(I − π¹)S⁰ψ‖ ≤ C_app h ‖ψ‖_V` on `Ṽₕ⁰ = P₂Λ̊⁰ ⊗ ℝ³`, since
`(I − π¹)S⁰ψ = (I − π¹)(S⁰ψ − Π¹S⁰ψ)` (`π¹` fixes `Π¹S⁰ψ ∈ P₁⁻Λ̊¹`), so it is at most
`(1 + 2C) ‖(I − Π¹)S⁰ψ‖ ≤ (1 + 2C) C h ‖∇ψ‖`. The hypothesis `happ0` of
`Feec.BGG.Discrete.error_estimate`. -/
theorem table51_happ0 : ∃ Capp, 0 ≤ Capp ∧ ∀ N, ∀ ψ ∈ (table51 hT hB N).Vt0h,
    ‖bggSegment.S0 ψ - (table51 hT hB N).S0h ψ‖ ^ 2 ≤
      (Capp * meshSize N) ^ 2 * Feec.BGG.graphSq bggSegment.dt0 ψ := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_sub_wsL2_le_mesh
  have hC := hT.two_mul_nonneg
  refine ⟨(1 + 2 * C) * C₁, by positivity, fun N ψ hψ => ?_⟩
  obtain ⟨w, hw, hwle⟩ := exists_sub_wsL2_le_of_eq N (hC₁ N) (mesh_domain 3 N)
    (isOpen_cubeDomain 3) (incl0 ψ) (fun a => hψ a) (fun a => (ψ a).2)
  have hd : ‖(WithLp.toLp 2 fun a => (extDerivOp ℝ 3 0).minimal (cubeDomain 3)
      ⟨incl0 ψ a, (ψ a).2⟩ : PiLp 2 (fun _ : Fin 3 => L2F ℝ (cubeDomain 3) (formIdx 3 1)))‖ =
      ‖bggSegment.dt0 ψ‖ := norm_incl1 (piMap segD0 ψ)
  have h1 : ‖bggSegment.S0 ψ - (table51 hT hB N).S0h ψ‖ ≤
      (1 + 2 * C) * (C₁ * meshSize N * ‖bggSegment.dt0 ψ‖) := by
    change ‖wsZero (incl0 ψ) - (hT.proj N).π 1 (wsZero (incl0 ψ))‖ ≤ _
    refine (norm_sub_π_le_of_mem (hT.proj N) (hT.norm_proj_le N 1) hw).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    rw [← hd, ← hN_eq_meshSize]
    exact hwle
  have h2 : ‖bggSegment.dt0 ψ‖ ^ 2 ≤ Feec.BGG.graphSq bggSegment.dt0 ψ := by
    unfold Feec.BGG.graphSq; nlinarith [sq_nonneg ‖ψ‖]
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hm := (meshSize_pos N).le
  calc _ ≤ ((1 + 2 * C) * (C₁ * meshSize N * ‖bggSegment.dt0 ψ‖)) ^ 2 := h3
    _ = ((1 + 2 * C) * C₁ * meshSize N) ^ 2 * ‖bggSegment.dt0 ψ‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)

variable (C) in
/-- The approximation constant of the regular potentials. -/
def regConst : ℝ :=
  3 * ((1 + 2 * C) * h1Const 3 PolySeq.lagrangeP2 1 1 * (Fintype.card (formIdx 3 1) : ℝ)) +
    (1 + 2 * C) * h1Const 3 PolySeq.lowestOrder 2 1 * (Fintype.card (formIdx 3 2) : ℝ) *
      (Fintype.card (Fin 3 × formIdx 3 1) : ℝ)

include hT in
theorem regConst_nonneg : 0 ≤ regConst C := by
  have := hT.two_mul_nonneg
  have h1 := h1Const_nonneg (n := 3) PolySeq.lagrangeP2 1 zero_le_one
  have h2 := h1Const_nonneg (n := 3) PolySeq.lowestOrder 2 zero_le_one
  unfold regConst; positivity

theorem sum_norm_d01_le {x : W1} (hy : ∀ s, coeffForm (x s) ∈ ((complexMin 3).d 0 1).domain)
    {B : ℝ} (hB : ∀ s, ∀ h : x s ∈ H1c, ‖gradc ⟨_, h⟩‖ ≤ B) :
    ∑ s, ‖(complexMin 3).d 0 1 ⟨coeffForm (x s), hy s⟩‖ ≤
      (Fintype.card (formIdx 3 1) : ℝ) * B := by
  calc ∑ s, ‖(complexMin 3).d 0 1 ⟨coeffForm (x s), hy s⟩‖ ≤ ∑ _s : formIdx 3 1, B := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [d01_apply]
        exact hB s (mem_D0_domain (hy s))
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

theorem sum_norm_d01_le_two {x : W2} (hy : ∀ s, coeffForm (x s) ∈ ((complexMin 3).d 0 1).domain)
    {B : ℝ} (hB : ∀ s, ∀ h : x s ∈ H1c, ‖gradc ⟨_, h⟩‖ ≤ B) :
    ∑ s, ‖(complexMin 3).d 0 1 ⟨coeffForm (x s), hy s⟩‖ ≤
      (Fintype.card (formIdx 3 2) : ℝ) * B := by
  calc ∑ s, ‖(complexMin 3).d 0 1 ⟨coeffForm (x s), hy s⟩‖ ≤ ∑ _s : formIdx 3 2, B := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [d01_apply]
        exact hB s (mem_D0_domain (hy s))
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- **Regular potentials for the discretization of Table 5.1**, from the regularity hypothesis
`curl H̊(curl) = curl S⁰ H̊¹(Q; ℝ³)` (with its constant `C_R`) and the `H̊¹` approximation of the
smoothed projections (`PolySmoothingEstimatesMin.norm_sub_proj_le_grad`): `X_reg = (H̊Λ⁰(Q)³)³`
(rows in `H̊¹`, graph norm), `R y = (S⁰ yₐ)ₐ`. -/
def table51Reg (N : ℕ) {CR : ℝ} (hCR0 : 0 ≤ CR)
    (hCR : ∀ u : V1, ∃ φ : Vt0, bggD1 (bggS0 φ) = bggD1 u ∧ ‖φ‖ ≤ CR * ‖bggD1 u‖)
    {Capp : ℝ} (hCapp : regConst C ≤ Capp) :
    (table51 hT hB N).RegularPotential (Wv Vt0) 1 CR Capp (meshSize N) where
  R := regR
  Cinc_nonneg := zero_le_one
  Creg_nonneg := hCR0
  norm_R_le := norm_regR_le
  exists_potential v _ := by
    choose φ hφ using fun a => hCR (D1.toGraphSpace (v a))
    refine ⟨WithLp.toLp 2 φ, PiLp.ext fun a => (hφ a).1, ?_⟩
    have h2 : ‖(WithLp.toLp 2 φ : Wv Vt0)‖ ^ 2 ≤ (CR * ‖bggSegment.dt1 v‖) ^ 2 := by
      rw [norm_sq_wv, mul_pow, norm_sq_wv, Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hφ a).2 2
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) h2
  approx_Pt1 y := by
    have hC := hT.two_mul_nonneg
    have hc1 : (0 : ℝ) ≤ Fintype.card (formIdx 3 1) := Nat.cast_nonneg _
    have hh1 := h1Const_nonneg (n := 3) PolySeq.lagrangeP2 1 zero_le_one
    have hm := (meshSize_pos N).le
    have hkey : ∀ a, ‖(regR y - (table51 hT hB N).Pt1 (regR y)) a‖ ≤
        (1 + 2 * C) * h1Const 3 PolySeq.lagrangeP2 1 1 * meshSize N *
          ((Fintype.card (formIdx 3 1) : ℝ) * ‖y‖) := by
      intro a
      have hy : ∀ s, coeffForm (((regR y a : U1) : W1) s) ∈ ((complexMin 3).d 0 1).domain := by
        intro s
        rw [coe_regR]
        exact mem_dom01 (wsZero_apply_mem_H1c (y a) s).1
      have h := hB.norm_sub_proj_le_grad N 1 ((regR y a : U1) : W1) hy
      refine (le_of_eq_of_le ?_ h).trans (mul_le_mul_of_nonneg_left
        (sum_norm_d01_le hy fun s hs => ?_) (by positivity))
      · rfl
      · have h' := (wsZero_apply_mem_H1c (y a) s).2
        refine le_trans (le_of_eq ?_) (h'.trans (PiLp.norm_apply_le y a))
        congr 2
    refine (norm_le_sum_wv _).trans ?_
    calc ∑ a, ‖(regR y - (table51 hT hB N).Pt1 (regR y)) a‖ ≤
          ∑ _a : Fin 3, (1 + 2 * C) * h1Const 3 PolySeq.lagrangeP2 1 1 * meshSize N *
            ((Fintype.card (formIdx 3 1) : ℝ) * ‖y‖) := Finset.sum_le_sum fun a _ => hkey a
      _ = 3 * ((1 + 2 * C) * h1Const 3 PolySeq.lagrangeP2 1 1 *
            (Fintype.card (formIdx 3 1) : ℝ)) * meshSize N * ‖y‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
      _ ≤ Capp * meshSize N * ‖y‖ := by
          have h2 := h1Const_nonneg (n := 3) PolySeq.lowestOrder 2 zero_le_one
          have hle : 3 * ((1 + 2 * C) * h1Const 3 PolySeq.lagrangeP2 1 1 *
              (Fintype.card (formIdx 3 1) : ℝ)) ≤ Capp := by
            refine le_trans ?_ hCapp
            unfold regConst
            have : 0 ≤ (1 + 2 * C) * h1Const 3 PolySeq.lowestOrder 2 1 *
                (Fintype.card (formIdx 3 2) : ℝ) * (Fintype.card (Fin 3 × formIdx 3 1) : ℝ) := by
              positivity
            linarith
          gcongr
  approx_S1 y := by
    have hC := hT.two_mul_nonneg
    have hh2 := h1Const_nonneg (n := 3) PolySeq.lowestOrder 2 zero_le_one
    have hm := (meshSize_pos N).le
    have hy : ∀ s, coeffForm (segS1 (regR y) s) ∈ ((complexMin 3).d 0 1).domain :=
      fun s => mem_dom01 (segS1_regR_mem_H1c y s).1
    have h := hT.norm_sub_proj_le_grad N 2 (segS1 (regR y)) hy
    change ‖segS1 (regR y) - (hT.proj N).π 2 (segS1 (regR y))‖ ≤ _
    refine h.trans ?_
    have hs := sum_norm_d01_le_two hy fun s hs => (segS1_regR_mem_H1c y s).2
    calc (1 + 2 * C) * h1Const 3 PolySeq.lowestOrder 2 1 * meshSize N *
          ∑ s, ‖(complexMin 3).d 0 1 ⟨coeffForm (segS1 (regR y) s), hy s⟩‖ ≤
        (1 + 2 * C) * h1Const 3 PolySeq.lowestOrder 2 1 * meshSize N *
          ((Fintype.card (formIdx 3 2) : ℝ) *
            ((Fintype.card (Fin 3 × formIdx 3 1) : ℝ) * ‖y‖)) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = (1 + 2 * C) * h1Const 3 PolySeq.lowestOrder 2 1 * (Fintype.card (formIdx 3 2) : ℝ) *
            (Fintype.card (Fin 3 × formIdx 3 1) : ℝ) * meshSize N * ‖y‖ := by ring
      _ ≤ Capp * meshSize N * ‖y‖ := by
          have h1 := h1Const_nonneg (n := 3) PolySeq.lagrangeP2 1 zero_le_one
          have hle : (1 + 2 * C) * h1Const 3 PolySeq.lowestOrder 2 1 *
              (Fintype.card (formIdx 3 2) : ℝ) * (Fintype.card (Fin 3 × formIdx 3 1) : ℝ) ≤
                Capp := by
            refine le_trans ?_ hCapp
            unfold regConst
            have : 0 ≤ 3 * ((1 + 2 * C) * h1Const 3 PolySeq.lagrangeP2 1 1 *
                (Fintype.card (formIdx 3 1) : ℝ)) := by positivity
            linarith
          gcongr

/-- **The continuous constants of Prop 5.3 on the cube** for a regularity constant `C_R`
(the form of `bggStability` with `C_R` given). -/
theorem bggStability_of {CR : ℝ} (hCR0 : 0 ≤ CR)
    (hCR : ∀ u : V1, ∃ φ : Vt0, bggD1 (bggS0 φ) = bggD1 u ∧ ‖φ‖ ≤ CR * ‖bggD1 u‖) :
    Feec.BGG.Stability bggSegment (2 * Real.pi)⁻¹ CR (Real.sqrt 2) :=
  ⟨by positivity, hCR0, Real.sqrt_nonneg _, poincare0, seg_poinct0,
    fun μ hμ => by obtain ⟨x, hx⟩ := exists_D0_eq hμ; exact ⟨x, Subtype.ext hx⟩,
    seg_hodget1, seg_reg hCR, seg_boundS0, seg_boundS1⟩

theorem table51_fd0 (N : ℕ) : FiniteDimensional ℝ (table51 hT hB N).V0h :=
  finiteDimensional_comap ((polyMin 3 PolySeq.lowestOrder N).V 0) D0.domain

theorem table51_fd1 (N : ℕ) : FiniteDimensional ℝ (table51 hT hB N).V1h :=
  finiteDimensional_comap ((polyMin 3 PolySeq.lowestOrder N).V 1) D1.domain

theorem table51_fdt0 (N : ℕ) : FiniteDimensional ℝ (table51 hT hB N).Vt0h :=
  haveI := finiteDimensional_comap ((polyMin 3 PolySeq.lagrangeP2 N).V 0) D0.domain
  finiteDimensional_tsub _

theorem table51_fdt1 (N : ℕ) : FiniteDimensional ℝ (table51 hT hB N).Vt1h :=
  haveI := finiteDimensional_comap ((polyMin 3 PolySeq.lagrangeP2 N).V 1) D1.domain
  finiteDimensional_tsub _

/-- `‖S₁,ₕ w‖² ≤ 8 C² ‖w‖²` for the discretization of Table 5.1. -/
theorem norm_table51_S1h_sq_le (N : ℕ) (w : Wv U1) :
    ‖(table51 hT hB N).S1h w‖ ^ 2 ≤ 8 * C ^ 2 * ‖w‖ ^ 2 := by
  have h1 : ‖(table51 hT hB N).S1h w‖ ≤ 2 * C * ‖segS1 w‖ := hT.norm_proj_le N 2 (segS1 w)
  have h2 : ‖segS1 w‖ ^ 2 ≤ 2 * ‖w‖ ^ 2 := norm_wsL2_one_incl1_sq_le w
  have hC := hT.two_mul_nonneg
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg (2 * C))]

/-- `gnSq ≤ (1 + 8C²) graphSq` for the discretization of Table 5.1. -/
theorem table51_gnSq_le (N : ℕ) (w : Wv U1) :
    (table51 hT hB N).gnSq w ≤ (1 + 8 * C ^ 2) * Feec.BGG.graphSq bggSegment.dt1 w := by
  have h := norm_table51_S1h_sq_le hT hB N w
  unfold Feec.BGG.Discrete.gnSq Feec.BGG.graphSq
  nlinarith [sq_nonneg ‖bggSegment.dt1 w‖, sq_nonneg C, sq_nonneg ‖w‖]

theorem table51_err_P0 (N : ℕ) {L : ℝ} (hL0 : 0 ≤ L) (σ : U0) (hσ : IsCsFormMin 0 0 L (σ : W0)) :
    Feec.BGG.graphSq bggSegment.d0 ((table51 hT hB N).P0 σ - σ) ≤
      2 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lowestOrder 0) ^ 2 * (L * meshSize N) ^ 2 := by
  have hA : 0 ≤ 1 + 2 * C := by linarith [hT.two_mul_nonneg]
  obtain ⟨v, hv, hv1, hv2⟩ := exists_approx_zero (S := PolySeq.lowestOrder) hL0 N σ hσ
  refine (graphSq_projU0_sub_le (hT.proj N) (hT.norm_proj_le N 1) (hT.norm_proj_le N 0) σ hv
    hv1 hv2 hA).trans (le_of_eq ?_)
  ring

theorem table51_err_Pt0 (N : ℕ) {L : ℝ} (hL0 : 0 ≤ L) (φ : Wv U0)
    (hφ : ∀ a, IsCsFormMin 0 0 L (φ a : W0)) :
    Feec.BGG.graphSq bggSegment.dt0 ((table51 hT hB N).Pt0 φ - φ) ≤
      3 * (2 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 0) ^ 2) *
        (L * meshSize N) ^ 2 := by
  have hA : 0 ≤ 1 + 2 * C := by linarith [hT.two_mul_nonneg]
  rw [table51, bggDiscrete_Pt0, bggSegment_dt0, graphSq_piMap]
  calc ∑ a, Feec.BGG.graphSq segD0 ((piMap (projU0 (hB.proj N)) φ - φ) a) ≤
        ∑ _a : Fin 3, 2 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 0) ^ 2 *
          (L * meshSize N) ^ 2 := by
        refine Finset.sum_le_sum fun a _ => ?_
        obtain ⟨v, hv, hv1, hv2⟩ := exists_approx_zero (S := PolySeq.lagrangeP2) hL0 N (φ a)
          (hφ a)
        refine (graphSq_projU0_sub_le (hB.proj N) (hB.norm_proj_le N 1) (hB.norm_proj_le N 0)
          (φ a) hv hv1 hv2 hA).trans (le_of_eq ?_)
        ring
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem table51_err_Pt1 (N : ℕ) {L : ℝ} (hL0 : 0 ≤ L) (u : Wv U1)
    (hu : ∀ a, IsCsFormMin 0 1 L (u a : W1)) :
    Feec.BGG.graphSq bggSegment.dt1 ((table51 hT hB N).Pt1 u - u) ≤
      3 * (2 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 1) ^ 2) *
        (L * meshSize N) ^ 2 := by
  have hA : 0 ≤ 1 + 2 * C := by linarith [hT.two_mul_nonneg]
  rw [table51, bggDiscrete_Pt1, bggSegment_dt1, graphSq_piMap]
  calc ∑ a, Feec.BGG.graphSq segD1 ((piMap (projU1 (hB.proj N)) u - u) a) ≤
        ∑ _a : Fin 3, 2 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 1) ^ 2 *
          (L * meshSize N) ^ 2 := by
        refine Finset.sum_le_sum fun a _ => ?_
        obtain ⟨v, hv, hv1, hv2⟩ := exists_approx_one (S := PolySeq.lagrangeP2) hL0 N (u a)
          (hu a)
        refine (graphSq_projU1_sub_le (hB.proj N) (hB.norm_proj_le N 2) (hB.norm_proj_le N 1)
          (u a) hv hv1 hv2 hA).trans (le_of_eq ?_)
        ring
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem table51_err_gnSq (N : ℕ) {L : ℝ} (hL0 : 0 ≤ L) (u : Wv U1)
    (hu : ∀ a, IsCsFormMin 0 1 L (u a : W1)) :
    (table51 hT hB N).gnSq ((table51 hT hB N).Pt1 u - u) ≤
      (1 + 8 * C ^ 2) * (3 * (2 * ((1 + 2 * C) * polyInterpBound 3 PolySeq.lagrangeP2 1) ^ 2)) *
        (L * meshSize N) ^ 2 := by
  have h1 := table51_gnSq_le hT hB N ((table51 hT hB N).Pt1 u - u)
  have h2 := mul_le_mul_of_nonneg_left (table51_err_Pt1 hT hB N hL0 u hu)
    (by positivity : (0 : ℝ) ≤ 1 + 8 * C ^ 2)
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ = _ := by ring

theorem table51_err_S1 (N : ℕ) {L : ℝ} (hL0 : 0 ≤ L) (u : Wv U1)
    (hSu : IsCsFormMin 0 2 L (bggSegment.S1 u)) :
    ‖bggSegment.S1 u - (table51 hT hB N).S1h u‖ ^ 2 ≤
      ((1 + 2 * C) * polyInterpBound 3 PolySeq.lowestOrder 2) ^ 2 * (L * meshSize N) ^ 2 := by
  have hA : 0 ≤ 1 + 2 * C := by linarith [hT.two_mul_nonneg]
  obtain ⟨v, hv, hv1, -⟩ := hSu.exists_mem_polyMin_le (S := PolySeq.lowestOrder)
    ((polyOrder_zero _).polyOrderAt 2) hL0 N
  have h' : ‖bggSegment.S1 u - (table51 hT hB N).S1h u‖ ≤
      (1 + 2 * C) * (polyInterpBound 3 PolySeq.lowestOrder 2 * L * meshSize N) := by
    change ‖segS1 u - (hT.proj N).π 2 (segS1 u)‖ ≤ _
    refine (norm_sub_π_le_of_mem (hT.proj N) (hT.norm_proj_le N 2) hv).trans
      (mul_le_mul_of_nonneg_left ?_ hA)
    have hv1' : ‖bggSegment.S1 u - v‖ ≤ polyInterpBound 3 PolySeq.lowestOrder 2 * L * meshSize N :=
      by simpa using hv1
    exact hv1'
  have := pow_le_pow_left₀ (norm_nonneg _) h' 2
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **Thesis Thm 5.5 on the cube with the elements of Table 5.1, with rate**: under the regularity
hypothesis (`curl H̊(curl) = curl S⁰H̊¹(Q;ℝ³)` with constant `C_R`), for every `N` and every solution
`(σ, φ, u, λ)` of the continuous system (5.3) whose components and `S¹u` are `C²` and vanish
outside `Q` (`IsCsFormMin 0`, bound `L`), with `‖λ‖, ‖S¹u‖ ≤ L` and `|⟪S¹u, d w⟫| ≤ L ‖w‖`
(`S¹u ∈ D(d¹*)`), the discrete solution of (5.6) satisfies
`‖σ − σₕ‖²_V + ‖φ − φₕ‖²_V + ‖u − uₕ‖²_{Γₕ} ≤ (K L h_N)²` with `K` independent of `N`. -/
theorem table51_rate {CR : ℝ} (hCR0 : 0 ≤ CR)
    (hCR : ∀ u : V1, ∃ φ : Vt0, bggD1 (bggS0 φ) = bggD1 u ∧ ‖φ‖ ≤ CR * ‖bggD1 u‖) :
    ∃ K, 0 ≤ K ∧ ∀ (N : ℕ) {σ : U0} {φ : Wv U0} {u : Wv U1} {lam : W1}
      {F : Wv U1 →ₗ[ℝ] ℝ} {L : ℝ}, 0 ≤ L →
      (∀ τ ψ, ⟪σ, τ⟫ - ⟪u, bggSegment.dt0 ψ⟫ -
        ⟪lam, ((bggSegment.d0 τ - bggSegment.S0 ψ : U1) : W1)⟫ = 0) →
      (∀ v, ⟪bggSegment.dt0 φ, v⟫ + ⟪bggSegment.S1 u, bggSegment.S1 v⟫ +
        ⟪bggSegment.dt1 u, bggSegment.dt1 v⟫ = F v) →
      bggSegment.d0 σ = bggSegment.S0 φ →
      IsCsFormMin 0 0 L (σ : W0) → (∀ a, IsCsFormMin 0 0 L (φ a : W0)) →
      (∀ a, IsCsFormMin 0 1 L (u a : W1)) → IsCsFormMin 0 2 L (bggSegment.S1 u) →
      ‖lam‖ ≤ L → ‖bggSegment.S1 u‖ ≤ L →
      (∀ w : U1, |⟪bggSegment.S1 u, bggSegment.d1 w⟫| ≤ L * ‖w‖) →
      ∀ {σh : U0} {φh : Wv U0} {uh : Wv U1} {lh : U1},
      σh ∈ (table51 hT hB N).V0h → φh ∈ (table51 hT hB N).Vt0h →
      uh ∈ (table51 hT hB N).Vt1h →
      (∀ τ ∈ (table51 hT hB N).V0h, ∀ ψ ∈ (table51 hT hB N).Vt0h,
        ⟪σh, τ⟫ - ⟪uh, bggSegment.dt0 ψ⟫ -
          ⟪lh, bggSegment.d0 τ - (table51 hT hB N).S0h ψ⟫ = 0) →
      (∀ v ∈ (table51 hT hB N).Vt1h, ⟪bggSegment.dt0 φh, v⟫ +
        ⟪(table51 hT hB N).S1h uh, (table51 hT hB N).S1h v⟫ +
          ⟪bggSegment.dt1 uh, bggSegment.dt1 v⟫ = F v) →
      (∀ μ ∈ (table51 hT hB N).V1h, ⟪bggSegment.d0 σh - (table51 hT hB N).S0h φh, μ⟫ = 0) →
      Feec.BGG.graphSq bggSegment.d0 (σ - σh) + Feec.BGG.graphSq bggSegment.dt0 (φ - φh) +
        (table51 hT hB N).gnSq (u - uh) ≤ (K * L * meshSize N) ^ 2 := by
  have hh0 := table51_happ0 hT hB
  obtain ⟨C0, hh1⟩ := hh0
  have hC00 := hh1.1
  have hhapp := hh1.2
  have hC := hT.two_mul_nonneg
  have hA : 0 ≤ 1 + 2 * C := by linarith
  have hreg := regConst_nonneg hT
  have hCapp_defex : ∃ x : ℝ, x = C0 + regConst C := ⟨_, rfl⟩
  obtain ⟨Capp, hCapp_def⟩ := hCapp_defex
  have hCapp0 : 0 ≤ Capp := by rw [hCapp_def]; linarith
  have hCpex : ∃ x : ℝ, x = (2 * Real.pi)⁻¹ := ⟨_, rfl⟩
  obtain ⟨Cp, hCp⟩ := hCpex
  have hCp0 : 0 ≤ Cp := by rw [hCp]; positivity
  have hCS0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hE_defex : ∃ x : ℝ,
      x = Feec.BGG.Discrete.errorConst Cp CR (Real.sqrt 2) (2 * C) Capp := ⟨_, rfl⟩
  obtain ⟨E, hE_def⟩ := hE_defex
  have hE0 : 0 ≤ E := by
    rw [hE_def]
    unfold Feec.BGG.Discrete.errorConst Feec.BGG.Discrete.Ca1 Feec.BGG.Discrete.Ca
      Feec.BGG.Discrete.KL Feec.BGG.Discrete.Cb
    positivity
  have hwaex : ∃ x : ℝ, x = √(1 + Cp ^ 2) * (1 + 2 * C * (1 + 1 * CR)) := ⟨_, rfl⟩
  obtain ⟨wa, hwa⟩ := hwaex
  have hwbex : ∃ x : ℝ, x = (1 + (1 + 2 * C) * Real.sqrt 2) * CR := ⟨_, rfl⟩
  obtain ⟨wb, hwb⟩ := hwbex
  have hwa0 : 0 ≤ wa := by rw [hwa]; positivity
  have hwb0 : 0 ≤ wb := by rw [hwb]; positivity
  have hBt0dex : ∃ x : ℝ, x = polyInterpBound 3 PolySeq.lowestOrder 0 := ⟨_, rfl⟩
  obtain ⟨Bt0, hBt0d⟩ := hBt0dex
  have hBb0dex : ∃ x : ℝ, x = polyInterpBound 3 PolySeq.lagrangeP2 0 := ⟨_, rfl⟩
  obtain ⟨Bb0, hBb0d⟩ := hBb0dex
  have hBb1dex : ∃ x : ℝ, x = polyInterpBound 3 PolySeq.lagrangeP2 1 := ⟨_, rfl⟩
  obtain ⟨Bb1, hBb1d⟩ := hBb1dex
  have hBt2dex : ∃ x : ℝ, x = polyInterpBound 3 PolySeq.lowestOrder 2 := ⟨_, rfl⟩
  obtain ⟨Bt2, hBt2d⟩ := hBt2dex
  have hBt0 : 0 ≤ Bt0 := by rw [hBt0d]; exact polyInterpBound_nonneg _ _
  have hBb0 : 0 ≤ Bb0 := by rw [hBb0d]; exact polyInterpBound_nonneg _ _
  have hBb1 : 0 ≤ Bb1 := by rw [hBb1d]; exact polyInterpBound_nonneg _ _
  have hBt2 : 0 ≤ Bt2 := by rw [hBt2d]; exact polyInterpBound_nonneg _ _
  have hKdex : ∃ x : ℝ, x = 2 * ((1 + 2 * C) * Bt0) ^ 2 + 3 * (2 * ((1 + 2 * C) * Bb0) ^ 2) +
    (1 + 8 * C ^ 2) * (3 * (2 * ((1 + 2 * C) * Bb1) ^ 2)) + 1 + (wa + wb) ^ 2 +
      ((1 + 2 * C) * Bt2) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Kd, hKd⟩ := hKdex
  have hKd0 : 0 ≤ Kd := by rw [hKd]; positivity
  refine ⟨√(E * Kd), Real.sqrt_nonneg _, fun N σ φ u lam F L hL0 c1 c2 c3 hσ hφ hu hSu hlam
    hSun hz σh φh uh lh hσh hφh huh h1 h2 h3 => ?_⟩
  have := table51_fdt1 hT hB N
  have hh : 0 ≤ meshSize N := (meshSize_pos N).le
  have H : Feec.BGG.Stability bggSegment Cp CR (Real.sqrt 2) := by rw [hCp]; exact bggStability_of hCR0 hCR
  have Bd := table51_bounded hT hB N
  have h54 := table51_compatible hT hB N
  have happ : ∀ ψ ∈ (table51 hT hB N).Vt0h,
      ‖bggSegment.S0 ψ - (table51 hT hB N).S0h ψ‖ ^ 2 ≤
        (Capp * meshSize N) ^ 2 * Feec.BGG.graphSq bggSegment.dt0 ψ := fun ψ hψ => by
    refine (hhapp N ψ hψ).trans (mul_le_mul_of_nonneg_right ?_ (Feec.BGG.graphSq_nonneg _ _))
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right
      (by rw [hCapp_def]; linarith) hh) 2
  have Rg := table51Reg hT hB N hCR0 hCR (by rw [hCapp_def]; linarith : regConst C ≤ Capp)
  have hwc := Feec.BGG.Discrete.weakConsistency_of_regularPotential_of_bound H Bd hh hCapp0 Rg
    happ hL0 hz
  have hℓ : ∀ μ, |((innerSL ℝ lam).toLinearMap ∘ₗ D1.domain.subtype) μ| ≤ L * ‖μ‖ := fun μ =>
    (abs_real_inner_le_norm lam (μ : W1)).trans (mul_le_mul_of_nonneg_right hlam (norm_nonneg _))
  have hest := Feec.BGG.Discrete.error_estimate_of_weakConsistency H Bd h54 hh hCapp0 happ hwc
    ((innerSL ℝ lam).toLinearMap ∘ₗ D1.domain.subtype) hL0 hℓ F (fun τ _ ψ _ => c1 τ ψ)
    (fun v _ => c2 v) c3 hσh hφh huh h1 h2 h3
  refine hest.trans ?_
  have hD1 := table51_err_P0 hT hB N hL0 σ hσ
  have hD2 := table51_err_Pt0 hT hB N hL0 φ hφ
  have hD3 := table51_err_gnSq hT hB N hL0 u hu
  rw [← hBt0d] at hD1
  rw [← hBb0d] at hD2
  rw [← hBb1d] at hD3
  have hK0 : 0 ≤ Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1 CR
      ‖bggSegment.S1 u‖ L := by
    unfold Feec.BGG.Discrete.weakConsistencyConst
    have := norm_nonneg (bggSegment.S1 u)
    positivity
  have hD5 : Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1 CR ‖bggSegment.S1 u‖ L ≤
      (wa + wb) * L := by
    have e : Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1 CR ‖bggSegment.S1 u‖ L =
        L * wa + ‖bggSegment.S1 u‖ * wb := by
      rw [hwa, hwb]; unfold Feec.BGG.Discrete.weakConsistencyConst; ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hSun hwb0
    calc L * wa + ‖bggSegment.S1 u‖ * wb ≤ L * wa + L * wb := add_le_add_right this _
      _ = (wa + wb) * L := by ring
  have hD5' : meshSize N ^ 2 *
      Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1 CR ‖bggSegment.S1 u‖ L ^ 2 ≤
      (wa + wb) ^ 2 * (L * meshSize N) ^ 2 := by
    have := pow_le_pow_left₀ hK0 hD5 2
    have h2 := mul_le_mul_of_nonneg_left this (sq_nonneg (meshSize N))
    exact le_of_le_of_eq h2 (by ring)
  have hD6 := table51_err_S1 hT hB N hL0 u hSu
  rw [← hBt2d] at hD6
  have hsum : Feec.BGG.graphSq bggSegment.d0 ((table51 hT hB N).P0 σ - σ) +
      Feec.BGG.graphSq bggSegment.dt0 ((table51 hT hB N).Pt0 φ - φ) +
      (table51 hT hB N).gnSq ((table51 hT hB N).Pt1 u - u) + meshSize N ^ 2 * L ^ 2 +
      meshSize N ^ 2 *
        Feec.BGG.Discrete.weakConsistencyConst Cp (Real.sqrt 2) (2 * C) 1 CR ‖bggSegment.S1 u‖ L ^ 2 +
      ‖bggSegment.S1 u - (table51 hT hB N).S1h u‖ ^ 2 ≤ Kd * (L * meshSize N) ^ 2 := by
    rw [hKd]
    linear_combination hD1 + hD2 + hD3 + hD5' + hD6
  rw [← hE_def]
  calc E * (_ : ℝ) ≤ E * (Kd * (L * meshSize N) ^ 2) := mul_le_mul_of_nonneg_left hsum hE0
    _ = (√(E * Kd) * L * meshSize N) ^ 2 := by
        rw [show (√(E * Kd) * L * meshSize N) ^ 2 = √(E * Kd) ^ 2 * (L * meshSize N) ^ 2 by ring,
          Real.sq_sqrt (mul_nonneg hE0 hKd0)]
        ring

end Table51

end Feec.Models.Cube.WeakSymmetry
