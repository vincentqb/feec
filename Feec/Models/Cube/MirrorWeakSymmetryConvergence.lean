module

public import Feec.Models.Cube.MirrorWeakSymmetryComplex
public import Feec.Models.Cube.ParitySmoothingEstimates
public import Feec.Models.Cube.MirrorWeakSymmetryFEM

/-!
# Convergence of the mirror scheme (6.5)

DOCSTRING
-/

open scoped InnerProductSpace RealInnerProductSpace ContDiff
open MeasureTheory Set Filter Finset

@[expose] public noncomputable section

namespace Feec.Models.Cube.MirrorWeakSymmetry

open Feec.Domain Feec.Mesh Feec.FiniteElement Feec.HilbertComplex Feec.Models.Cube.FEM
open Feec.Models.Cube.WeakSymmetry (W0 W1 W2 Wv rel_m10 rel_01 rel_12)
open Feec.Models.Cube.DeRhamIdent (dPart)

/-! ### Subcomplexes of the rows -/

section Dpart

variable {J : Finset (Fin 3)} {S' : (complexPart 3 J).Subcomplex}

theorem d01_apply_part (x : ((complexPart 3 J).d 0 1).domain) :
    (complexPart 3 J).d 0 1 x = dPart (cubeDomain 3) J 0 ⟨x, complexPart_d01 J ▸ x.2⟩ :=
  LinearPMap.apply_eq_of_eq' (complexPart_d01 J) x

theorem d12_apply_part (x : ((complexPart 3 J).d 1 2).domain) :
    (complexPart 3 J).d 1 2 x = dPart (cubeDomain 3) J 1 ⟨x, complexPart_d12 J ▸ x.2⟩ :=
  LinearPMap.apply_eq_of_eq' (complexPart_d12 J) x

theorem mem_dom01_part {x : W0} (hx : x ∈ (dPart (cubeDomain 3) J 0).domain) :
    x ∈ ((complexPart 3 J).d 0 1).domain := (complexPart_d01 J).symm ▸ hx

theorem mem_dom12_part {x : W1} (hx : x ∈ (dPart (cubeDomain 3) J 1).domain) :
    x ∈ ((complexPart 3 J).d 1 2).domain := (complexPart_d12 J).symm ▸ hx

theorem mem_dPart0_of_mem_V {x : W0} (hx : x ∈ S'.V 0) :
    x ∈ (dPart (cubeDomain 3) J 0).domain :=
  complexPart_d01 J ▸ S'.le_domain 0 1 hx

theorem mem_dPart1_of_mem_V {x : W1} (hx : x ∈ S'.V 1) :
    x ∈ (dPart (cubeDomain 3) J 1).domain :=
  complexPart_d12 J ▸ S'.le_domain 1 2 hx

theorem dPart0_mem_V (x : (dPart (cubeDomain 3) J 0).domain) (hx : (x : W0) ∈ S'.V 0) :
    (dPart (cubeDomain 3) J 0 x : W1) ∈ S'.V 1 := by
  have h := S'.mapsTo 0 1 x hx
  rwa [d01_apply_part] at h

theorem dPart1_mem_V (x : (dPart (cubeDomain 3) J 1).domain) (hx : (x : W1) ∈ S'.V 1) :
    (dPart (cubeDomain 3) J 1 x : W2) ∈ S'.V 2 := by
  have h := S'.mapsTo 1 2 x hx
  rwa [d12_apply_part] at h

/-- `d π = π d` in degree `0`. -/
theorem dPart0_π (P : S'.CochainProjection) (x : (dPart (cubeDomain 3) J 0).domain) :
    dPart (cubeDomain 3) J 0 ⟨P.π 0 x, mem_dPart0_of_mem_V (P.mem 0 x)⟩ =
      P.π 1 (dPart (cubeDomain 3) J 0 x) := by
  have h := P.comm 0 1 ⟨x, mem_dom01_part x.2⟩
  rw [d01_apply_part, d01_apply_part] at h
  exact h

/-- `d π = π d` in degree `1`. -/
theorem dPart1_π (P : S'.CochainProjection) (x : (dPart (cubeDomain 3) J 1).domain) :
    dPart (cubeDomain 3) J 1 ⟨P.π 1 x, mem_dPart1_of_mem_V (P.mem 1 x)⟩ =
      P.π 2 (dPart (cubeDomain 3) J 1 x) := by
  have h := P.comm 1 2 ⟨x, mem_dom12_part x.2⟩
  rw [d12_apply_part, d12_apply_part] at h
  exact h

/-- A cochain projection in degree `0`, on `D(d_J)`. -/
def projD0 (P : S'.CochainProjection) :
    (dPart (cubeDomain 3) J 0).domain →ₗ[ℝ] (dPart (cubeDomain 3) J 0).domain :=
  LinearMap.codRestrict _ (P.π 0 ∘ₗ (dPart (cubeDomain 3) J 0).domain.subtype)
    fun x => mem_dPart0_of_mem_V (P.mem 0 x)

/-- A cochain projection in degree `1`, on `D(d_J)`. -/
def projD1 (P : S'.CochainProjection) :
    (dPart (cubeDomain 3) J 1).domain →ₗ[ℝ] (dPart (cubeDomain 3) J 1).domain :=
  LinearMap.codRestrict _ (P.π 1 ∘ₗ (dPart (cubeDomain 3) J 1).domain.subtype)
    fun x => mem_dPart1_of_mem_V (P.mem 1 x)

@[simp] theorem coe_projD0 (P : S'.CochainProjection) (x : (dPart (cubeDomain 3) J 0).domain) :
    ((projD0 P x : (dPart (cubeDomain 3) J 0).domain) : W0) = P.π 0 x := rfl

@[simp] theorem coe_projD1 (P : S'.CochainProjection) (x : (dPart (cubeDomain 3) J 1).domain) :
    ((projD1 P x : (dPart (cubeDomain 3) J 1).domain) : W1) = P.π 1 x := rfl

end Dpart

/-! ### The discretization of the mirror data by a pair of rows of subcomplexes -/

section Discretization

variable (ST : (complexPart 3 ∅).Subcomplex) (SB : ∀ a : Fin 3, (complexPart 3 {a}).Subcomplex)

/-- The bottom-row discrete `0`-forms `∏ₐ V_{h,a}⁰`. -/
def bSub0 : Submodule ℝ BU0 where
  carrier := {φ | ∀ a, (φ a : W0) ∈ (SB a).V 0}
  add_mem' hφ hψ a := Submodule.add_mem _ (hφ a) (hψ a)
  zero_mem' _ := Submodule.zero_mem _
  smul_mem' c _ hφ a := Submodule.smul_mem _ c (hφ a)

/-- The bottom-row discrete `1`-forms `∏ₐ V_{h,a}¹`. -/
def bSub1 : Submodule ℝ BU1 where
  carrier := {v | ∀ a, (v a : W1) ∈ (SB a).V 1}
  add_mem' hφ hψ a := Submodule.add_mem _ (hφ a) (hψ a)
  zero_mem' _ := Submodule.zero_mem _
  smul_mem' c _ hφ a := Submodule.smul_mem _ c (hφ a)

/-- The bottom-row discrete `2`-forms `∏ₐ V_{h,a}²`. -/
def bSub2 : Submodule ℝ (Wv W2) where
  carrier := {z | ∀ a, z a ∈ (SB a).V 2}
  add_mem' hφ hψ a := Submodule.add_mem _ (hφ a) (hψ a)
  zero_mem' _ := Submodule.zero_mem _
  smul_mem' c _ hφ a := Submodule.smul_mem _ c (hφ a)

variable {SB} in
/-- Componentwise cochain projections in degree `0`. -/
def projB0 (PB : ∀ a, (SB a).CochainProjection) : BU0 →ₗ[ℝ] BU0 where
  toFun φ := WithLp.toLp 2 fun a => projD0 (PB a) (φ a)
  map_add' _ _ := PiLp.ext fun a => map_add (projD0 (PB a)) _ _
  map_smul' _ _ := PiLp.ext fun a => map_smul (projD0 (PB a)) _ _

variable {SB} in
/-- Componentwise cochain projections in degree `1`. -/
def projB1 (PB : ∀ a, (SB a).CochainProjection) : BU1 →ₗ[ℝ] BU1 where
  toFun v := WithLp.toLp 2 fun a => projD1 (PB a) (v a)
  map_add' _ _ := PiLp.ext fun a => map_add (projD1 (PB a)) _ _
  map_smul' _ _ := PiLp.ext fun a => map_smul (projD1 (PB a)) _ _

variable {SB} in
/-- Componentwise cochain projections in degree `2`. -/
def projB2 (PB : ∀ a, (SB a).CochainProjection) : Wv W2 →ₗ[ℝ] Wv W2 where
  toFun z := WithLp.toLp 2 fun a => (PB a).π 2 (z a)
  map_add' _ _ := PiLp.ext fun a => map_add ((PB a).π 2) _ _
  map_smul' _ _ := PiLp.ext fun a => map_smul ((PB a).π 2) _ _

/-- **The discretization of the mirror data** by a subcomplex `ST` of the top row `HΛ(Q)` and
subcomplexes `SB a` of the bottom components `HΛ_{a}(Q)`, with cochain projections. -/
def mirrorDiscrete (PT : ST.CochainProjection) (PB : ∀ a, (SB a).CochainProjection) :
    Feec.BGG.Discrete mirrorBGGSegment where
  V0h := (ST.V 0).comap TD0.domain.subtype
  V1h := (ST.V 1).comap TD1.domain.subtype
  W2h := ST.V 2
  Vt0h := bSub0 SB
  Vt1h := bSub1 SB
  Wt2h := bSub2 SB
  d0_mem x hx := dPart0_mem_V x hx
  d1_mem x hx := dPart1_mem_V x hx
  dt0_mem x hx a := dPart0_mem_V (x a) (hx a)
  dt1_mem x hx a := dPart1_mem_V (x a) (hx a)
  P0 := projD0 PT
  P1 := projD1 PT
  P2 := PT.π 2
  Pt0 := projB0 PB
  Pt1 := projB1 PB
  Pt2 := projB2 PB
  P0_mem x := PT.mem 0 x
  P1_mem x := PT.mem 1 x
  P2_mem x := PT.mem 2 x
  Pt0_mem x a := (PB a).mem 0 (x a)
  Pt1_mem x a := (PB a).mem 1 (x a)
  Pt2_mem x a := (PB a).mem 2 (x a)
  P0_id x hx := Subtype.ext (PT.proj 0 x hx)
  P1_id x hx := Subtype.ext (PT.proj 1 x hx)
  P2_id x hx := PT.proj 2 x hx
  Pt0_id x hx := PiLp.ext fun a => Subtype.ext ((PB a).proj 0 (x a) (hx a))
  Pt1_id x hx := PiLp.ext fun a => Subtype.ext ((PB a).proj 1 (x a) (hx a))
  Pt2_id x hx := PiLp.ext fun a => (PB a).proj 2 (x a) (hx a)
  comm0 x := Subtype.ext (dPart0_π PT x)
  comm1 x := dPart1_π PT x
  commt0 x := PiLp.ext fun a => Subtype.ext (dPart0_π (PB a) (x a))
  commt1 x := PiLp.ext fun a => dPart1_π (PB a) (x a)

variable {ST SB}

theorem graphSq_bD1 (w : BU1) :
    Feec.BGG.graphSq bD1 w = ∑ a, (‖(w a : W1)‖ ^ 2 + ‖BD1 a (w a)‖ ^ 2) := by
  unfold Feec.BGG.graphSq
  rw [norm_sq_BU1, norm_sq_bD1, ← Finset.sum_add_distrib]

/-- **Uniform bounds of the mirror discretization** from graph-norm bounds of the projections in
degree `1 → 2` and an `L²` bound of the top projection in degree `2`. -/
theorem mirrorDiscrete_bounded {PT : ST.CochainProjection} {PB : ∀ a, (SB a).CochainProjection}
    {C : ℝ} (hC0 : 0 ≤ C) (hT : ∀ x, ‖PT.π 2 x‖ ≤ C * ‖x‖) (hTg : PT.IsGraphBounded 1 2 C)
    (hBg : ∀ a, (PB a).IsGraphBounded 1 2 C) : (mirrorDiscrete ST SB PT PB).Bounded C where
  CP_nonneg := hC0
  P1 x := by
    have h := hTg ⟨x, mem_dom12_part x.2⟩
    rw [d12_apply_part, d12_apply_part] at h
    exact h
  P2 z := hT z
  Pt1 v := by
    change Feec.BGG.graphSq bD1 (projB1 PB v) ≤ C ^ 2 * Feec.BGG.graphSq bD1 v
    rw [graphSq_bD1, graphSq_bD1, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have h := hBg a ⟨v a, mem_dom12_part (v a).2⟩
    rw [d12_apply_part, d12_apply_part] at h
    exact h

end Discretization


/-! ### The parity smoother and `S⁰`: compatibility (5.4) -/

section Compat

open Feec.Models.Cube.ParitySmoother

variable {n : ℕ} (ρ : ReflKernel n)

theorem smoothFun_zero' (pv : Fin n → ℝ) : smoothFun ρ pv (0 : (Fin n → ℝ) → ℝ) = 0 := by
  simpa using smoothFun_smul ρ pv 0 (0 : (Fin n → ℝ) → ℝ)

/-- The smoothed parity extension of a finite combination of `L²` functions. -/
theorem smoothFun_L2_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (f : ι → L2 ℝ (Geometry.Q (Fin n))) (pv : Fin n → ℝ) :
    smoothFun ρ pv (((∑ i ∈ s, c i • f i : L2 ℝ (Geometry.Q (Fin n))) : (Fin n → ℝ) → ℝ)) =
      ∑ i ∈ s, c i • smoothFun ρ pv (f i : (Fin n → ℝ) → ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [smoothFun_congr_ae ρ pv (Lp.coeFn_zero ℝ 2 _), smoothFun_zero']
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      smoothFun_congr_ae ρ pv (Lp.coeFn_add _ _),
      smoothFun_add ρ pv (integrableOn_L2 _) (integrableOn_L2 _), ih,
      smoothFun_congr_ae ρ pv (Lp.coeFn_smul _ _), smoothFun_smul]

theorem formExt_apply_pt {k : ℤ} (w : formIdx n k → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    (fun s => formExt w s x) = formExt (fun r => w r x) := by
  funext s
  unfold formExt
  split_ifs <;> rfl

theorem symmDiff_empty_singleton (a : Fin n) : symmDiff (∅ : Finset (Fin n)) {a} = {a} := by
  ext x; simp [Finset.mem_symmDiff]

/-- **The parity smoother intertwines `S⁰`** at the level of smooth forms, for compatible classes
(the components `a` in the classes `J ∆ {a}`): `R^J S⁰ y = S⁰ (R^{J ∆ {a}} yₐ)ₐ` pointwise, the
smooth-form version of `Feec.Models.Cube.ParitySmoother.wsL2_paritySmooth_symmDiff`. -/
theorem paritySmoothForm_wsL2_zero {Ω : Set (Fin n → ℝ)} (J : Finset (Fin n))
    (hΩ : Ω = Geometry.Q (Fin n))
    (y : PiLp 2 (fun _ : Fin n => L2F ℝ Ω (formIdx n ((0 : ℕ) : ℤ)))) :
    Submodule.inclusion c1Forms_le_contForms
        (paritySmoothForm ρ J hΩ (((0 : ℕ) : ℤ) + 1) (wsL2 (Ω := Ω) ((0 : ℕ) : ℤ) y)) =
      coordWedgeC (fun a => Submodule.inclusion c1Forms_le_contForms
        (paritySmoothForm ρ (symmDiff J {a}) hΩ ((0 : ℕ) : ℤ) (y a))) := by
  subst hΩ
  refine Subtype.ext (funext fun x => funext fun t => ?_)
  change formExt (parCoeff ρ J (wsL2 (Ω := Geometry.Q (Fin n)) ((0 : ℕ) : ℤ) y)) t x =
    coordWedgeSum (fun a s => formExt (parCoeff ρ (symmDiff J {a}) (y a)) s x) t
  rw [show (fun a s => formExt (parCoeff ρ (symmDiff J {a}) (y a)) s x) =
      fun a => formExt (fun r => parCoeff ρ (symmDiff J {a}) (y a) r x) from
    funext fun a => formExt_apply_pt _ x]
  by_cases ht : (#t : ℤ) = ((0 : ℕ) : ℤ) + 1
  · rw [formExt_of_card _ ht,
      coordWedgeSum_formExt (fun a r => parCoeff ρ (symmDiff J {a}) (y a) r x) ⟨t, ht⟩]
    simp only [parCoeff]
    rw [wsL2_apply, smoothFun_L2_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : wsCoeff ((0 : ℕ) : ℤ) ⟨t, ht⟩ p = 0
    · rw [hp, zero_mul, zero_mul]
    · congr 1
      rw [wsCoeff_eq] at hp
      split_ifs at hp with h
      · obtain ⟨ha, he⟩ := h
        rw [← he, pvec_symmDiff_erase J ha]
      · exact absurd rfl hp
  · have h1 : formExt (parCoeff ρ J (wsL2 (Ω := Geometry.Q (Fin n)) ((0 : ℕ) : ℤ) y)) t x = 0 := by
      unfold formExt; rw [dite_eq_right_iff.2 fun h => absurd h ht]; rfl
    rw [h1]
    refine (isDeg_coordWedgeSum (k := 0) (fun a s hs => ?_) t fun h => ht ?_).symm
    · have : ¬ ((#s : ℤ) = ((0 : ℕ) : ℤ)) := by exact_mod_cast hs
      unfold formExt; exact dite_eq_right_iff.2 fun h => absurd h this
    · rw [h]; push_cast

end Compat

section CompatMesh

open Feec.Models.Cube.ParitySmoother PolySeq

variable (ρ : ReflKernel 3)

/-- **(5.4) at the mesh level**: if the bottom-row parity-smoothed interpolants of `y`, `y'` agree
componentwise (classes `{a}`), so do the top-row parity-smoothed interpolants of `S⁰y`, `S⁰y'`
(class `∅`): `Π_h R S⁰ y = Π¹ S⁰ Π̃⁰ R̃ y` (corrected Prop 5.7, `bggS0h_tensorInterp`). -/
theorem paritySmoothedInterp_wsL2_zero_eq (M : SimplicialMesh 3) (hM : M.domain = Geometry.Q (Fin 3))
    {y y' : PiLp 2 (fun _ : Fin 3 => L2F ℝ M.domain (formIdx 3 0))}
    (h : ∀ a, Ebot.paritySmoothedInterp M ρ {a} hM ((0 : ℕ) : ℤ) (y a) =
      Ebot.paritySmoothedInterp M ρ {a} hM ((0 : ℕ) : ℤ) (y' a)) :
    Etop.paritySmoothedInterp M ρ ∅ hM (((0 : ℕ) : ℤ) + 1) (wsL2 (Ω := M.domain) 0 y) =
      Etop.paritySmoothedInterp M ρ ∅ hM (((0 : ℕ) : ℤ) + 1) (wsL2 (Ω := M.domain) 0 y') := by
  have hMo : IsOpen M.domain := isOpen_of_eq_Q hM
  have key : ∀ z : PiLp 2 (fun _ : Fin 3 => L2F ℝ M.domain (formIdx 3 0)),
      Etop.paritySmoothedInterp M ρ ∅ hM (((0 : ℕ) : ℤ) + 1) (wsL2 (Ω := M.domain) 0 z) =
        Etop.glue M ((1 : ℕ) : ℤ) ((bggS0h M (Ebot.tensorInterp M 3 0 fun a =>
          Submodule.inclusion c1Forms_le_contForms (paritySmoothForm ρ {a} hM ((0 : ℕ) : ℤ)
            (z a))) : Etop.globalSpace M 1) : Etop.Piecewise M 1) := by
    intro z
    change Etop.glue M ((1 : ℕ) : ℤ) (Etop.globalInterp M 1 (Submodule.inclusion
      c1Forms_le_contForms (paritySmoothForm ρ ∅ hM (((0 : ℕ) : ℤ) + 1)
        (wsL2 (Ω := M.domain) ((0 : ℕ) : ℤ) z))) : Etop.Piecewise M 1) = _
    rw [paritySmoothForm_wsL2_zero ρ ∅ hM z, bggS0h_tensorInterp]
    simp only [symmDiff_empty_singleton]
  rw [key, key]
  have ht : (Ebot.tensorInterp M 3 0 fun a => Submodule.inclusion c1Forms_le_contForms
      (paritySmoothForm ρ {a} hM ((0 : ℕ) : ℤ) (y a))) =
      Ebot.tensorInterp M 3 0 fun a => Submodule.inclusion c1Forms_le_contForms
        (paritySmoothForm ρ {a} hM ((0 : ℕ) : ℤ) (y' a)) := by
    funext a
    exact Subtype.ext (Ebot.glue_injective M hMo 0 (h a))
  rw [ht]


/-- `paritySmoothedInterp_wsL2_zero_eq` transported along `(mesh 3 N).domain = Θ`. -/
theorem commutingMapOfEqPart_wsL2_zero_eq (N : ℕ) {Θ : Set (Fin 3 → ℝ)}
    (e : (mesh 3 N).domain = Θ) (hΘ : IsOpen Θ) (hΘQ : Θ ⊆ Geometry.Q (Fin 3))
    {y y' : PiLp 2 (fun _ : Fin 3 => L2F ℝ Θ (formIdx 3 0))}
    (h : ∀ a, (commutingMapOfEqPart e (isOpen_of_eq_Q (mesh_domain_eq_Q N))
        (mesh_domain_eq_Q N).le hΘ hΘQ {a}
        (Ebot.paritySmoothedCommutingMap (mesh 3 N) ρ {a} (mesh_domain_eq_Q N))).Q 0 (y a) =
      (commutingMapOfEqPart e (isOpen_of_eq_Q (mesh_domain_eq_Q N))
        (mesh_domain_eq_Q N).le hΘ hΘQ {a}
        (Ebot.paritySmoothedCommutingMap (mesh 3 N) ρ {a} (mesh_domain_eq_Q N))).Q 0 (y' a)) :
    (commutingMapOfEqPart e (isOpen_of_eq_Q (mesh_domain_eq_Q N)) (mesh_domain_eq_Q N).le hΘ hΘQ
        ∅ (Etop.paritySmoothedCommutingMap (mesh 3 N) ρ ∅ (mesh_domain_eq_Q N))).Q 1
          (wsL2 (Ω := Θ) 0 y) =
      (commutingMapOfEqPart e (isOpen_of_eq_Q (mesh_domain_eq_Q N)) (mesh_domain_eq_Q N).le hΘ
        hΘQ ∅ (Etop.paritySmoothedCommutingMap (mesh 3 N) ρ ∅ (mesh_domain_eq_Q N))).Q 1
          (wsL2 (Ω := Θ) 0 y') := by
  subst e
  exact paritySmoothedInterp_wsL2_zero_eq ρ (mesh 3 N) (mesh_domain_eq_Q N) h

end CompatMesh


/-! ### The parity-smoothed projections of one smoother for both rows -/

section Estimates

open Feec.Models.Cube.ParitySmoother

theorem _root_.Feec.Models.Cube.FEM.ParitySmoothingEstimates.mono {n : ℕ} [NeZero n] {J : Finset (Fin n)} {S : PolySeq}
    {ρ : ℕ → ReflKernel n} {C C' : ℝ} (hE : ParitySmoothingEstimates n J S ρ C) (hC : C ≤ C') :
    ParitySmoothingEstimates n J S ρ C' where
  half_le := hE.half_le.trans hC
  bound N i x := (hE.bound N i x).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))
  close := hE.close

/-- **One smoother for both rows of the mirror scheme**: kernels `ρ_N` (of radius `γ h_N / 32`)
and a constant `C` for which the parity smoothing estimates hold for the top row (class `∅`,
`P₁⁻Λ`) and for every bottom component (class `{a}`, `P₂Λ ⊗ ℝ³`). -/
theorem exists_mirror_estimates : ∃ (ρ : ℕ → ReflKernel 3) (C : ℝ),
    ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C ∧
      ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C := by
  obtain ⟨γT, hγT, hγT2, hT⟩ := paritySmoothingEstimates_parKernel (n := 3) PolySeq.lowestOrder
  obtain ⟨γB, hγB, hγB2, hB⟩ := paritySmoothingEstimates_parKernel (n := 3) PolySeq.lagrangeP2
  set γ := min γT γB
  have hγ : 0 < γ := lt_min hγT hγB
  have hγ1 : γ ≤ 1 := (min_le_left _ _).trans (by linarith)
  obtain ⟨CT, hCT⟩ := hT γ hγ hγ1 (min_le_left _ _) ∅
  choose CB hCB using fun a : Fin 3 => hB γ hγ hγ1 (min_le_right _ _) {a}
  refine ⟨parKernel 3 γ hγ hγ1, max CT (∑ a, |CB a|), hCT.mono (le_max_left _ _), fun a =>
    (hCB a).mono ((le_abs_self _).trans ((Finset.single_le_sum (f := fun a => |CB a|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ a)).trans (le_max_right _ _)))⟩

end Estimates

section MirrorFEM

open Feec.Models.Cube.ParitySmoother PolySeq

variable {ρ : ℕ → ReflKernel 3} {C : ℝ}
  (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C)

/-- **(5.4) for the parity-smoothed projections**: `π¹ S⁰ π̃⁰ = π¹ S⁰` (common smoother;
`π̃⁰` componentwise, classes `{a}`). -/
theorem proj_wsL2_compatible (N : ℕ) (x : PiLp 2 (fun _ : Fin 3 => W0)) :
    (hT.proj N).π 1 (wsL2 (Ω := cubeDomain 3) 0
        (WithLp.toLp 2 fun a => ((hB a).proj N).π 0 (x a))) =
      (hT.proj N).π 1 (wsL2 (Ω := cubeDomain 3) 0 x) := by
  change ((paritySmoothed 3 PolySeq.lowestOrder N ∅ (ρ N)).toCochainProjection
      (θ := 1 / 2) (by norm_num) (hT.close N)).π 1 _ =
    ((paritySmoothed 3 PolySeq.lowestOrder N ∅ (ρ N)).toCochainProjection
      (θ := 1 / 2) (by norm_num) (hT.close N)).π 1 _
  rw [Subcomplex.CommutingMap.toCochainProjection_π,
    Subcomplex.CommutingMap.toCochainProjection_π]
  congr 3
  refine commutingMapOfEqPart_wsL2_zero_eq (ρ N) N (mesh_domain 3 N) (isOpen_cubeDomain 3)
    (cubeDomain_subset_Q 3) fun a => ?_
  exact (paritySmoothed 3 PolySeq.lagrangeP2 N {a} (ρ N)).Q_restrictVEquiv_symm
    (θ := 1 / 2) (by norm_num) ((hB a).close N) 0
    ⟨(paritySmoothed 3 PolySeq.lagrangeP2 N {a} (ρ N)).Q 0 (x a),
      (paritySmoothed 3 PolySeq.lagrangeP2 N {a} (ρ N)).mem 0 (x a)⟩

/-- **The mirror scheme (6.5) as a discretization of the mirror data**: the spaces of Table 6.1
with the mirror boundary conditions (`polyPartial`: top row `P₁Λ⁰ → P₁⁻Λ¹ → P₁⁻Λ²` without
boundary condition, bottom component `a` `P₂Λ⁰ → P₂⁻Λ¹ → P₁Λ²` with vanishing degrees of freedom on
the faces normal to `eₐ`) on the level-`(N + 1)` Freudenthal mesh, with the parity-smoothed
projections `π = J⁻¹ Π_h R` of one smoother. -/
def mirrorFEM (N : ℕ) : Feec.BGG.Discrete mirrorBGGSegment :=
  mirrorDiscrete (polyPartial 3 PolySeq.lowestOrder N ∅)
    (fun a => polyPartial 3 PolySeq.lagrangeP2 N {a}) (hT.proj N) fun a => (hB a).proj N

/-- **(5.4) holds for the mirror scheme** (`Feec.BGG.Discrete.Compatible`). -/
theorem mirrorFEM_compatible (N : ℕ) : (mirrorFEM hT hB N).Compatible := fun ψ => by
  refine Subtype.ext ?_
  change (hT.proj N).π 1 (wsL2 (Ω := cubeDomain 3) 0 (bIncl0 (projB0 (fun a => (hB a).proj N) ψ))) =
    (hT.proj N).π 1 (wsL2 (Ω := cubeDomain 3) 0 (bIncl0 ψ))
  have e : bIncl0 (projB0 (fun a => (hB a).proj N) ψ) =
      WithLp.toLp 2 fun a => ((hB a).proj N).π 0 (bIncl0 ψ a) := PiLp.ext fun a => rfl
  rw [e, proj_wsL2_compatible]

/-- **Uniform bounds of the mirror projections**: `Discrete.Bounded (2C)` for every `N`. -/
theorem mirrorFEM_bounded (N : ℕ) : (mirrorFEM hT hB N).Bounded (2 * C) :=
  mirrorDiscrete_bounded hT.two_mul_nonneg (hT.norm_proj_le N 2) (hT.isGraphBounded_proj N 1 2)
    fun a => (hB a).isGraphBounded_proj N 1 2

instance mirrorFEM_fd0 (N : ℕ) : FiniteDimensional ℝ (mirrorFEM hT hB N).V0h :=
  WeakSymmetry.finiteDimensional_comap _ _
instance mirrorFEM_fd1 (N : ℕ) : FiniteDimensional ℝ (mirrorFEM hT hB N).V1h :=
  WeakSymmetry.finiteDimensional_comap _ _
instance mirrorFEM_fd2 (N : ℕ) : FiniteDimensional ℝ (mirrorFEM hT hB N).W2h :=
  inferInstanceAs (FiniteDimensional ℝ ((polyPartial 3 PolySeq.lowestOrder N ∅).V 2))

end MirrorFEM


/-! ### Prop 5.9(1) for `π¹` on the mirror spaces -/

section ApproxS0

open PolySeq

/-- **Prop 5.9(1) on the mirror spaces (mesh level)**: for `ψ ∈ ∏ₐ P₂Λ⁰_{Γₐ}` the canonical
`w = Π¹S⁰ψ ∈ P₁⁻Λ¹` (no boundary condition on the top row) satisfies `‖S⁰ψ − w‖ ≤ C h ‖∇ψ‖`,
`C` independent of `N` (`norm_sub_glue_bggS0h_le`, which needs no boundary condition). -/
theorem exists_sub_wsL2_le_mesh_mirror : ∃ C, 0 ≤ C ∧ ∀ (N : ℕ)
    (ψ : PiLp 2 (fun _ : Fin 3 => L2F ℝ (mesh 3 N).domain (formIdx 3 0)))
    (_ : ∀ a, ψ a ∈ Ebot.VPartial (mesh 3 N) (partialFaces 3 {a}) 0)
    (hd : ∀ a, ψ a ∈ (dPart (mesh 3 N).domain {a} 0).domain),
    ∃ w ∈ Etop.VPartial (mesh 3 N) (partialFaces 3 ∅) 1,
      ‖WeakSymmetry.wsZero (Ω := (mesh 3 N).domain) ψ - w‖ ≤ C * hN N *
        ‖(WithLp.toLp 2 fun a => dPart (mesh 3 N).domain {a} 0 ⟨ψ a, hd a⟩ :
          PiLp 2 (fun _ : Fin 3 => L2F ℝ (mesh 3 N).domain (formIdx 3 1)))‖ := by
  obtain ⟨C, hC0, hC⟩ := WeakSymmetry.norm_sub_glue_bggS0h_le
  refine ⟨C, hC0, fun N ψ hψ hd => ?_⟩
  have hψ' : ∀ a, ∃ v : Ebot.globalSpacePartial (mesh 3 N) (partialFaces 3 {a}) 0,
      Ebot.glue (mesh 3 N) ((0 : ℕ) : ℤ) (v : Ebot.Piecewise (mesh 3 N) 0) = ψ a := fun a => hψ a
  choose u hu using hψ'
  set u' : Fin 3 → Ebot.globalSpace (mesh 3 N) 0 := fun a =>
    ⟨(u a : Ebot.Piecewise (mesh 3 N) 0), Ebot.globalSpacePartial_le _ _ 0 (u a).2⟩
  have hψe : ψ = Ebot.tensorGlue (mesh 3 N) 3 ((0 : ℕ) : ℤ) fun a =>
      ((u' a : Ebot.globalSpace (mesh 3 N) 0) : Ebot.Piecewise (mesh 3 N) 0) :=
    PiLp.ext fun a => (hu a).symm
  have hmem : Etop.glue (mesh 3 N) (((0 : ℕ) : ℤ) + 1)
      ((bggS0h (mesh 3 N) u' : Etop.globalSpace (mesh 3 N) 1) : Etop.Piecewise (mesh 3 N) 1) ∈
        Etop.VPartial (mesh 3 N) (partialFaces 3 ∅) 1 := by
    rw [VPartial_empty]
    exact ⟨bggS0h (mesh 3 N) u', rfl⟩
  refine ⟨_, hmem, ?_⟩
  have hd' : (WithLp.toLp 2 fun a => dPart (mesh 3 N).domain {a} 0 ⟨ψ a, hd a⟩ :
      PiLp 2 (fun _ : Fin 3 => L2F ℝ (mesh 3 N).domain (formIdx 3 1))) =
      Ebot.tensorGlue (mesh 3 N) 3 ((0 + 1 : ℕ) : ℤ)
        fun a => Ebot.dPiecewise (mesh 3 N) 0
          ((u' a : Ebot.globalSpace (mesh 3 N) 0) : Ebot.Piecewise (mesh 3 N) 0) := by
    refine PiLp.ext fun a => ?_
    obtain ⟨h, hval⟩ := glue_mem_dPart Ebot (mesh_domain_eq_Q N) {a} 0 (u a)
    have e : (⟨ψ a, hd a⟩ : (dPart (mesh 3 N).domain {a} 0).domain) = ⟨_, h⟩ :=
      Subtype.ext (hu a).symm
    change dPart (mesh 3 N).domain {a} 0 ⟨ψ a, hd a⟩ = _
    rw [e]
    exact hval
  rw [hd', hψe]
  exact hC N u'

/-- `exists_sub_wsL2_le_mesh_mirror` transported to a domain `Θ = (mesh 3 N).domain`. -/
theorem exists_sub_wsL2_le_of_eq_mirror {C : ℝ} (N : ℕ)
    (hC : ∀ (ψ : PiLp 2 (fun _ : Fin 3 => L2F ℝ (mesh 3 N).domain (formIdx 3 0)))
      (_ : ∀ a, ψ a ∈ Ebot.VPartial (mesh 3 N) (partialFaces 3 {a}) 0)
      (hd : ∀ a, ψ a ∈ (dPart (mesh 3 N).domain {a} 0).domain),
      ∃ w ∈ Etop.VPartial (mesh 3 N) (partialFaces 3 ∅) 1,
        ‖WeakSymmetry.wsZero (Ω := (mesh 3 N).domain) ψ - w‖ ≤ C * hN N *
          ‖(WithLp.toLp 2 fun a => dPart (mesh 3 N).domain {a} 0 ⟨ψ a, hd a⟩ :
            PiLp 2 (fun _ : Fin 3 => L2F ℝ (mesh 3 N).domain (formIdx 3 1)))‖)
    {Θ : Set (Fin 3 → ℝ)} (e : (mesh 3 N).domain = Θ) (hΘ : IsOpen Θ)
    (hΘQ : Θ ⊆ Geometry.Q (Fin 3))
    (ψ : PiLp 2 (fun _ : Fin 3 => L2F ℝ Θ (formIdx 3 0)))
    (hψ : ∀ a, ψ a ∈ (partialSubcomplexOfEq e (isOpen_of_eq_Q (mesh_domain_eq_Q N))
      (mesh_domain_eq_Q N).le hΘ hΘQ {a}
      (subcomplexPart Ebot (mesh 3 N) (mesh_domain_eq_Q N) {a})).V 0)
    (hd : ∀ a, ψ a ∈ (dPart Θ {a} 0).domain) :
    ∃ w ∈ (partialSubcomplexOfEq e (isOpen_of_eq_Q (mesh_domain_eq_Q N))
      (mesh_domain_eq_Q N).le hΘ hΘQ ∅
      (subcomplexPart Etop (mesh 3 N) (mesh_domain_eq_Q N) ∅)).V 1,
      ‖WeakSymmetry.wsZero (Ω := Θ) ψ - @id (L2F ℝ Θ (formIdx 3 1)) w‖ ≤ C * hN N *
        ‖(WithLp.toLp 2 fun a => dPart Θ {a} 0 ⟨ψ a, hd a⟩ :
          PiLp 2 (fun _ : Fin 3 => L2F ℝ Θ (formIdx 3 1)))‖ := by
  subst e
  exact hC ψ hψ hd

variable {ρ : ℕ → Feec.Models.Cube.ParitySmoother.ReflKernel 3} {C : ℝ}
  (hT : ParitySmoothingEstimates 3 ∅ PolySeq.lowestOrder ρ C)
  (hB : ∀ a : Fin 3, ParitySmoothingEstimates 3 {a} PolySeq.lagrangeP2 ρ C)

/-- **Consistency of `S₀,ₕ = π¹S⁰` on the mirror spaces** ([QuennevilleBelair2015], Prop 5.9(1),
transferred to the smoothed projection): `‖(I − π¹)S⁰ψ‖ ≤ C_app h ‖ψ‖_V` on
`Ṽₕ⁰ = ∏ₐ P₂Λ⁰_{Γₐ}`. -/
theorem mirrorFEM_happ0 : ∃ Capp, 0 ≤ Capp ∧ ∀ N, ∀ ψ ∈ (mirrorFEM hT hB N).Vt0h,
    ‖mirrorBGGSegment.S0 ψ - (mirrorFEM hT hB N).S0h ψ‖ ^ 2 ≤
      (Capp * meshSize N) ^ 2 * Feec.BGG.graphSq mirrorBGGSegment.dt0 ψ := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_sub_wsL2_le_mesh_mirror
  have hC := hT.two_mul_nonneg
  refine ⟨(1 + 2 * C) * C₁, by positivity, fun N ψ hψ => ?_⟩
  obtain ⟨w, hw, hwle⟩ := exists_sub_wsL2_le_of_eq_mirror N (hC₁ N) (mesh_domain 3 N)
    (isOpen_cubeDomain 3) (cubeDomain_subset_Q 3) (bIncl0 ψ) (fun a => hψ a) (fun a => (ψ a).2)
  have hd : ‖(WithLp.toLp 2 fun a => dPart (cubeDomain 3) {a} 0 ⟨bIncl0 ψ a, (ψ a).2⟩ :
      PiLp 2 (fun _ : Fin 3 => L2F ℝ (cubeDomain 3) (formIdx 3 1)))‖ =
      ‖mirrorBGGSegment.dt0 ψ‖ := norm_bIncl1 (bD0 ψ)
  have h1 : ‖mirrorBGGSegment.S0 ψ - (mirrorFEM hT hB N).S0h ψ‖ ≤
      (1 + 2 * C) * (C₁ * meshSize N * ‖mirrorBGGSegment.dt0 ψ‖) := by
    change ‖WeakSymmetry.wsZero (Ω := cubeDomain 3) (bIncl0 ψ) -
      (hT.proj N).π 1 (WeakSymmetry.wsZero (Ω := cubeDomain 3) (bIncl0 ψ))‖ ≤ _
    refine (norm_sub_π_le_of_mem (hT.proj N) (hT.norm_proj_le N 1) hw).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    rw [← hd, ← hN_eq_meshSize]
    exact hwle
  have h2 : ‖mirrorBGGSegment.dt0 ψ‖ ^ 2 ≤ Feec.BGG.graphSq mirrorBGGSegment.dt0 ψ := by
    unfold Feec.BGG.graphSq; nlinarith [sq_nonneg ‖ψ‖]
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc _ ≤ ((1 + 2 * C) * (C₁ * meshSize N * ‖mirrorBGGSegment.dt0 ψ‖)) ^ 2 := h3
    _ = ((1 + 2 * C) * C₁ * meshSize N) ^ 2 * ‖mirrorBGGSegment.dt0 ψ‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)

end ApproxS0

end Feec.Models.Cube.MirrorWeakSymmetry
