module

public import Feec.HilbertComplex.BGG.ToComplex
public import Feec.Variational.SaddlePoint

/-!
# Weak symmetry: the saddle point problem of the BGG complex

For real analytic BGG data, the mixed Hodge Laplacian of the complex with weak symmetries (5.1) is
the saddle point problem (5.3) of [QuennevilleBelair2015], §5.1, with the constraint `dσ = Sφ`
imposed by a multiplier in the completion `W̌¹` of `W¹` for `|||λ||| = ‖B*λ‖`; it is equivalent to
the reduced Hodge Laplacian (5.2), and well posed under `Hilb.Hyps` by Brezzi's theorem
([Brezzi1974]).

## Main results

* `Hilb.existsUnique_isSaddle`: under `Hyps`, (5.3) is well posed on `X × W̌¹`.
* `Hilb.isSaddle_iff_isReduced`: `(x, λ)` solves (5.3) iff `x` solves (5.2) with multiplier `λ`.

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  §5.1, §4.5
* [F. Brezzi, *On the existence, uniqueness and approximation of saddle-point problems arising from Lagrangian multipliers*][Brezzi1974]

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped RealInnerProductSpace
open Set Filter Topology

@[expose] public noncomputable section

namespace Feec.BGG

section ProdSpaces

variable {V0 Vt0 Vt1 : Type*} [NormedAddCommGroup V0] [InnerProductSpace ℝ V0]
  [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0] [NormedAddCommGroup Vt1] [InnerProductSpace ℝ Vt1]

/-- `P = V⁰ × Ṽ⁰` with the `ℓ²` product norm. -/
abbrev Psp (V0 Vt0 : Type*) := WithLp 2 (V0 × Vt0)

/-- The trial/test space `X = V⁰ × Ṽ⁰ × Ṽ¹` of (5.3), with the `ℓ²` product of graph norms. -/
abbrev Xsp (V0 Vt0 Vt1 : Type*) := WithLp 2 (Psp V0 Vt0 × Vt1)

variable (V0 Vt0 Vt1) in
/-- coordinate projections of `X` -/
def pP : Xsp V0 Vt0 Vt1 →L[ℝ] Psp V0 Vt0 := WithLp.fstL 2 ℝ (Psp V0 Vt0) Vt1
variable (V0 Vt0 Vt1) in
def pu : Xsp V0 Vt0 Vt1 →L[ℝ] Vt1 := WithLp.sndL 2 ℝ (Psp V0 Vt0) Vt1
variable (V0 Vt0 Vt1) in
def pσ : Xsp V0 Vt0 Vt1 →L[ℝ] V0 := WithLp.fstL 2 ℝ V0 Vt0 ∘L pP V0 Vt0 Vt1
variable (V0 Vt0 Vt1) in
def pφ : Xsp V0 Vt0 Vt1 →L[ℝ] Vt0 := WithLp.sndL 2 ℝ V0 Vt0 ∘L pP V0 Vt0 Vt1

/-- `(σ, φ, u) ∈ X` -/
def mkX (σ : V0) (φ : Vt0) (u : Vt1) : Xsp V0 Vt0 Vt1 := WithLp.toLp 2 (WithLp.toLp 2 (σ, φ), u)

@[simp] lemma pσ_mkX (σ : V0) (φ : Vt0) (u : Vt1) : pσ V0 Vt0 Vt1 (mkX σ φ u) = σ := rfl
@[simp] lemma pφ_mkX (σ : V0) (φ : Vt0) (u : Vt1) : pφ V0 Vt0 Vt1 (mkX σ φ u) = φ := rfl
@[simp] lemma pu_mkX (σ : V0) (φ : Vt0) (u : Vt1) : pu V0 Vt0 Vt1 (mkX σ φ u) = u := rfl

lemma mkX_eta (x : Xsp V0 Vt0 Vt1) :
    mkX (pσ V0 Vt0 Vt1 x) (pφ V0 Vt0 Vt1 x) (pu V0 Vt0 Vt1 x) = x := rfl

lemma norm_sq_X (x : Xsp V0 Vt0 Vt1) :
    ‖x‖ ^ 2 = ‖pσ V0 Vt0 Vt1 x‖ ^ 2 + ‖pφ V0 Vt0 Vt1 x‖ ^ 2 + ‖pu V0 Vt0 Vt1 x‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]; rfl

lemma inner_X (x y : Xsp V0 Vt0 Vt1) :
    ⟪x, y⟫ = ⟪pσ V0 Vt0 Vt1 x, pσ V0 Vt0 Vt1 y⟫ + ⟪pφ V0 Vt0 Vt1 x, pφ V0 Vt0 Vt1 y⟫ +
      ⟪pu V0 Vt0 Vt1 x, pu V0 Vt0 Vt1 y⟫ := rfl

/-- bounded bilinear form `(x, y) ↦ ⟪f x, g y⟫` -/
def ip {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f g : Xsp V0 Vt0 Vt1 →L[ℝ] E) : Xsp V0 Vt0 Vt1 →L[ℝ] Xsp V0 Vt0 Vt1 →L[ℝ] ℝ :=
  (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp f g

end ProdSpaces

/-! ## Brezzi's theorem for real bilinear forms -/

section Brezzi

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- A real bounded bilinear form, seen as a sesquilinear form over `ℝ`. -/
def toSesq (a : X →L[ℝ] X →L[ℝ] ℝ) : X →L[ℝ] X →L⋆[ℝ] ℝ :=
  LinearMap.mkContinuous₂ (LinearMap.mk₂'ₛₗ (RingHom.id ℝ) (starRingEnd ℝ) (fun u v => a u v)
    (fun u u' v => by simp) (fun c u v => by simp) (fun u v v' => by simp)
    (fun c u v => by simp)) ‖a‖ (fun u v => by simpa using a.le_opNorm₂ u v)

@[simp] lemma toSesq_apply (a : X →L[ℝ] X →L[ℝ] ℝ) (u v : X) : toSesq a u v = a u v := rfl

lemma norm_innerSLFlip_le (x : X) : ‖innerSLFlip ℝ x‖ ≤ ‖x‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x) fun v => by
    rw [innerSLFlip_apply_apply, mul_comm]; exact norm_inner_le_norm v x

/-- Brezzi's theorem for a real bilinear form and a constraint. [QuennevilleBelair2015], Thm 4.11;
[Brezzi1974] -/
theorem brezzi_wellPosed_real [CompleteSpace X] [CompleteSpace Y] (a : X →L[ℝ] X →L[ℝ] ℝ)
    (Bs : X →L[ℝ] Y)
    (hZ : ∃ γ > 0, ∀ z ∈ Bs.ker, ∃ z' ∈ Bs.ker, ‖z'‖ ≤ 1 ∧ γ * ‖z‖ ≤ a z z')
    (hZd : ∀ z' ∈ Bs.ker, (∀ z ∈ Bs.ker, a z z' = 0) → z' = 0)
    (hb : ∃ β > 0, ∀ q, β * ‖q‖ ≤ ‖ContinuousLinearMap.adjoint Bs q‖) :
    (∀ F G, ∃! up : X × Y,
      (∀ v, a up.1 v + ⟪Bs v, up.2⟫ = ⟪F, v⟫) ∧ ∀ q, ⟪Bs up.1, q⟫ = ⟪G, q⟫) ∧
    ∃ C, ∀ (F : X) (G : Y) (u : X) (p : Y),
      (∀ v, a u v + ⟪Bs v, p⟫ = ⟪F, v⟫) → (∀ q, ⟪Bs u, q⟫ = ⟪G, q⟫) →
        ‖u‖ + ‖p‖ ≤ C * (‖F‖ + ‖G‖) := by
  obtain ⟨γ, hγ, hZ⟩ := hZ
  obtain ⟨β, hβ, hb⟩ := hb
  have hInf : Variational.InfSup (Variational.restrict (toSesq a) Bs.ker Bs.ker) γ :=
    Variational.InfSup.of_forall_exists_norm_le_one hγ fun z => by
      obtain ⟨z', hz', h1, h2⟩ := hZ z z.2
      refine ⟨⟨z', hz'⟩, h1, h2.trans ?_⟩
      simp only [Variational.restrict_apply, toSesq_apply, Real.norm_eq_abs]
      exact le_abs_self _
  have hSep : Variational.SeparatingRight (Variational.restrict (toSesq a) Bs.ker Bs.ker) :=
    fun y hy => Subtype.ext (hZd y y.2 fun z hz => hy ⟨z, hz⟩)
  have hiff : ∀ (F : X) (G : Y) (u : X) (p : Y),
      Variational.IsSaddleSolution (toSesq a) Bs (innerSLFlip ℝ F) (innerSLFlip ℝ G) u p ↔
        (∀ v, a u v + ⟪Bs v, p⟫ = ⟪F, v⟫) ∧ ∀ q, ⟪Bs u, q⟫ = ⟪G, q⟫ := by
    intro F G u p
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun v => ?_, fun q => ?_⟩
      · have := h1 v
        rwa [toSesq_apply, ContinuousLinearMap.adjoint_inner_right, innerSLFlip_apply_apply,
          real_inner_comm F v] at this
      · have := h2 q
        rwa [innerSLFlip_apply_apply, real_inner_comm (Bs u) q, real_inner_comm G q] at this
    · rintro ⟨h1, h2⟩
      refine ⟨fun v => ?_, fun q => ?_⟩
      · rw [toSesq_apply, ContinuousLinearMap.adjoint_inner_right, innerSLFlip_apply_apply,
          real_inner_comm F v]
        exact h1 v
      · rw [innerSLFlip_apply_apply, real_inner_comm (Bs u) q, real_inner_comm G q]
        exact h2 q
  refine ⟨fun F G => ?_, ?_⟩
  · obtain ⟨up, hup, huniq⟩ := Variational.existsUnique_isSaddleSolution hInf hSep hβ hb
      (innerSLFlip ℝ F) (innerSLFlip ℝ G)
    exact ⟨up, (hiff F G _ _).1 hup, fun up' h' => huniq up' ((hiff F G _ _).2 h')⟩
  · set A := ‖toSesq a‖
    set cu := γ⁻¹ + β⁻¹ * (1 + A / γ)
    refine ⟨cu + β⁻¹ * (1 + A * cu), fun F G u p h1 h2 => ?_⟩
    have hs := (hiff F G u p).2 ⟨h1, h2⟩
    have hu := hs.norm_fst_le hInf hβ hb
    have hp := hs.norm_snd_le hβ hb
    have hF := norm_innerSLFlip_le F
    have hG := norm_innerSLFlip_le G
    have hA : 0 ≤ A := norm_nonneg (toSesq a)
    have hcu : 0 ≤ cu := by positivity
    have hu' : ‖u‖ ≤ cu * (‖F‖ + ‖G‖) := by
      calc ‖u‖ ≤ γ⁻¹ * ‖innerSLFlip ℝ F‖ + β⁻¹ * (1 + A / γ) * ‖innerSLFlip ℝ G‖ := hu
        _ ≤ γ⁻¹ * ‖F‖ + β⁻¹ * (1 + A / γ) * ‖G‖ := by gcongr
        _ ≤ cu * (‖F‖ + ‖G‖) := by
          have := norm_nonneg F; have := norm_nonneg G
          have : 0 ≤ β⁻¹ * (1 + A / γ) := by positivity
          nlinarith [inv_nonneg.2 hγ.le]
    have hp' : ‖p‖ ≤ β⁻¹ * (1 + A * cu) * (‖F‖ + ‖G‖) := by
      calc ‖p‖ ≤ β⁻¹ * (‖innerSLFlip ℝ F‖ + A * ‖u‖) := hp
        _ ≤ β⁻¹ * (‖F‖ + A * (cu * (‖F‖ + ‖G‖))) := by gcongr
        _ ≤ β⁻¹ * (1 + A * cu) * (‖F‖ + ‖G‖) := by
          have := norm_nonneg F; have := norm_nonneg G
          have hβ' := inv_nonneg.2 hβ.le
          nlinarith [mul_nonneg hβ' (mul_nonneg hA hcu)]
    calc ‖u‖ + ‖p‖ ≤ cu * (‖F‖ + ‖G‖) + β⁻¹ * (1 + A * cu) * (‖F‖ + ‖G‖) := add_le_add hu' hp'
      _ = _ := by ring

end Brezzi

namespace Hilb

variable {W0 W1 Wt0 Wt1 W2 Wt2 V0 V1 Vt0 Vt1 : Type*}
    [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]
    [NormedAddCommGroup W1] [InnerProductSpace ℝ W1] [CompleteSpace W1]
    [NormedAddCommGroup Wt0] [InnerProductSpace ℝ Wt0] [CompleteSpace Wt0]
    [NormedAddCommGroup Wt1] [InnerProductSpace ℝ Wt1] [CompleteSpace Wt1]
    [NormedAddCommGroup W2] [InnerProductSpace ℝ W2] [CompleteSpace W2]
    [NormedAddCommGroup Wt2] [InnerProductSpace ℝ Wt2] [CompleteSpace Wt2]
    [NormedAddCommGroup V0] [InnerProductSpace ℝ V0] [CompleteSpace V0]
    [NormedAddCommGroup V1] [InnerProductSpace ℝ V1] [CompleteSpace V1]
    [NormedAddCommGroup Vt0] [InnerProductSpace ℝ Vt0] [CompleteSpace Vt0]
    [NormedAddCommGroup Vt1] [InnerProductSpace ℝ Vt1] [CompleteSpace Vt1]
    (D : Hilb ℝ W0 W1 Wt0 Wt1 W2 Wt2 V0 V1 Vt0 Vt1)

/-! ### The saddle point problem (5.3) -/

/-- The bilinear form `a` of (5.3). -/
def aForm : Xsp V0 Vt0 Vt1 →L[ℝ] Xsp V0 Vt0 Vt1 →L[ℝ] ℝ :=
  ip (D.ι0 ∘L pσ V0 Vt0 Vt1) (D.ι0 ∘L pσ V0 Vt0 Vt1)
    - ip (D.ιt1 ∘L pu V0 Vt0 Vt1) (D.ιt1 ∘L D.dt0 ∘L pφ V0 Vt0 Vt1)
    + ip (D.ιt1 ∘L D.dt0 ∘L pφ V0 Vt0 Vt1) (D.ιt1 ∘L pu V0 Vt0 Vt1)
    + ip (D.S1 ∘L pu V0 Vt0 Vt1) (D.S1 ∘L pu V0 Vt0 Vt1)
    + ip (D.dt1 ∘L pu V0 Vt0 Vt1) (D.dt1 ∘L pu V0 Vt0 Vt1)

lemma aForm_mkX (σ τ : V0) (φ ψ : Vt0) (u v : Vt1) :
    D.aForm (mkX σ φ u) (mkX τ ψ v) = ⟪D.ι0 σ, D.ι0 τ⟫ - ⟪D.ιt1 u, D.ιt1 (D.dt0 ψ)⟫ +
      ⟪D.ιt1 (D.dt0 φ), D.ιt1 v⟫ + ⟪D.S1 u, D.S1 v⟫ + ⟪D.dt1 u, D.dt1 v⟫ := rfl

lemma aForm_apply (x y : Xsp V0 Vt0 Vt1) : D.aForm x y =
    ⟪D.ι0 (pσ V0 Vt0 Vt1 x), D.ι0 (pσ V0 Vt0 Vt1 y)⟫ -
      ⟪D.ιt1 (pu V0 Vt0 Vt1 x), D.ιt1 (D.dt0 (pφ V0 Vt0 Vt1 y))⟫ +
      ⟪D.ιt1 (D.dt0 (pφ V0 Vt0 Vt1 x)), D.ιt1 (pu V0 Vt0 Vt1 y)⟫ +
      ⟪D.S1 (pu V0 Vt0 Vt1 x), D.S1 (pu V0 Vt0 Vt1 y)⟫ +
      ⟪D.dt1 (pu V0 Vt0 Vt1 x), D.dt1 (pu V0 Vt0 Vt1 y)⟫ := rfl

/-- `B(τ, ψ) = dτ - Sψ ∈ W¹`, so that `b(τ,ψ,v; λ) = -(λ, B(τ,ψ))`. -/
def Bop : Psp V0 Vt0 →L[ℝ] W1 :=
  D.ι1 ∘L (D.d0 ∘L WithLp.fstL 2 ℝ V0 Vt0 - D.S0 ∘L WithLp.sndL 2 ℝ V0 Vt0)

lemma Bop_apply (q : Psp V0 Vt0) : D.Bop q = D.ι1 (D.d0 q.fst - D.S0 q.snd) := rfl

lemma Bop_eq_zero_iff (q : Psp V0 Vt0) : D.Bop q = 0 ↔ (q.fst, q.snd) ∈ D.Γ := by
  rw [Bop_apply, D.mem_Γ, ← sub_eq_zero (a := D.d0 _)]
  constructor
  · intro h0; exact D.ι1_injective (by rw [h0, map_zero])
  · intro h0; rw [h0, map_zero]

local notation "adj" => ContinuousLinearMap.adjoint

/-- The multiplier space `W̌¹`, the closure of `R(B*)` in `V⁰ × Ṽ⁰`. -/
def Wcheck : Submodule ℝ (Psp V0 Vt0) := (adj D.Bop).range.topologicalClosure

instance : CompleteSpace D.Wcheck :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- `|||λ||| = ‖B*λ‖`, with the `ℓ²` norm on `V⁰ × Ṽ⁰`. -/
def tripleNorm (l : W1) : ℝ := ‖adj D.Bop l‖

theorem tripleNorm_spec (l : W1) :
    (∀ q, ⟪l, D.Bop q⟫ ≤ D.tripleNorm l * ‖q‖) ∧
      ∃ q, ‖q‖ ≤ 1 ∧ ⟪l, D.Bop q⟫ = D.tripleNorm l := by
  refine ⟨fun q => ?_, ?_⟩
  · rw [← ContinuousLinearMap.adjoint_inner_left, real_inner_comm, tripleNorm]
    exact (real_inner_le_norm _ _).trans (by rw [mul_comm])
  · rcases eq_or_ne (adj D.Bop l) 0 with h0 | h0
    · exact ⟨0, by simp, by simp [tripleNorm, h0]⟩
    · refine ⟨‖adj D.Bop l‖⁻¹ • adj D.Bop l, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)]
      · rw [← ContinuousLinearMap.adjoint_inner_left, inner_smul_right,
          real_inner_self_eq_norm_sq, tripleNorm]
        field_simp

theorem tripleNorm_definite
    (hdense : Dense ((LinearMap.range (D.ι1 ∘L D.d0 : V0 →ₗ[ℝ] W1) ⊔
      LinearMap.range (D.ι1 ∘L D.S0 : Vt0 →ₗ[ℝ] W1) : Submodule ℝ W1) : Set W1))
    {l : W1} (hl : D.tripleNorm l = 0) : l = 0 := by
  have h0 : adj D.Bop l = 0 := norm_eq_zero.1 hl
  refine hdense.eq_zero_of_mem_orthogonal ?_
  rw [Submodule.mem_orthogonal]
  intro k hk
  have hB : ∀ q, ⟪D.Bop q, l⟫ = 0 := fun q => by
    rw [← ContinuousLinearMap.adjoint_inner_right, h0, inner_zero_right]
  obtain ⟨a, ⟨τ, rfl⟩, b, ⟨ψ, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hk
  have h1 := hB (WithLp.toLp 2 (τ, 0))
  have h2 := hB (WithLp.toLp 2 (0, ψ))
  simp only [Bop_apply, WithLp.toLp_fst, WithLp.toLp_snd, map_zero, sub_zero, zero_sub,
    map_neg, inner_neg_left, neg_eq_zero] at h1 h2
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, inner_add_left]
  rw [h1, h2, add_zero]

/-- The map `W¹ → W̌¹`, `λ ↦ B*λ`. -/
def jW : W1 →L[ℝ] D.Wcheck :=
  (adj D.Bop).codRestrict D.Wcheck fun l =>
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ l)

/-- When `d⁰V⁰ + S₀Ṽ⁰` is dense in `W¹`, `jW` is an injective isometry for `|||·|||` with dense
range. -/
theorem jW_spec
    (hdense : Dense ((LinearMap.range (D.ι1 ∘L D.d0 : V0 →ₗ[ℝ] W1) ⊔
      LinearMap.range (D.ι1 ∘L D.S0 : Vt0 →ₗ[ℝ] W1) : Submodule ℝ W1) : Set W1)) :
    (∀ l, ‖D.jW l‖ = D.tripleNorm l) ∧ DenseRange D.jW ∧ Function.Injective D.jW := by
  refine ⟨fun l => rfl, ?_, ?_⟩
  · intro μ
    have hμ : (μ : Psp V0 Vt0) ∈ closure (Set.range (adj D.Bop)) := μ.2
    rw [mem_closure_iff_seq_limit] at hμ ⊢
    obtain ⟨q, hq, hlim⟩ := hμ
    choose l hl using hq
    refine ⟨fun n => D.jW (l n), fun n => ⟨l n, rfl⟩, ?_⟩
    rw [tendsto_subtype_rng]
    have : (fun n => ((D.jW (l n) : D.Wcheck) : Psp V0 Vt0)) = q := funext fun n => hl n
    rw [this]; exact hlim
  · refine (injective_iff_map_eq_zero _).2 fun l hl => D.tripleNorm_definite hdense ?_
    rw [tripleNorm, show adj D.Bop l = (D.jW l : Psp V0 Vt0) from rfl, hl]
    simp

/-- The constraint operator: `b(y, μ) = ⟪Bs y, μ⟫`. -/
def Bs : Xsp V0 Vt0 Vt1 →L[ℝ] D.Wcheck := -(D.Wcheck.orthogonalProjectionOnto ∘L pP V0 Vt0 Vt1)

/-- The bilinear form `b` of (5.3), extended to `μ ∈ W̌¹`. -/
def bForm (y : Xsp V0 Vt0 Vt1) (μ : D.Wcheck) : ℝ := -⟪pP V0 Vt0 Vt1 y, (μ : Psp V0 Vt0)⟫

lemma inner_Bs (y : Xsp V0 Vt0 Vt1) (μ : D.Wcheck) : ⟪D.Bs y, μ⟫ = D.bForm y μ := by
  simp [Bs, bForm, inner_neg_left]

lemma bForm_jW (y : Xsp V0 Vt0 Vt1) (l : W1) :
    D.bForm y (D.jW l) = -⟪l, D.ι1 (D.d0 (pσ V0 Vt0 Vt1 y) - D.S0 (pφ V0 Vt0 Vt1 y))⟫ := by
  rw [bForm, show ((D.jW l : D.Wcheck) : Psp V0 Vt0) = adj D.Bop l from rfl,
    ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
  rfl

lemma mem_orth_Wcheck_iff (q : Psp V0 Vt0) : q ∈ D.Wcheckᗮ ↔ (q.fst, q.snd) ∈ D.Γ := by
  rw [Wcheck, Submodule.orthogonal_closure, ← D.Bop_eq_zero_iff]
  have := ContinuousLinearMap.orthogonal_range (adj D.Bop)
  rw [ContinuousLinearMap.adjoint_adjoint] at this
  rw [this]
  rfl

lemma mem_ker_Bs (y : Xsp V0 Vt0 Vt1) :
    y ∈ D.Bs.ker ↔ (pσ V0 Vt0 Vt1 y, pφ V0 Vt0 Vt1 y) ∈ D.Γ := by
  show D.Bs y = 0 ↔ _
  rw [Bs, neg_apply, neg_eq_zero,
    ContinuousLinearMap.comp_apply, Submodule.orthogonalProjectionOnto_eq_zero_iff,
    mem_orth_Wcheck_iff]
  rfl

lemma mkX_mem_ker {σ : V0} {φ : Vt0} (u : Vt1) (h : (σ, φ) ∈ D.Γ) : mkX σ φ u ∈ D.Bs.ker :=
  (D.mem_ker_Bs _).2 h

theorem infSup_b : ∀ μ : D.Wcheck, 1 * ‖μ‖ ≤ ‖adj D.Bs μ‖ := by
  intro μ
  rw [one_mul]
  set x : Xsp V0 Vt0 Vt1 := WithLp.toLp 2 (-(μ : Psp V0 Vt0), 0)
  have hx : ‖x‖ = ‖μ‖ := by
    have h2 : ‖x‖ ^ 2 = ‖μ‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      simp [x]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2
  have hi : ⟪adj D.Bs μ, x⟫ = ‖μ‖ ^ 2 := by
    rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm, inner_Bs, bForm]
    simp [x, pP, inner_neg_left]
  have hle : ‖μ‖ ^ 2 ≤ ‖adj D.Bs μ‖ * ‖μ‖ := by
    rw [← hi, ← hx]; exact real_inner_le_norm _ _
  rcases (norm_nonneg μ).lt_or_eq with hpos | h0
  · nlinarith
  · rw [← h0]; exact norm_nonneg _

lemma norm_Z1 {e : Vt1} (he : e ∈ D.Z1) : ‖e‖ = ‖D.ιt1 e‖ := by
  have h1 := D.norm_sq_Vt1 e
  rw [(D.mem_Z1.1 he).2, norm_zero] at h1
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)

lemma inner_ιt1_of_orth {e w : Vt1} (he : e ∈ D.Z1) (hw : w ∈ D.Z1ᗮ) :
    ⟪D.ιt1 w, D.ιt1 e⟫ = 0 := by
  have h0 : ⟪w, e⟫ = 0 := Submodule.inner_left_of_mem_orthogonal he hw
  rwa [D.grapht1, (D.mem_Z1.1 he).2, inner_zero_right, add_zero] at h0

private lemma core_low {s r E P A B ε c : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hεc : ε * c ^ 2 = 1)
    (hr : r ≤ s * (c * E)) :
    ε / 2 * (E ^ 2 + P ^ 2 + A ^ 2 + B ^ 2) ≤ s ^ 2 - ε * r + ε * E ^ 2 + ε * P ^ 2 + A ^ 2 + B ^ 2 := by
  have h1 : ε * r ≤ ε * (s * (c * E)) := mul_le_mul_of_nonneg_left hr hε0
  have h3 : ε ^ 2 * c ^ 2 * E ^ 2 = ε * E ^ 2 := by
    rw [show ε ^ 2 * c ^ 2 * E ^ 2 = (ε * c ^ 2) * (ε * E ^ 2) by ring, hεc, one_mul]
  nlinarith [sq_nonneg (s - ε * c * E), mul_nonneg (sub_nonneg.2 hε1) (sq_nonneg A),
    mul_nonneg (sub_nonneg.2 hε1) (sq_nonneg B), mul_nonneg hε0 (sq_nonneg P),
    mul_nonneg hε0 (sq_nonneg E)]

private lemma core_prod {a b n M : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b) (hn : n ≤ a + b)
    (ha2 : a ^ 2 ≤ M) (hb2 : b ^ 2 ≤ M) : a * n ≤ 2 * M := by
  have := mul_le_mul_of_nonneg_left hn ha
  nlinarith [sq_nonneg (a - b)]

private lemma sq_add_le_two (a b : ℝ) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

private lemma sq3_eq_zero {a b c : ℝ} (h : a ^ 2 + b ^ 2 + c ^ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have ha : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have hb : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have hc : c ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  exact ⟨pow_eq_zero_iff two_ne_zero |>.1 ha, pow_eq_zero_iff two_ne_zero |>.1 hb,
    pow_eq_zero_iff two_ne_zero |>.1 hc⟩

theorem infSup_a (h : D.Hyps) :
    ∃ γ > 0, ∀ z ∈ D.Bs.ker, ∃ z' ∈ D.Bs.ker, ‖z'‖ ≤ 1 ∧ γ * ‖z‖ ≤ D.aForm z z' := by
  obtain ⟨C1, hC1, hP1⟩ := D.poincare_Γ h
  obtain ⟨C2, hC2, hP2⟩ := D.poincare_T h
  set c := max 1 (max C1 C2) with hc
  have hc1 : 1 ≤ c := le_max_left _ _
  have hcC1 : C1 ≤ c := (le_max_left _ _).trans (le_max_right _ _)
  have hcC2 : C2 ≤ c := (le_max_right _ _).trans (le_max_right _ _)
  have hcpos : 0 < c := by linarith
  have hc2 : 1 ≤ c ^ 2 := one_le_pow₀ hc1
  set ε := 1 / c ^ 2 with hε
  have hεc : ε * c ^ 2 = 1 := by rw [hε]; field_simp
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by rw [hε, div_le_one (by positivity)]; exact hc2
  refine ⟨ε / (8 * c ^ 2), by positivity, fun z hz => ?_⟩
  set σ := pσ V0 Vt0 Vt1 z with hσdef
  set φ := pφ V0 Vt0 Vt1 z with hφdef
  set u := pu V0 Vt0 Vt1 z with hudef
  have hΓ : (σ, φ) ∈ D.Γ := (D.mem_ker_Bs z).1 hz
  obtain ⟨xr, hxr, w, hw, hu⟩ := D.hodge_Vt1 h u
  set ρ := xr.1
  set χ := xr.2
  set p := D.dt0 φ with hpdef
  set e := D.dt0 χ with hedef
  have hpZ : p ∈ D.Z1 := D.dt0_mem_Z1 hΓ
  have heZ : e ∈ D.Z1 := D.dt0_mem_Z1 hxr
  obtain ⟨hS1p, hdt1p⟩ := D.mem_Z1.1 hpZ
  obtain ⟨hS1e, hdt1e⟩ := D.mem_Z1.1 heZ
  have hwp := D.inner_ιt1_of_orth hpZ hw
  have hwe := D.inner_ιt1_of_orth heZ hw
  have hew : ⟪e, w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal heZ hw
  -- the test function
  set y := mkX (σ - ε • ρ) (φ - ε • χ) (u + ε • p) with hydef
  have hy : y ∈ D.Bs.ker := D.mkX_mem_ker _ (D.Γ.sub_mem hΓ (D.Γ.smul_mem ε hxr))
  set s := ‖D.ι0 σ‖
  set E := ‖D.ιt1 e‖
  set P := ‖D.ιt1 p‖
  set A := ‖D.S1 w‖
  set B := ‖D.dt1 w‖
  have hval : D.aForm z y =
      s ^ 2 - ε * ⟪D.ι0 σ, D.ι0 ρ⟫ + ε * E ^ 2 + ε * P ^ 2 + A ^ 2 + B ^ 2 := by
    show D.aForm (mkX σ φ u) y = _
    rw [hydef, aForm_mkX, hu]
    simp only [map_add, map_sub, map_smul, ← hpdef, ← hedef, hS1p, hS1e, hdt1p, hdt1e,
      inner_add_left, inner_add_right, inner_sub_right, real_inner_smul_right,
      smul_zero, add_zero, zero_add, real_inner_self_eq_norm_sq,
      real_inner_comm (D.ιt1 w) (D.ιt1 p), hwp, hwe, real_inner_comm (D.ιt1 e) (D.ιt1 p)]
    ring
  -- Poincaré bounds
  obtain ⟨hρ, hχ⟩ := hP1 xr hxr
  obtain ⟨hσ, hφ⟩ := hP1 (σ, φ) hΓ
  have hρc : ‖ρ‖ ≤ c * E := hρ.trans (by gcongr)
  have hχc : ‖χ‖ ≤ c * E := hχ.trans (by gcongr)
  have hσc : ‖σ‖ ≤ c * P := hσ.trans (by gcongr)
  have hφc : ‖φ‖ ≤ c * P := hφ.trans (by gcongr)
  have hcs : ⟪D.ι0 σ, D.ι0 ρ⟫ ≤ s * (c * E) :=
    (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left ((D.norm_ι0_le ρ).trans hρc) (norm_nonneg _))
  set Q := E ^ 2 + P ^ 2 + A ^ 2 + B ^ 2 with hQ
  have hlow : ε / 2 * Q ≤ D.aForm z y := by
    rw [hval]; exact core_low hε0.le hε1 hεc hcs
  -- upper bounds
  have hpn : ‖p‖ = P := D.norm_Z1 hpZ
  have hen : ‖e‖ = E := D.norm_Z1 heZ
  have hun : ‖u‖ ^ 2 = E ^ 2 + ‖w‖ ^ 2 := by
    rw [hu, norm_add_sq_real, hew, hen]; ring
  have hwT : ‖D.T w‖ ≤ A + B := by
    rw [T_apply, Prod.norm_def]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  have hwn : ‖w‖ ≤ c * (A + B) := (hP2 w hw).trans (by gcongr)
  have sq_le {x y : ℝ} (hx : 0 ≤ x) (h : x ≤ c * y) : x ^ 2 ≤ c ^ 2 * y ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hx h 2
  have hw2 : ‖w‖ ^ 2 ≤ 2 * c ^ 2 * (A ^ 2 + B ^ 2) :=
    (sq_le (norm_nonneg _) hwn).trans (by nlinarith [sq_add_le_two A B, sq_nonneg c])
  have hz2 : ‖z‖ ^ 2 ≤ 2 * c ^ 2 * Q := by
    rw [norm_sq_X, ← hσdef, ← hφdef, ← hudef, hun, hQ]
    linarith [sq_le (norm_nonneg _) hσc, sq_le (norm_nonneg _) hφc,
      le_mul_of_one_le_left (sq_nonneg E) hc2, (by positivity : 0 ≤ c ^ 2 * E ^ 2),
      (by positivity : 0 ≤ c ^ 2 * (A ^ 2 + B ^ 2))]
  have hyz2 : ‖y - z‖ ^ 2 ≤ 2 * c ^ 2 * Q := by
    rw [norm_sq_X]
    have e1 : pσ V0 Vt0 Vt1 (y - z) = -(ε • ρ) := by
      rw [map_sub, hydef, pσ_mkX, ← hσdef]; abel
    have e2 : pφ V0 Vt0 Vt1 (y - z) = -(ε • χ) := by
      rw [map_sub, hydef, pφ_mkX, ← hφdef]; abel
    have e3 : pu V0 Vt0 Vt1 (y - z) = ε • p := by
      rw [map_sub, hydef, pu_mkX, ← hudef]; abel
    rw [e1, e2, e3, norm_neg, norm_neg, norm_smul, norm_smul, norm_smul,
      Real.norm_of_nonneg hε0.le, hpn]
    have hε2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε0.le hε1
    have hb : ‖ρ‖ ^ 2 + ‖χ‖ ^ 2 + P ^ 2 ≤ 2 * c ^ 2 * Q := by
      rw [hQ]
      linarith [sq_le (norm_nonneg _) hρc, sq_le (norm_nonneg _) hχc,
        le_mul_of_one_le_left (sq_nonneg P) hc2, (by positivity : 0 ≤ c ^ 2 * P ^ 2),
        (by positivity : 0 ≤ c ^ 2 * (A ^ 2 + B ^ 2))]
    have hnn : 0 ≤ ‖ρ‖ ^ 2 + ‖χ‖ ^ 2 + P ^ 2 := by positivity
    calc (ε * ‖ρ‖) ^ 2 + (ε * ‖χ‖) ^ 2 + (ε * P) ^ 2
        = ε ^ 2 * (‖ρ‖ ^ 2 + ‖χ‖ ^ 2 + P ^ 2) := by ring
      _ ≤ 1 * (‖ρ‖ ^ 2 + ‖χ‖ ^ 2 + P ^ 2) := by gcongr
      _ ≤ _ := by rw [one_mul]; exact hb
  have hyle : ‖y‖ ≤ ‖z‖ + ‖y - z‖ := by
    calc ‖y‖ = ‖z + (y - z)‖ := by rw [add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
  have hprod : ‖z‖ * ‖y‖ ≤ 2 * (2 * c ^ 2 * Q) :=
    core_prod (norm_nonneg _) (norm_nonneg _) hyle hz2 hyz2
  have hmain : ε / (8 * c ^ 2) * ‖z‖ * ‖y‖ ≤ D.aForm z y := by
    have e : ε / (8 * c ^ 2) * (2 * (2 * c ^ 2 * Q)) = ε / 2 * Q := by field_simp; ring
    calc ε / (8 * c ^ 2) * ‖z‖ * ‖y‖ = ε / (8 * c ^ 2) * (‖z‖ * ‖y‖) := by ring
      _ ≤ ε / (8 * c ^ 2) * (2 * (2 * c ^ 2 * Q)) := by gcongr
      _ = ε / 2 * Q := e
      _ ≤ _ := hlow
  rcases eq_or_ne y 0 with hy0 | hy0
  · refine ⟨0, Submodule.zero_mem _, by simp, ?_⟩
    rw [hy0, map_zero] at hlow
    have hQ0 : Q ≤ 0 := le_of_mul_le_mul_left (by simpa using hlow) (half_pos hε0)
    have hz0 : ‖z‖ = 0 := pow_eq_zero_iff two_ne_zero |>.1
      (le_antisymm (hz2.trans (mul_nonpos_of_nonneg_of_nonpos (by positivity) hQ0)) (sq_nonneg _))
    rw [hz0, mul_zero, map_zero]
  · have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
    refine ⟨‖y‖⁻¹ • y, Submodule.smul_mem _ _ hy, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hyn.ne']
    · rw [map_smul, smul_eq_mul, le_inv_mul_iff₀ hyn]
      calc ‖y‖ * (ε / (8 * c ^ 2) * ‖z‖) = ε / (8 * c ^ 2) * ‖z‖ * ‖y‖ := by ring
        _ ≤ _ := hmain

theorem nondeg_a (h : D.Hyps) :
    ∀ z' ∈ D.Bs.ker, (∀ z ∈ D.Bs.ker, D.aForm z z' = 0) → z' = 0 := by
  intro z' hz' hall
  set τ := pσ V0 Vt0 Vt1 z' with hτ
  set ψ := pφ V0 Vt0 Vt1 z' with hψ
  set v := pu V0 Vt0 Vt1 z' with hv
  have hΓ : (τ, ψ) ∈ D.Γ := (D.mem_ker_Bs z').1 hz'
  -- step 1: a(z', z') = ‖τ‖² + ‖S₁v‖² + ‖d̃v‖²
  have h1 := hall z' hz'
  rw [aForm_apply, ← hτ, ← hψ, ← hv, real_inner_comm (D.ιt1 (D.dt0 ψ)) (D.ιt1 v),
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h1
  obtain ⟨hι0τ, hS1v, hdt1v⟩ := sq3_eq_zero (a := ‖D.ι0 τ‖) (b := ‖D.S1 v‖) (c := ‖D.dt1 v‖)
    (by linarith)
  rw [norm_eq_zero] at hS1v hdt1v
  -- step 2: ψ = 0
  have h2 := hall (mkX 0 0 (D.dt0 ψ)) (D.mkX_mem_ker _ (by simp [D.mem_Γ]))
  rw [aForm_apply] at h2
  simp only [pσ_mkX, pφ_mkX, pu_mkX, map_zero, inner_zero_left, ← hψ, ← hv, hS1v,
    inner_zero_right, D.dt1_dt0, zero_sub, add_zero, real_inner_self_eq_norm_sq,
    neg_eq_zero] at h2
  have hψ0 : ψ = 0 := h.dt0_injective (D.ιt1_injective (by
    rw [map_zero, map_zero]; exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)))
  -- step 3: τ = 0
  have hd0τ : D.d0 τ = 0 := by rw [D.mem_Γ.1 hΓ]; simp [hψ0]
  have hτ0 : τ = 0 := by
    have := D.norm_sq_V0 τ
    rw [hι0τ, hd0τ, map_zero, norm_zero] at this
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (by linarith))
  -- step 4: v = 0
  obtain ⟨xr, hxr, hxv⟩ := (D.mem_Z1_iff h).1 (D.mem_Z1.2 ⟨hS1v, hdt1v⟩)
  have h3 := hall (mkX xr.1 xr.2 0) (D.mkX_mem_ker _ hxr)
  rw [aForm_apply] at h3
  simp only [pσ_mkX, pφ_mkX, pu_mkX, ← hτ, ← hψ, ← hv, hτ0, hψ0, hxv, map_zero,
    inner_zero_left, inner_zero_right, sub_zero, zero_add, add_zero,
    real_inner_self_eq_norm_sq] at h3
  have hv0 : v = 0 := D.ιt1_injective (by
    rw [map_zero]; exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3))
  rw [← mkX_eta z', ← hτ, ← hψ, ← hv, hτ0, hψ0, hv0]
  rfl

/-- The saddle point problem with forms `a`, `b` on `X × W̌¹` is well posed.
[QuennevilleBelair2015], Prop 5.2 (adapted) -/
theorem saddle_wellPosed (h : D.Hyps) :
    (∀ (F : Xsp V0 Vt0 Vt1) (G : D.Wcheck), ∃! xl : Xsp V0 Vt0 Vt1 × D.Wcheck,
      (∀ y, D.aForm xl.1 y + D.bForm y xl.2 = ⟪F, y⟫) ∧ ∀ μ, D.bForm xl.1 μ = ⟪G, μ⟫) ∧
    ∃ C, ∀ (F : Xsp V0 Vt0 Vt1) (G : D.Wcheck) (x : Xsp V0 Vt0 Vt1) (l : D.Wcheck),
      (∀ y, D.aForm x y + D.bForm y l = ⟪F, y⟫) → (∀ μ, D.bForm x μ = ⟪G, μ⟫) →
        ‖x‖ + ‖l‖ ≤ C * (‖F‖ + ‖G‖) := by
  have hb : ∃ β > 0, ∀ q, β * ‖q‖ ≤ ‖adj D.Bs q‖ := ⟨1, one_pos, D.infSup_b⟩
  obtain ⟨hex, C, hC⟩ :=
    brezzi_wellPosed_real D.aForm D.Bs (D.infSup_a h) (D.nondeg_a h) hb
  simp only [inner_Bs] at hex hC
  exact ⟨hex, C, hC⟩

/-- The system (5.3) with right-hand side `f ∈ W̃¹` and multiplier `λ ∈ W̌¹`. -/
def IsSaddle (f : Wt1) (x : Xsp V0 Vt0 Vt1) (l : D.Wcheck) : Prop :=
  (∀ y, D.aForm x y + D.bForm y l = ⟪f, D.ιt1 (pu V0 Vt0 Vt1 y)⟫) ∧ ∀ μ, D.bForm x μ = 0

/-- (5.3) has a unique solution for every `f ∈ W̃¹`, with `‖(σ,φ,u)‖_V + |||λ||| ≤ C ‖f‖`.
[QuennevilleBelair2015], Prop 5.2 (adapted) -/
theorem existsUnique_isSaddle (h : D.Hyps) :
    (∀ f : Wt1, ∃! xl : Xsp V0 Vt0 Vt1 × D.Wcheck, D.IsSaddle f xl.1 xl.2) ∧
    ∃ C, ∀ (f : Wt1) (x : Xsp V0 Vt0 Vt1) (l : D.Wcheck), D.IsSaddle f x l →
      ‖x‖ + ‖l‖ ≤ C * ‖f‖ := by
  obtain ⟨hex, C, hC⟩ := D.saddle_wellPosed h
  set R := D.ιt1 ∘L pu V0 Vt0 Vt1
  have hF : ∀ (f : Wt1) y, ⟪adj R f, y⟫ = ⟪f, D.ιt1 (pu V0 Vt0 Vt1 y)⟫ := fun f y => by
    rw [ContinuousLinearMap.adjoint_inner_left]; rfl
  have hiff : ∀ f x l, D.IsSaddle f x l ↔
      ((∀ y, D.aForm x y + D.bForm y l = ⟪adj R f, y⟫) ∧ ∀ μ, D.bForm x μ = ⟪(0 : D.Wcheck), μ⟫) := by
    intro f x l
    simp only [IsSaddle, hF, inner_zero_left]
  refine ⟨fun f => ?_, max C 0 * ‖R‖, fun f x l hs => ?_⟩
  · obtain ⟨xl, hxl, hu⟩ := hex (adj R f) 0
    exact ⟨xl, (hiff _ _ _).2 hxl, fun xl' h' => hu xl' ((hiff _ _ _).1 h')⟩
  · have := (hiff f x l).1 hs
    have hb := hC _ _ x l this.1 this.2
    have hR : ‖adj R f‖ ≤ ‖R‖ * ‖f‖ := by
      have : ‖adj R‖ = ‖R‖ := LinearIsometryEquiv.norm_map _ _
      rw [← this]; exact (adj R).le_opNorm f
    calc ‖x‖ + ‖l‖ ≤ C * (‖adj R f‖ + ‖(0 : D.Wcheck)‖) := hb
      _ = C * ‖adj R f‖ := by rw [norm_zero, add_zero]
      _ ≤ max C 0 * ‖adj R f‖ := by gcongr; exact le_max_left _ _
      _ ≤ max C 0 * (‖R‖ * ‖f‖) := by gcongr
      _ = _ := by ring

/-- The reduced Hodge Laplacian (5.2). -/
def IsReduced (f : Wt1) (x : Xsp V0 Vt0 Vt1) : Prop :=
  (pσ V0 Vt0 Vt1 x, pφ V0 Vt0 Vt1 x) ∈ D.Γ ∧
  (∀ τ ψ, (τ, ψ) ∈ D.Γ →
    ⟪D.ι0 (pσ V0 Vt0 Vt1 x), D.ι0 τ⟫ - ⟪D.ιt1 (pu V0 Vt0 Vt1 x), D.ιt1 (D.dt0 ψ)⟫ = 0) ∧
  ∀ v, ⟪D.ιt1 (D.dt0 (pφ V0 Vt0 Vt1 x)), D.ιt1 v⟫ + ⟪D.S1 (pu V0 Vt0 Vt1 x), D.S1 v⟫ +
    ⟪D.dt1 (pu V0 Vt0 Vt1 x), D.dt1 v⟫ = ⟪f, D.ιt1 v⟫

lemma aForm_split (x : Xsp V0 Vt0 Vt1) (τ : V0) (ψ : Vt0) (v : Vt1) :
    D.aForm x (mkX τ ψ v) =
      (⟪D.ι0 (pσ V0 Vt0 Vt1 x), D.ι0 τ⟫ - ⟪D.ιt1 (pu V0 Vt0 Vt1 x), D.ιt1 (D.dt0 ψ)⟫) +
      (⟪D.ιt1 (D.dt0 (pφ V0 Vt0 Vt1 x)), D.ιt1 v⟫ + ⟪D.S1 (pu V0 Vt0 Vt1 x), D.S1 v⟫ +
        ⟪D.dt1 (pu V0 Vt0 Vt1 x), D.dt1 v⟫) := by
  rw [aForm_apply]; simp only [pσ_mkX, pφ_mkX, pu_mkX]; ring

lemma bForm_mkX_of_mem {τ : V0} {ψ : Vt0} (v : Vt1) (hΓ : (τ, ψ) ∈ D.Γ) (μ : D.Wcheck) :
    D.bForm (mkX τ ψ v) μ = 0 := by
  have : pP V0 Vt0 Vt1 (mkX τ ψ v) ∈ D.Wcheckᗮ := (D.mem_orth_Wcheck_iff _).2 hΓ
  rw [bForm, Submodule.inner_left_of_mem_orthogonal μ.2 this, neg_zero]

lemma forall_bForm_eq_zero_iff (x : Xsp V0 Vt0 Vt1) :
    (∀ μ, D.bForm x μ = 0) ↔ (pσ V0 Vt0 Vt1 x, pφ V0 Vt0 Vt1 x) ∈ D.Γ := by
  rw [← D.mem_ker_Bs]
  show _ ↔ D.Bs x = 0
  constructor
  · intro hb
    exact ext_inner_right ℝ fun μ => by rw [inner_Bs, hb, inner_zero_left]
  · intro hb μ
    rw [← inner_Bs, hb, inner_zero_left]

theorem isReduced_of_isSaddle {f : Wt1} {x : Xsp V0 Vt0 Vt1} {l : D.Wcheck}
    (hs : D.IsSaddle f x l) : D.IsReduced f x := by
  have hΓ := (D.forall_bForm_eq_zero_iff x).1 hs.2
  refine ⟨hΓ, fun τ ψ hτψ => ?_, fun v => ?_⟩
  · have e := hs.1 (mkX τ ψ 0)
    rw [D.bForm_mkX_of_mem 0 hτψ, D.aForm_split] at e
    simpa using e
  · have e := hs.1 (mkX 0 0 v)
    rw [D.bForm_mkX_of_mem v (by simp [D.mem_Γ]), D.aForm_split] at e
    simpa using e

/-- The reduced Hodge Laplacian (5.2) has exactly one solution for every `f ∈ W̃¹`. -/
theorem existsUnique_isReduced (h : D.Hyps) (f : Wt1) : ∃! x, D.IsReduced f x := by
  obtain ⟨⟨xl, hxl, -⟩, -⟩ := (D.existsUnique_isSaddle h).1 f, ()
  refine ⟨xl.1, D.isReduced_of_isSaddle hxl, fun x' hx' => ?_⟩
  obtain ⟨γ, hγ, hZ⟩ := D.infSup_a h
  have hval : ∀ x : Xsp V0 Vt0 Vt1, D.IsReduced f x → ∀ z ∈ D.Bs.ker,
      D.aForm x z = ⟪f, D.ιt1 (pu V0 Vt0 Vt1 z)⟫ := by
    intro x hx z hz
    rw [← mkX_eta z, D.aForm_split, hx.2.1 _ _ ((D.mem_ker_Bs z).1 hz), hx.2.2, zero_add]
    rfl
  have hd : x' - xl.1 ∈ D.Bs.ker := (D.mem_ker_Bs _).2 (by
    have := D.Γ.sub_mem hx'.1 (D.isReduced_of_isSaddle hxl).1
    simpa using this)
  obtain ⟨z', hz', -, hle⟩ := hZ _ hd
  have h0 : D.aForm (x' - xl.1) z' = 0 := by
    rw [map_sub, sub_apply, hval x' hx' z' hz',
      hval xl.1 (D.isReduced_of_isSaddle hxl) z' hz', sub_self]
  rw [h0] at hle
  have : ‖x' - xl.1‖ = 0 :=
    le_antisymm (by nlinarith [norm_nonneg (x' - xl.1)]) (norm_nonneg _)
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

theorem existsUnique_multiplier (h : D.Hyps) {f : Wt1} {x : Xsp V0 Vt0 Vt1}
    (hx : D.IsReduced f x) : ∃! l : D.Wcheck, D.IsSaddle f x l := by
  obtain ⟨xl, hxl, huniq⟩ := (D.existsUnique_isSaddle h).1 f
  have hx' : xl.1 = x :=
    (D.existsUnique_isReduced h f).unique (D.isReduced_of_isSaddle hxl) hx
  refine ⟨xl.2, hx' ▸ hxl, fun l hl => ?_⟩
  have := huniq (x, l) hl
  rw [← this]

/-- `(x, λ)` solves (5.3) iff `x` solves (5.2) and `b(y, λ) = (f, v) - a(x, y)` for all `y`. -/
theorem isSaddle_iff_isReduced (f : Wt1) (x : Xsp V0 Vt0 Vt1) (l : D.Wcheck) :
    D.IsSaddle f x l ↔ D.IsReduced f x ∧
      ∀ y, D.bForm y l = ⟪f, D.ιt1 (pu V0 Vt0 Vt1 y)⟫ - D.aForm x y := by
  constructor
  · intro hs
    exact ⟨D.isReduced_of_isSaddle hs, fun y => by rw [← hs.1 y]; ring⟩
  · rintro ⟨hr, hm⟩
    exact ⟨fun y => by rw [hm y]; ring, (D.forall_bForm_eq_zero_iff x).2 hr.1⟩

/-- The system (5.3) with `λ, μ ∈ W¹`. -/
def IsSaddleW1 (f : Wt1) (x : Xsp V0 Vt0 Vt1) (l : W1) : Prop :=
  (∀ y, D.aForm x y - ⟪l, D.ι1 (D.d0 (pσ V0 Vt0 Vt1 y) - D.S0 (pφ V0 Vt0 Vt1 y))⟫ =
    ⟪f, D.ιt1 (pu V0 Vt0 Vt1 y)⟫) ∧
  ∀ μ : W1, ⟪D.ι1 (D.d0 (pσ V0 Vt0 Vt1 x) - D.S0 (pφ V0 Vt0 Vt1 x)), μ⟫ = 0

end Hilb

end Feec.BGG
