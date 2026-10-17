module

public import Feec.Variational.BabuskaNecas

/-!
# Saddle point problems: Brezzi's theorem over `ℝ` and `ℂ`

Let `X`, `Y` be Hilbert spaces over `𝕜`, `a : X →L[𝕜] X →L⋆[𝕜] 𝕜` a bounded sesquilinear form
and `B : X →L[𝕜] Y` bounded (the constraint `b(v, q) = ⟪q, B v⟫`). The saddle point problem is:
given antilinear `F`, `G`, find `(u, p) ∈ X × Y` with

  `a u v + ⟪v, B† p⟫ = F v` for all `v`,   `⟪q, B u⟫ = G q` for all `q`

(`IsSaddleSolution`). With `Z = ker B`:

## Main results

* `existsUnique_isSaddleSolution` (Brezzi): if `a` restricted to `Z × Z` has the inf-sup property
  and separates, and `β ‖q‖ ≤ ‖B† q‖` (the inf-sup condition of `b` with the inf over `q`), the
  problem is uniquely solvable;
* `IsSaddleSolution.norm_fst_le`, `IsSaddleSolution.norm_snd_le`: the stability bounds
  `‖u‖ ≤ γ⁻¹ ‖F‖ + β⁻¹ (1 + ‖a‖/γ) ‖G‖` and `‖p‖ ≤ β⁻¹ (‖F‖ + ‖a‖ ‖u‖)`;
* `brezzi_iff`: the converse, so Brezzi's conditions are *equivalent* to well-posedness;
* `exists_lift`, `exists_adjoint_eq_of_mem_orthogonal`: `B` is onto with a bounded right inverse
  and `(ker B)ᗮ = R(B†)` under the inf-sup condition of `b`;
* `rieszOp`-translation lemmas for constraint forms `b : X →L[𝕜] Y →L⋆[𝕜] 𝕜`
  (`mem_ker_rieszOp_iff`, `norm_adjoint_rieszOp_apply`, `isSaddleSolution_rieszOp_iff`).

## References

* [V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of General Relativity*][QuennevilleBelair2015],
  Thm 4.11 (Brezzi, corrected: the inf-sup of `b` is over `q`)
* [F. Brezzi, *On the existence, uniqueness and approximation of saddle-point problems arising from Lagrangian multipliers*][Brezzi1974]
* [D. Boffi, F. Brezzi, M. Fortin, *Mixed Finite Element Methods and Applications*][BoffiBrezziFortin2013],
  Ch. 4
* [D. N. Arnold, *Finite Element Exterior Calculus*][Arnold2018], Ch. 4
-/

open ContinuousLinearMap (adjoint)

@[expose] public noncomputable section

namespace Feec.Variational

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [CompleteSpace Y]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- `(u, p)` solves the saddle point problem `a u v + ⟪v, B† p⟫ = F v`, `⟪q, B u⟫ = G q`.
[QuennevilleBelair2015], Thm 4.11 -/
structure IsSaddleSolution (a : X →L[𝕜] X →L⋆[𝕜] 𝕜) (B : X →L[𝕜] Y) (F : X →L⋆[𝕜] 𝕜)
    (G : Y →L⋆[𝕜] 𝕜) (u : X) (p : Y) : Prop where
  fst : ∀ v, a u v + ⟪v, adjoint B p⟫ = F v
  snd : ∀ q, ⟪q, B u⟫ = G q

variable {a : X →L[𝕜] X →L⋆[𝕜] 𝕜} {B : X →L[𝕜] Y} {F : X →L⋆[𝕜] 𝕜} {G : Y →L⋆[𝕜] 𝕜}
  {γ β : ℝ}

/-! ### The constraint operator -/

/-- `⟪z, B† p⟫ = 0` on `ker B`. -/
theorem inner_adjoint_eq_zero_of_mem_ker {z : X} (hz : z ∈ B.ker) (p : Y) :
    ⟪z, adjoint B p⟫ = 0 := by
  rw [ContinuousLinearMap.adjoint_inner_right, show B z = 0 from hz, inner_zero_left]

/-- **Lifting.** If `β ‖q‖ ≤ ‖B† q‖`, every antilinear `G` on `Y` is `q ↦ ⟪q, B u_G⟫` with
`u_G = B† w ∈ R(B†)` and `β ‖u_G‖ ≤ ‖G‖`. [QuennevilleBelair2015], Thm 4.11 -/
theorem exists_lift (hβ : 0 < β) (hb : ∀ q, β * ‖q‖ ≤ ‖adjoint B q‖) (G : Y →L⋆[𝕜] 𝕜) :
    ∃ w : Y, (∀ q, ⟪q, B (adjoint B w)⟫ = G q) ∧ β * ‖adjoint B w‖ ≤ ‖G‖ := by
  set c : Y →L[𝕜] Y →L⋆[𝕜] 𝕜 := (innerSLFlip 𝕜).comp (B.comp (adjoint B))
  have hc : ∀ w q, c w q = ⟪q, B (adjoint B w)⟫ := fun _ _ => rfl
  have hre : ∀ q, RCLike.re (c q q) = ‖adjoint B q‖ ^ 2 := fun q => by
    rw [hc, ← ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq]
  have hcoer : ∀ q, β ^ 2 * ‖q‖ ^ 2 ≤ RCLike.re (c q q) := fun q => by
    rw [hre]; have := hb q; have : 0 ≤ β * ‖q‖ := by positivity
    nlinarith
  obtain ⟨w, hw, -⟩ := existsUnique_of_coercive (by positivity) hcoer G
  refine ⟨w, fun q => by rw [← hc, hw], ?_⟩
  have h1 : ‖adjoint B w‖ ^ 2 ≤ ‖G‖ * ‖w‖ := by
    rw [← hre, show c w w = G w by rw [hw]]
    exact (RCLike.re_le_norm _).trans (G.le_opNorm w)
  rcases (norm_nonneg (adjoint B w)).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact norm_nonneg _
  · have h2 := hb w
    have : β * ‖adjoint B w‖ * ‖adjoint B w‖ ≤ ‖G‖ * ‖adjoint B w‖ := by
      nlinarith [norm_nonneg G]
    exact le_of_mul_le_mul_right this hpos

/-- Under the inf-sup condition of `b`, `(ker B)ᗮ ⊆ R(B†)`. -/
theorem exists_adjoint_eq_of_mem_orthogonal (hβ : 0 < β)
    (hb : ∀ q, β * ‖q‖ ≤ ‖adjoint B q‖) {g : X} (hg : g ∈ B.kerᗮ) : ∃ p, adjoint B p = g := by
  obtain ⟨w, hw, -⟩ := exists_lift hβ hb (innerSLFlip 𝕜 (B g))
  refine ⟨w, ?_⟩
  have h1 : adjoint B w - g ∈ B.ker := by
    show B (adjoint B w - g) = 0
    refine ext_inner_left 𝕜 fun q => ?_
    rw [map_sub, inner_sub_right, hw, innerSLFlip_apply_apply, sub_self, inner_zero_right]
  have h2 : adjoint B w - g ∈ B.kerᗮ := by
    refine B.kerᗮ.sub_mem ?_ hg
    rw [Submodule.mem_orthogonal]
    intro z hz
    exact inner_adjoint_eq_zero_of_mem_ker hz w
  have : adjoint B w - g ∈ B.ker ⊓ B.kerᗮ := ⟨h1, h2⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at this
  exact sub_eq_zero.1 this

/-! ### Brezzi's theorem -/

omit [CompleteSpace X] in
/-- The residual `F - a u` of an approximate first equation. -/
private theorem norm_residual_le (F : X →L⋆[𝕜] 𝕜) (u : X) :
    ‖F - a u‖ ≤ ‖F‖ + ‖a‖ * ‖u‖ :=
  (norm_sub_le _ _).trans (by gcongr; exact a.le_opNorm u)

/-- **Brezzi**, uniqueness: the inf-sup condition of `a` on `ker B` and of `b` force uniqueness.
[QuennevilleBelair2015], Thm 4.11 -/
theorem IsSaddleSolution.unique (hZ : InfSup (restrict a B.ker B.ker) γ)
    (hβ : 0 < β) (hb : ∀ q, β * ‖q‖ ≤ ‖adjoint B q‖) {u u' : X} {p p' : Y}
    (h : IsSaddleSolution a B F G u p) (h' : IsSaddleSolution a B F G u' p') :
    u = u' ∧ p = p' := by
  have hz : u - u' ∈ B.ker := by
    show B (u - u') = 0
    refine ext_inner_left 𝕜 fun q => ?_
    rw [map_sub, inner_sub_right, h.snd, h'.snd, sub_self, inner_zero_right]
  have hu : u = u' := by
    refine sub_eq_zero.1 (congrArg Subtype.val (hZ.eq_zero_of_apply_eq_zero
      (x := ⟨u - u', hz⟩) (ContinuousLinearMap.ext fun z => ?_)))
    have e1 := h.fst z
    have e2 := h'.fst z
    rw [inner_adjoint_eq_zero_of_mem_ker z.2, add_zero] at e1 e2
    rw [restrict_apply, map_sub, sub_apply, e1, e2, sub_self]; rfl
  subst hu
  refine ⟨rfl, ?_⟩
  have hv : adjoint B (p - p') = 0 := by
    refine ext_inner_left 𝕜 fun v => ?_
    have e1 := h.fst v
    have e2 := h'.fst v
    rw [map_sub, inner_sub_right, inner_zero_right]
    linear_combination e1 - e2
  have := hb (p - p')
  rw [hv, norm_zero] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 (by nlinarith [norm_nonneg (p - p')]))

/-- **Brezzi's theorem** (Thm 4.11, corrected): if `a` restricted to `Z = ker B` has the inf-sup
property and separates, and `β ‖q‖ ≤ ‖B† q‖`, the saddle point problem has a unique solution for
all antilinear `F`, `G`. The thesis' inf-sup condition on `b` (inf over the first argument) is
unsatisfiable when `Z ≠ 0`; the inf is over `q`. [QuennevilleBelair2015], Thm 4.11 (corrected) -/
theorem existsUnique_isSaddleSolution (hZ : InfSup (restrict a B.ker B.ker) γ)
    (hZs : SeparatingRight (restrict a B.ker B.ker)) (hβ : 0 < β)
    (hb : ∀ q, β * ‖q‖ ≤ ‖adjoint B q‖) (F : X →L⋆[𝕜] 𝕜) (G : Y →L⋆[𝕜] 𝕜) :
    ∃! up : X × Y, IsSaddleSolution a B F G up.1 up.2 := by
  set Z := B.ker
  have : CompleteSpace Z := B.isClosed_ker.completeSpace_coe
  obtain ⟨w, hw, -⟩ := exists_lift hβ hb G
  set uG := adjoint B w
  obtain ⟨z, hz, -⟩ := existsUnique_apply_eq hZ hZs ((F - a uG).comp Z.subtypeL)
  set u := uG + (z : X)
  have hBu : ∀ q, ⟪q, B u⟫ = G q := fun q => by
    rw [map_add, show B z = 0 from z.2, add_zero, hw]
  obtain ⟨g, hg⟩ := innerSLFlip_surjective (F - a u)
  have hgZ : g ∈ Zᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z' hz'
    have e := congrArg (fun f => f ⟨z', hz'⟩) hz
    simp only [restrict_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      sub_apply] at e
    have : (F - a u) z' = 0 := by
      rw [sub_apply, map_add, add_apply, e]; ring
    rw [← hg, innerSLFlip_apply_apply] at this
    exact this
  obtain ⟨p, hp⟩ := exists_adjoint_eq_of_mem_orthogonal hβ hb hgZ
  have hsol : IsSaddleSolution a B F G u p := ⟨fun v => by
    rw [hp]
    have := congrArg (fun f => f v) hg
    simp only [innerSLFlip_apply_apply, sub_apply] at this
    rw [this]; ring, hBu⟩
  refine ⟨(u, p), hsol, fun up hup => ?_⟩
  obtain ⟨e1, e2⟩ := IsSaddleSolution.unique hZ hβ hb hup hsol
  exact Prod.ext e1 e2

/-- **Brezzi**, stability of `u`: `‖u‖ ≤ γ⁻¹ ‖F‖ + β⁻¹ (1 + ‖a‖/γ) ‖G‖`. [QuennevilleBelair2015], Thm 4.11 -/
theorem IsSaddleSolution.norm_fst_le (hZ : InfSup (restrict a B.ker B.ker) γ) (hβ : 0 < β)
    (hb : ∀ q, β * ‖q‖ ≤ ‖adjoint B q‖) {u : X} {p : Y} (h : IsSaddleSolution a B F G u p) :
    ‖u‖ ≤ γ⁻¹ * ‖F‖ + β⁻¹ * (1 + ‖a‖ / γ) * ‖G‖ := by
  obtain ⟨w, hw, hβw⟩ := exists_lift hβ hb G
  set uG := adjoint B w
  have hz : u - uG ∈ B.ker := by
    show B (u - uG) = 0
    refine ext_inner_left 𝕜 fun q => ?_
    rw [map_sub, inner_sub_right, h.snd, hw, sub_self, inner_zero_right]
  have hres : restrict a B.ker B.ker ⟨u - uG, hz⟩ = (F - a uG).comp B.ker.subtypeL :=
    ContinuousLinearMap.ext fun z => by
      have e := h.fst z
      rw [inner_adjoint_eq_zero_of_mem_ker z.2, add_zero] at e
      simp [e]
  have h1 : ‖u - uG‖ ≤ γ⁻¹ * (‖F‖ + ‖a‖ * ‖uG‖) := by
    have := hZ.norm_le_of_apply_eq hres
    refine this.trans (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hZ.pos.le))
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc ‖F - a uG‖ * ‖B.ker.subtypeL‖ ≤ ‖F - a uG‖ * 1 := by
          gcongr; exact Submodule.norm_subtypeL_le _
      _ ≤ _ := by rw [mul_one]; exact norm_residual_le F uG
  have huG : ‖uG‖ ≤ β⁻¹ * ‖G‖ := by rw [le_inv_mul_iff₀ hβ]; exact hβw
  have hγ := hZ.pos
  calc ‖u‖ = ‖uG + (u - uG)‖ := by congr 1; abel
    _ ≤ ‖uG‖ + ‖u - uG‖ := norm_add_le _ _
    _ ≤ ‖uG‖ + γ⁻¹ * (‖F‖ + ‖a‖ * ‖uG‖) := by gcongr
    _ = γ⁻¹ * ‖F‖ + (1 + ‖a‖ / γ) * ‖uG‖ := by field_simp; ring
    _ ≤ γ⁻¹ * ‖F‖ + (1 + ‖a‖ / γ) * (β⁻¹ * ‖G‖) := by gcongr
    _ = _ := by ring

/-- **Brezzi**, stability of `p`: `‖p‖ ≤ β⁻¹ (‖F‖ + ‖a‖ ‖u‖)`. [QuennevilleBelair2015], Thm 4.11 -/
theorem IsSaddleSolution.norm_snd_le (hβ : 0 < β) (hb : ∀ q, β * ‖q‖ ≤ ‖adjoint B q‖) {u : X}
    {p : Y} (h : IsSaddleSolution a B F G u p) : ‖p‖ ≤ β⁻¹ * (‖F‖ + ‖a‖ * ‖u‖) := by
  set t := adjoint B p
  have e : ⟪t, t⟫ = (F - a u) t := by
    have := h.fst t
    rw [sub_apply]; linear_combination this
  have ht : ‖t‖ ≤ ‖F‖ + ‖a‖ * ‖u‖ := by
    rcases (norm_nonneg t).eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · refine le_of_mul_le_mul_right ?_ hpos
      calc ‖t‖ * ‖t‖ = ‖⟪t, t⟫‖ := by
            rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm, sq]
        _ = ‖(F - a u) t‖ := by rw [e]
        _ ≤ ‖F - a u‖ * ‖t‖ := (F - a u).le_opNorm t
        _ ≤ (‖F‖ + ‖a‖ * ‖u‖) * ‖t‖ := by gcongr; exact norm_residual_le F u
  rw [le_inv_mul_iff₀ hβ]
  exact (hb p).trans ht

/-- **Brezzi, equivalence**: the saddle point problem is uniquely solvable for all antilinear
`F`, `G` iff `a` has the inf-sup property and separates on `Z = ker B` and `b` has the inf-sup
property (inf over `q`). [QuennevilleBelair2015], Thm 4.11 (corrected) -/
theorem brezzi_iff :
    ((∃ γ, InfSup (restrict a B.ker B.ker) γ) ∧ SeparatingRight (restrict a B.ker B.ker) ∧
      ∃ β, 0 < β ∧ ∀ q, β * ‖q‖ ≤ ‖adjoint B q‖) ↔
    ∀ (F : X →L⋆[𝕜] 𝕜) (G : Y →L⋆[𝕜] 𝕜), ∃! up : X × Y, IsSaddleSolution a B F G up.1 up.2 := by
  constructor
  · rintro ⟨⟨γ, hZ⟩, hZs, β, hβ, hb⟩ F G
    exact existsUnique_isSaddleSolution hZ hZs hβ hb F G
  intro H
  set Z := B.ker
  have : CompleteSpace Z := B.isClosed_ker.completeSpace_coe
  -- `B` is onto
  have hsurj : Function.Surjective B := fun y => by
    obtain ⟨⟨u, p⟩, h, -⟩ := H 0 (innerSLFlip 𝕜 y)
    exact ⟨u, ext_inner_left 𝕜 fun q => by rw [h.snd, innerSLFlip_apply_apply]⟩
  -- inf-sup of `b`
  obtain ⟨C, hC, hpre⟩ := B.exists_preimage_norm_le hsurj
  have hb : ∀ q, C⁻¹ * ‖q‖ ≤ ‖adjoint B q‖ := fun q => by
    obtain ⟨x, hx, hxn⟩ := hpre q
    rw [inv_mul_le_iff₀ hC]
    rcases (norm_nonneg q).eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    refine le_of_mul_le_mul_right ?_ hpos
    calc ‖q‖ * ‖q‖ = ‖⟪adjoint B q, x⟫‖ := by
          rw [ContinuousLinearMap.adjoint_inner_left, hx, inner_self_eq_norm_sq_to_K, norm_pow,
            RCLike.norm_ofReal, abs_norm, sq]
      _ ≤ ‖adjoint B q‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ ‖adjoint B q‖ * (C * ‖q‖) := by gcongr
      _ = C * ‖adjoint B q‖ * ‖q‖ := by ring
  have hβ : 0 < C⁻¹ := inv_pos.2 hC
  -- `a` is bijective on `Z`
  have hZsurj : Function.Surjective (restrict a Z Z) := fun ℓ => by
    obtain ⟨⟨u, p⟩, h, -⟩ := H (ℓ.comp Z.orthogonalProjectionOnto) 0
    have hu : u ∈ Z := by
      show B u = 0
      exact ext_inner_left 𝕜 fun q => by rw [h.snd, inner_zero_right]; rfl
    refine ⟨⟨u, hu⟩, ContinuousLinearMap.ext fun z => ?_⟩
    have e := h.fst z
    rw [inner_adjoint_eq_zero_of_mem_ker z.2, add_zero, ContinuousLinearMap.comp_apply,
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] at e
    simpa using e
  have hZinj : Function.Injective (restrict a Z Z) := by
    intro z z' hzz'
    -- `a (z - z')` vanishes on `Z`, so it is `⟪·, B† p₀⟫`
    obtain ⟨g, hg⟩ := innerSLFlip_surjective (a ((z : X) - z'))
    have hgZ : g ∈ Zᗮ := by
      rw [Submodule.mem_orthogonal]
      intro y hy
      have e := congrArg (fun f => f ⟨y, hy⟩) hzz'
      simp only [restrict_apply] at e
      have : a ((z : X) - z') y = 0 := by
        rw [map_sub, sub_apply, e, sub_self]
      rw [← hg, innerSLFlip_apply_apply] at this
      exact this
    obtain ⟨p₀, hp₀⟩ := exists_adjoint_eq_of_mem_orthogonal hβ hb hgZ
    have hsol : IsSaddleSolution a B 0 0 ((z : X) - z') (-p₀) := ⟨fun v => by
      rw [map_neg, inner_neg_right, hp₀, ← innerSLFlip_apply_apply (𝕜 := 𝕜) g v, hg]
      simp, fun q => by
        rw [map_sub, show B z = 0 from z.2, show B z' = 0 from z'.2, sub_zero,
          inner_zero_right]; rfl⟩
    obtain ⟨⟨u₀, p₁⟩, -, huniq⟩ := H 0 0
    have h1 := huniq ((z : X) - z', -p₀) hsol
    have h0 := huniq (0, 0) ⟨fun v => by simp, fun q => by simp⟩
    have : (z : X) - z' = 0 := congrArg Prod.fst (h1.trans h0.symm)
    exact Subtype.ext (sub_eq_zero.1 this)
  obtain ⟨γ, hγ⟩ := exists_infSup_of_bijective ⟨hZinj, hZsurj⟩
  refine ⟨⟨γ, hγ⟩, ?_, C⁻¹, hβ, hb⟩
  exact (babuskaNecas_iff.2 fun f =>
    ⟨_, (hZsurj f).choose_spec, fun y hy => hZinj (hy.trans (hZsurj f).choose_spec.symm)⟩).2

/-! ### Constraint forms -/

section Form

variable {b : X →L[𝕜] Y →L⋆[𝕜] 𝕜}

/-- `ker (rieszOp b) = {v | b v = 0}`. -/
theorem mem_ker_rieszOp_iff {v : X} : v ∈ (rieszOp b).ker ↔ ∀ q, b v q = 0 := by
  constructor
  · intro h q; rw [← inner_rieszOp, show rieszOp b v = 0 from h, inner_zero_right]
  · intro h
    show rieszOp b v = 0
    exact ext_inner_left 𝕜 fun q => by rw [inner_rieszOp, h, inner_zero_right]

/-- `‖(rieszOp b)† q‖ = sup_v |b v q| / ‖v‖`: the inf-sup condition of `b` with the inf over `q`
is `β ‖q‖ ≤ ‖(rieszOp b)† q‖`. -/
theorem norm_adjoint_rieszOp_apply (q : Y) :
    ‖adjoint (rieszOp b) q‖ = ‖(b.flip q : X →L[𝕜] 𝕜)‖ := by
  have : (b.flip q : X →L[𝕜] 𝕜) = InnerProductSpace.toDual 𝕜 X (adjoint (rieszOp b) q) :=
    ContinuousLinearMap.ext fun v => by
      rw [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.adjoint_inner_left,
        inner_rieszOp]; rfl
  rw [this, LinearIsometryEquiv.norm_map]

/-- The saddle point problem with constraint form `b`:
`a u v + conj (b v p) = F v`, `b u q = G q`. -/
theorem isSaddleSolution_rieszOp_iff {u : X} {p : Y} :
    IsSaddleSolution a (rieszOp b) F G u p ↔
      (∀ v, a u v + star (b v p) = F v) ∧ ∀ q, b u q = G q := by
  have h1 : ∀ v, ⟪v, adjoint (rieszOp b) p⟫ = star (b v p) := fun v => by
    rw [ContinuousLinearMap.adjoint_inner_right, ← inner_rieszOp b v p, ← inner_conj_symm]
    rfl
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨fun v => by rw [← h1]; exact h v, fun q => by rw [← inner_rieszOp]; exact h' q⟩
  · rintro ⟨h, h'⟩
    exact ⟨fun v => by rw [h1]; exact h v, fun q => by rw [inner_rieszOp]; exact h' q⟩

end Form

end Feec.Variational
