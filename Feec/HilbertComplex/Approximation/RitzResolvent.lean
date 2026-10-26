module

public import Feec.HilbertComplex.Approximation.Ritz
public import Feec.HilbertComplex.Approximation.DissipGalerkin

/-!
# The discrete resolvent as a Ritz projection

The Trotter–Kato core of `Feec.HilbertComplex.DissipGalerkin` (`DissipFEEC.Core.ofResolvent`,
comparison trajectories `pₕ(t) = (1 - Lₕ)⁻¹ πₕ (1 - A) S(t) x` on `D(A²) = (1 - A)⁻¹ D(A)`) is a
Ritz projection (`Feec.HilbertComplex.DissipFEEC.Ritz`) for the **resolvent lift**
(`DissipFEEC.Lift.resolvent`): `G = E`, `ℓ = 1 - A`, read back by `ρ = (1 - A)⁻¹`. The projection
is `Rₕ = (1 - Lₕ)⁻¹ πₕ`, and with `Dₕ = πₕ (1 - A)⁻¹ - (1 - Lₕ)⁻¹ πₕ` the defect identity holds with
`Δₕ = -Dₕ`, `Δₕ' = Dₕ` (`DissipFEEC.Ritz.ofResolvent`). Resolvent consistency
`ιₕ (1 - Lₕ)⁻¹ πₕ → (1 - A)⁻¹` and `ιₕ πₕ → 1` are exactly the hypotheses of `Ritz.toCore`
(`Ritz.tendsto_ofResolvent`), and the comparison trajectories are those of
`Comparison.ofResolvent` (`Ritz.ofResolvent_cmp_p`).

Unlike the wave, whose Ritz projection is the elliptic projection on the graph space of `𝐝`, the
resolvent lift reads lifted states through `(1 - A)⁻¹`, not through an inclusion.

## References

* [A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*][Pazy1983],
  §3.4 (Thm 4.2, Trotter–Kato, resolvent form)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology

@[expose] public noncomputable section

universe u

namespace Feec.HilbertComplex.DissipFEEC

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  {A : E →ₗ.[𝕜] E} {κ : Type*} (F : DissipFEEC.{u} A κ)

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem genExt_sub {y z : E} (hy : y ∈ A.domain) (hz : z ∈ A.domain) :
    genExt A (y - z) = genExt A y - genExt A z := by
  rw [genExt_of_mem (A.domain.sub_mem hy hz), genExt_of_mem hy, genExt_of_mem hz]
  exact A.toFun.map_sub ⟨y, hy⟩ ⟨z, hz⟩

/-- `ℓ = 1 - A` commutes with `S(t)` on `D(A)` (`t ≥ 0`). -/
theorem S_sub_genExt {z : E} (hz : z ∈ A.domain) {t : ℝ} (ht : 0 ≤ t) :
    F.S t z - genExt A (F.S t z) = F.S t (z - genExt A z) := by
  rw [_root_.map_sub, F.S_genExt hz ht]

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
theorem genExt_mem_domain_of_mem_resData {x : E} (hx : x ∈ resData (A := A))
    (hA : A.IsMDissipative) : genExt A x ∈ A.domain := by
  have h := A.domain.sub_mem (mem_domain_of_mem_resData hA hx) (sub_genExt_mem_domain hA hx)
  rwa [sub_sub_cancel] at h

/-- The **resolvent lift**: data `D(A²) = (1 - A)⁻¹ D(A)`, `ℓ = 1 - A`, read back by
`ρ = (1 - A)⁻¹`. -/
def Lift.resolvent : F.Lift E where
  Data := resData (A := A)
  le_domain _ hx := mem_domain_of_mem_resData F.isMDissipative hx
  S_mem x hx t ht := by
    obtain ⟨u, hu, rfl⟩ := hx
    exact ⟨_, F.isMDissipative.semigroup_mem_domain ⟨u, hu⟩ ht, F.resolvent_S ht u⟩
  lift y := y - genExt A y
  read := Operator.resolvent A 1
  read_lift _ hy := resolvent_sub_genExt F.isMDissipative hy
  continuousOn x hx := (F.isMDissipative.semigroup.strongCont (x - genExt A x)).congr fun _ ht =>
    F.S_sub_genExt (mem_domain_of_mem_resData F.isMDissipative hx) ht
  continuousOn' x hx := (F.isMDissipative.semigroup.strongCont
    (genExt A x - genExt A (genExt A x))).congr fun _ ht =>
      F.S_sub_genExt (genExt_mem_domain_of_mem_resData hx F.isMDissipative) ht
  hasDerivWithinAt x hx t ht := by
    have hxd := mem_domain_of_mem_resData F.isMDissipative hx
    have hAx := genExt_mem_domain_of_mem_resData hx F.isMDissipative
    have hu := sub_genExt_mem_domain F.isMDissipative hx
    have hd : HasDerivWithinAt (fun s => F.S s (x - genExt A x))
        (F.S t (A ⟨_, hu⟩)) (Ici t) t := F.isMDissipative.hasDerivWithinAt_semigroup ⟨_, hu⟩ ht
    rw [← genExt_of_mem hu, genExt_sub hxd hAx, ← F.S_sub_genExt hAx ht] at hd
    exact hd.congr (fun s hs => F.S_sub_genExt hxd (ht.trans hs)) (F.S_sub_genExt hxd ht)

/-- The consistency defect `Dₕ = πₕ (1 - A)⁻¹ - (1 - Lₕ)⁻¹ πₕ` of the discrete resolvent. -/
def resDefect (h : κ) : E →L[𝕜] F.X h :=
  F.proj h ∘L Operator.resolvent A 1 - F.discreteRes h ∘L F.proj h

/-- **The discrete resolvent is a Ritz projection** for the resolvent lift: `Rₕ = (1 - Lₕ)⁻¹ πₕ`,
`Δₕ = -Dₕ`, `Δₕ' = Dₕ`. [Pazy1983], §3.4 -/
def Ritz.ofResolvent : F.Ritz (Lift.resolvent F) where
  R h := F.discreteRes h ∘L F.proj h
  Δ h := -F.resDefect h
  Δ' := F.resDefect
  defect_eq h y hy := by
    have hyd : y ∈ A.domain := mem_domain_of_mem_resData F.isMDissipative hy
    have hAy := genExt_mem_domain_of_mem_resData hy F.isMDissipative
    have hb := sub_genExt_mem_domain F.isMDissipative hy
    set R1 := Operator.resolvent A (1 : 𝕜)
    set a := genExt A y - genExt A (genExt A y)
    set b := y - genExt A y
    -- `(1 - A)⁻¹ (b - a) = b`, since `a = A b`
    have key : R1 b = b + R1 a := by
      have e : R1 (b - genExt A b) = b := by
        rw [genExt_of_mem hb]; exact resolvent_one_apply_sub F.isMDissipative ⟨b, hb⟩
      rw [genExt_sub hyd hAy, _root_.map_sub] at e
      exact sub_eq_iff_eq_add.1 e
    have hL : F.L h (F.discreteRes h (F.proj h b)) =
        F.discreteRes h (F.proj h b) - F.proj h b := by
      rw [eq_sub_iff_add_eq, add_comm, ← eq_sub_iff_add_eq]
      exact (F.discreteRes_sub h _).symm
    change F.discreteRes h (F.proj h a) - F.L h (F.discreteRes h (F.proj h b)) =
      -(F.proj h (R1 a) - F.discreteRes h (F.proj h a)) +
        (F.proj h (R1 b) - F.discreteRes h (F.proj h b))
    rw [hL, key, _root_.map_add]
    abel
  bound := by
    set C := F.boundConst
    have hC := F.boundConst_nonneg
    have hG : ∀ h, ‖F.discreteRes h ∘L F.proj h‖ ≤ C := fun h =>
      ContinuousLinearMap.opNorm_le_bound _ hC fun y =>
        (F.norm_discreteRes_apply_le h _).trans
          (((F.proj h).le_opNorm y).trans (mul_le_mul_of_nonneg_right (F.norm_proj_le h)
            (norm_nonneg _)))
    have hP : ∀ h, ‖F.proj h ∘L Operator.resolvent A 1‖ ≤ C := fun h =>
      ContinuousLinearMap.opNorm_le_bound _ hC fun y => by
        have h1 : ‖Operator.resolvent A (1 : 𝕜) y‖ ≤ ‖y‖ := by
          simpa using F.isMDissipative.norm_resolvent_apply_le one_pos y
        exact ((F.proj h).le_opNorm _).trans (mul_le_mul (F.norm_proj_le h) h1 (norm_nonneg _) hC)
    have hD : ∀ h, ‖F.resDefect h‖ ≤ 2 * C := fun h =>
      (norm_sub_le _ _).trans (by linarith [hG h, hP h])
    exact ⟨2 * C, fun h => ⟨(hG h).trans (by linarith), (norm_neg (F.resDefect h)).symm ▸ hD h,
      hD h⟩⟩

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- **Resolvent consistency makes the defect vanish**: `ιₕ (1 - Lₕ)⁻¹ πₕ → (1 - A)⁻¹` and
`ιₕ πₕ → 1` strongly give `Dₕ → 0` strongly (`‖v‖ ≤ C ‖ιₕ v‖`). -/
theorem tendsto_norm_resDefect
    (hres : ∀ z, Tendsto (fun h => F.incl h (F.discreteRes h (F.proj h z))) F.l
      (𝓝 (Operator.resolvent A 1 z)))
    (happ : ∀ z, Tendsto (fun h => F.incl h (F.proj h z)) F.l (𝓝 z)) (g : E) :
    Tendsto (fun h => ‖F.resDefect h g‖) F.l (𝓝 0) := by
  have hι : Tendsto (fun h => ‖F.incl h (F.resDefect h g)‖) F.l (𝓝 0) := by
    have := ((happ (Operator.resolvent A 1 g)).sub (hres g)).norm
    rw [sub_self, norm_zero] at this
    refine this.congr fun h => ?_
    simp only [resDefect, sub_apply, ContinuousLinearMap.comp_apply,
      _root_.map_sub]
  have h0 := hι.const_mul F.boundConst
  rw [mul_zero] at h0
  exact squeeze_zero (fun _ => norm_nonneg _) (fun h => F.norm_le_norm_incl h _) h0

/-- The defects of the resolvent Ritz projection tend to `0` strongly under resolvent
consistency: the hypotheses of `Core.ofResolvent` are those of `Ritz.toCore`. -/
theorem Ritz.tendsto_ofResolvent
    (hres : ∀ z, Tendsto (fun h => F.incl h (F.discreteRes h (F.proj h z))) F.l
      (𝓝 (Operator.resolvent A 1 z)))
    (happ : ∀ z, Tendsto (fun h => F.incl h (F.proj h z)) F.l (𝓝 z)) :
    (∀ g, Tendsto (fun h => ‖(Ritz.ofResolvent F).Δ h g‖) F.l (𝓝 0)) ∧
      ∀ g, Tendsto (fun h => ‖(Ritz.ofResolvent F).Δ' h g‖) F.l (𝓝 0) :=
  ⟨fun g => (F.tendsto_norm_resDefect hres happ g).congr fun h => (norm_neg (F.resDefect h g)).symm,
    F.tendsto_norm_resDefect hres happ⟩

/-- **The resolvent Ritz projection has the trajectories of `Comparison.ofResolvent`**: on the
data `D(A²)`, `(1 - Lₕ)⁻¹ πₕ ℓ(S(t) x) = (1 - Lₕ)⁻¹ πₕ S(t) (1 - A) x` for `t ≥ 0`. -/
theorem Ritz.ofResolvent_cmp_p {T : ℝ} {x : E} (hx : x ∈ resData (A := A)) (h : κ) {t : ℝ}
    (ht : 0 ≤ t) : ((Ritz.ofResolvent F).cmp T).p x h t = (Comparison.ofResolvent F T).p x h t :=
  congrArg (fun z => F.discreteRes h (F.proj h z))
    (F.S_sub_genExt (mem_domain_of_mem_resData F.isMDissipative hx) ht)

end Feec.HilbertComplex.DissipFEEC
