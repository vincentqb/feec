module

public import Feec.HilbertComplex.Approximation.ApproxComplexCrime
public import Feec.HilbertComplex.Approximation.ApproxComplexWitness

/-!
# Non-vacuity of `ApproxFEEC.ofComplexCrime`: a nonzero cochain defect, and rates

On the complex `𝕜 --id--> 𝕜 → 0` (`Feec.HilbertComplex.ConstrainedFEEC.idComplex`):

* **A reading map that is not a cochain map.** The family
  `Feec.HilbertComplex.ApproxComplexCrime.shifted` has, at level `n` with `cₙ = 1 + 1/(n+1)`, the
  discrete differential space `𝕜 × 𝕜 × 0` with `𝐝ₙ = cₙ·d` (the differential of
  `Feec.HilbertComplex.ApproxComplex.scaledShort`), read in `W` by the **identity**: `iₙ` is
  isometric (`Jₙ = 1`), but `𝐝 iₙ ≠ iₙ 𝐝ₙ` (`shifted_not_cochain`). Its cochain defect is
  `⟪κₙ(y), v⟫ = (cₙ - 1) ȳ₁ v₀` (`inner_shifted_cochainDefect`): **nonzero** at every level for
  `y = (0, 1, 0)` (`shifted_cochainDefect_ne_zero`), and at most `(cₙ - 1) ‖y‖` in the dual
  discrete graph norm. The family goes through `ApproxComplexCrime.ofCochainDefect` (graph-norm
  approximation by `w = y`, error `(cₙ - 1) |y₀|`), so the approximating FEEC theorem applies with
  all core hypotheses derived; its rate is `O(cₙ - 1)` (`shifted_rate`). The scheme is inexact
  (`shifted_exists_sol_ne`).
* **The rate of the inner-product crime.** The cochain family
  `Feec.HilbertComplex.ApproxComplex.scaled` (`iₙ = diag(cₙ, 1, 1)`, `Feec.HilbertComplex.Approximation.ApproxComplexWitness`)
  gets, through `ApproxComplex.toCrime` and `ApproxComplexCrime.rateClass`, the rate given by its
  inner-product defect: `‖e^{tL} x - iₙ e^{tLₙ} Rₙ x‖ ≤ (C + C_ι C' t) (cₙ² - 1) ‖x‖_{D(L²)}`
  (`scaled_rate`), with exact graph-norm approximation and zero cochain defect.
* **Distinct orders: `min(α, β, γ)` is attained by the inner-product defect.** The family
  `Feec.HilbertComplex.ApproxComplexCrime.mixed` (`𝐝ₙ = bₙ·d` with `bₙ = cₙ + hₙ²`, read by
  `iₙ = diag(cₙ, 1, 1)`, `hₙ = 1/(n+1)`) has both crimes: inner-product defect positive and
  `≤ 3 hₙ` (`mixed_innerDefect_le_mesh`), cochain defect `⟪κₙ(0, 1, 0), (1, 0, 0)⟫ = hₙ²`
  (`inner_mixed_cochainDefect_secondDatum`), graph-norm error of `πₙ y` at most `hₙ² ‖y‖`
  (`norm_idTotalD_sub_mixed_le`). Through `ApproxComplexCrime.rateClass_of_split` with
  `(α, β, γ) = (2, 1, 2)` it gets a rate class of order `min(2, 1, 2) = 1` (`mixedRate_α`) and the
  error `O(hₙ)` (`mixed_rate`, `mixed_nonvacuous`).

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3 (inner-product crimes; the cochain defect is a further crime)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap Metric

@[expose] public noncomputable section

namespace Feec.HilbertComplex

namespace ApproxComplexCrime

open ConstrainedFEEC ShortHilbertComplex ApproxFEEC ApproxComplex

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The continuous differential of `𝕜 --id--> 𝕜 → 0` on components -/

theorem c0_idTotalD (v : (idComplex 𝕜).totalD.domain) :
    c0 ((idComplex 𝕜).totalD v) = 0 := by
  change ((idComplex 𝕜).totalD v) 0 = 0
  rw [totalD_apply, Fin.sum_univ_three]
  simp only [apply_eq_zero_of_eq_zero (show (idComplex 𝕜).d 0 0 = 0 from rfl),
    apply_eq_zero_of_eq_zero (show (idComplex 𝕜).d 1 0 = 0 from rfl),
    apply_eq_zero_of_eq_zero (show (idComplex 𝕜).d 2 0 = 0 from rfl), add_zero]

theorem c1_idTotalD (v : (idComplex 𝕜).totalD.domain) :
    c1 ((idComplex 𝕜).totalD v) = c0 (v : PiLp 2 (W3 𝕜 𝕜 PUnit)) := by
  change ((idComplex 𝕜).totalD v) 1 = _
  rw [totalD_apply, Fin.sum_univ_three]
  simp only [apply_eq_zero_of_eq_zero (show (idComplex 𝕜).d 1 1 = 0 from rfl),
    apply_eq_zero_of_eq_zero (show (idComplex 𝕜).d 2 1 = 0 from rfl), add_zero]
  rfl

theorem mem_idComplex_totalD_domain (v : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    v ∈ (idComplex 𝕜).totalD.domain := (mem_idComplex_wave_domain v).1

theorem mem_idComplex_domainSq (x : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    x ∈ (idComplex 𝕜).wave.domainSq :=
  mem_domainSq.2 ⟨mem_idComplex_wave_domain x, mem_idComplex_wave_domain _⟩

omit [RCLike 𝕜] in
theorem norm_vec3_zero [RCLike 𝕜] (a : 𝕜) : ‖vec3 0 a‖ = ‖a‖ := by
  have h := PiLp.norm_sq_eq_of_L2 (W3 𝕜 𝕜 PUnit) (vec3 (0 : 𝕜) a)
  rw [Fin.sum_univ_three] at h
  have h0 : ‖(vec3 (0 : 𝕜) a) 0‖ = 0 := norm_zero
  have h2 : ‖(vec3 (0 : 𝕜) a) 2‖ = 0 := norm_zero
  have h1 : ‖(vec3 (0 : 𝕜) a) 1‖ = ‖a‖ := rfl
  rw [h0, h1, h2] at h
  have := norm_nonneg (vec3 (0 : 𝕜) a)
  nlinarith [norm_nonneg a]

theorem norm_c0_le (u : PiLp 2 (W3 𝕜 𝕜 PUnit)) : ‖c0 u‖ ≤ ‖u‖ := PiLp.norm_apply_le u 0

theorem norm_c1_le (u : PiLp 2 (W3 𝕜 𝕜 PUnit)) : ‖c1 u‖ ≤ ‖u‖ := PiLp.norm_apply_le u 1

/-! ### The shifted family: an isometric reading map that is not a cochain map -/

variable (𝕜) in
/-- **Discrete differential spaces with a non-cochain reading map** for `𝕜 --id--> 𝕜 → 0`: at
level `n`, `Xₙ = 𝕜 × 𝕜 × 0` with the differential `𝐝ₙ = cₙ·d` of `scaledShort`, read in `W` by
the identity (`iₙ = πₙ = 1`). -/
abbrev shiftedFamily : ApproxComplexCrime.Family (idComplex 𝕜) ℕ where
  X _ := PiLp 2 (W3 𝕜 𝕜 PUnit)
  D n := (scaledFamily 𝕜).D n
  D_D n v := (scaledShort 𝕜 (sc n)).toHilbertComplex.totalDL_totalDL v
  incl _ := ContinuousLinearMap.id 𝕜 _
  proj _ := ContinuousLinearMap.id 𝕜 _
  proj_incl _ _ := rfl
  bound := ⟨1, fun _ => ⟨ContinuousLinearMap.norm_id_le, ContinuousLinearMap.norm_id_le⟩⟩

/-- The reading map is isometric: `Jₙ = 1`. -/
theorem shifted_J (n : ℕ) : (shiftedFamily 𝕜).J n = 1 :=
  ContinuousLinearMap.ext fun v => ext_inner_right 𝕜 fun w => by
    rw [ApproxComplexCrime.Family.inner_J, one_apply_eq_self]; rfl

/-- `𝐝ₙ v - 𝐝 v = (0, (cₙ - 1) v₀, 0)`. -/
theorem shifted_D_sub (n : ℕ) (v : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    (shiftedFamily 𝕜).D n v - (idComplex 𝕜).totalD ⟨v, mem_idComplex_totalD_domain v⟩ =
      vec3 0 ((sc n - 1) * c0 v) := by
  refine ext3 ?_ ?_
  · change c0 ((scaledFamily 𝕜).D n v) - c0 ((idComplex 𝕜).totalD _) = 0
    rw [c0_scaled_D, c0_idTotalD, sub_zero]
  · change c1 ((scaledFamily 𝕜).D n v) - c1 ((idComplex 𝕜).totalD _) = _
    rw [c1_scaled_D, c1_idTotalD, c1_vec3]
    ring

/-- **The reading map is not a cochain map** at any level: `𝐝 iₙ (1, 0, 0) ≠ iₙ 𝐝ₙ (1, 0, 0)`. -/
theorem shifted_not_cochain (n : ℕ) :
    (idComplex 𝕜).totalD ⟨firstDatum 𝕜, mem_idComplex_totalD_domain _⟩ ≠
      (shiftedFamily 𝕜).incl n ((shiftedFamily 𝕜).D n (firstDatum 𝕜)) := fun h => by
  have e := congrArg c1 (shifted_D_sub (𝕜 := 𝕜) n (firstDatum 𝕜))
  have h' : (shiftedFamily 𝕜).D n (firstDatum 𝕜) -
      (idComplex 𝕜).totalD ⟨firstDatum 𝕜, mem_idComplex_totalD_domain _⟩ = 0 := by
    rw [h]; exact sub_self _
  rw [h', c1_vec3] at e
  have e1 : c0 (firstDatum 𝕜) = 1 := rfl
  rw [e1, mul_one] at e
  have : sc (𝕜 := 𝕜) n = 1 := (sub_eq_zero.1 e.symm)
  have hn := one_lt_norm_sc (𝕜 := 𝕜) n
  rw [this, norm_one] at hn
  exact lt_irrefl _ hn

/-- **The cochain defect** `⟪κₙ(y), v⟫ = (cₙ - 1) ȳ₁ v₀`. -/
theorem inner_shifted_cochainDefect (n : ℕ) (y : (idComplex 𝕜).wave.domain)
    (v : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    ⟪(shiftedFamily 𝕜).cochainDefect n y, v⟫_𝕜 =
      starRingEnd 𝕜 (c1 (y : PiLp 2 (W3 𝕜 𝕜 PUnit))) * ((sc n - 1) * c0 v) := by
  rw [(shiftedFamily 𝕜).inner_cochainDefect_of_mem n y v (mem_idComplex_totalD_domain v)]
  change ⟪(y : PiLp 2 (W3 𝕜 𝕜 PUnit)), (shiftedFamily 𝕜).D n v -
    (idComplex 𝕜).totalD ⟨v, mem_idComplex_totalD_domain v⟩⟫_𝕜 = _
  rw [shifted_D_sub, inner_W3, c0_vec3, c1_vec3, mul_zero, zero_add]

theorem norm_sc_sub_one (n : ℕ) : ‖sc (𝕜 := 𝕜) n - 1‖ = perturbMesh n := by
  rw [show sc (𝕜 := 𝕜) n - 1 = ((perturbScale n - 1 : ℝ) : 𝕜) by push_cast; rfl,
    RCLike.norm_ofReal, abs_of_pos (by linarith [one_lt_perturbScale n])]
  unfold perturbScale; ring

/-- **The cochain defect is at most `(cₙ - 1) ‖y‖`** in the dual discrete graph norm. -/
theorem norm_inner_shifted_cochainDefect_le (n : ℕ) (y : (idComplex 𝕜).wave.domain)
    (v : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    ‖⟪(shiftedFamily 𝕜).cochainDefect n y, v⟫_𝕜‖ ≤
      perturbMesh n * ‖(y : PiLp 2 (W3 𝕜 𝕜 PUnit))‖ * (‖v‖ + ‖(shiftedFamily 𝕜).D n v‖) := by
  rw [inner_shifted_cochainDefect, norm_mul, norm_mul, RCLike.norm_conj, norm_sc_sub_one]
  have h1 := norm_c1_le (y : PiLp 2 (W3 𝕜 𝕜 PUnit))
  have h2 := norm_c0_le v
  have hm := (perturbMesh_pos n).le
  have := norm_nonneg ((shiftedFamily 𝕜).D n v)
  calc _ ≤ ‖(y : PiLp 2 (W3 𝕜 𝕜 PUnit))‖ * (perturbMesh n * ‖v‖) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 hm) (by positivity) (norm_nonneg _)
    _ ≤ _ := by
      have hh := mul_nonneg (mul_nonneg hm (norm_nonneg (y : PiLp 2 (W3 𝕜 𝕜 PUnit)))) this
      nlinarith [hh]

/-- **The cochain defect is nonzero** at every level: for `y = (0, 1, 0)`,
`⟪κₙ(y), (1, 0, 0)⟫ = cₙ - 1 ≠ 0`. -/
theorem shifted_cochainDefect_ne_zero (n : ℕ) :
    (shiftedFamily 𝕜).cochainDefect n ⟨secondDatum 𝕜, mem_idComplex_wave_domain _⟩ ≠ 0 :=
  fun h => by
    have e := inner_shifted_cochainDefect (𝕜 := 𝕜) n
      ⟨secondDatum 𝕜, mem_idComplex_wave_domain _⟩ (firstDatum 𝕜)
    rw [h, inner_zero_left] at e
    change (0 : 𝕜) = starRingEnd 𝕜 1 * ((sc n - 1) * 1) at e
    rw [map_one, one_mul, mul_one] at e
    have := norm_sc_sub_one (𝕜 := 𝕜) n
    rw [← e, norm_zero] at this
    exact (perturbMesh_pos n).ne this

/-- The graph-norm error of the approximant `w = y`: `‖𝐝 y - 𝐝ₙ y‖ ≤ (cₙ - 1) ‖y‖`. -/
theorem norm_idTotalD_sub_shifted_le (n : ℕ) (y : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    ‖(idComplex 𝕜).totalD ⟨y, mem_idComplex_totalD_domain y⟩ -
      (shiftedFamily 𝕜).incl n ((shiftedFamily 𝕜).D n y)‖ ≤ perturbMesh n * ‖y‖ := by
  have e : (idComplex 𝕜).totalD ⟨y, mem_idComplex_totalD_domain y⟩ -
      (shiftedFamily 𝕜).incl n ((shiftedFamily 𝕜).D n y) =
        -((shiftedFamily 𝕜).D n y - (idComplex 𝕜).totalD ⟨y, mem_idComplex_totalD_domain y⟩) :=
    (neg_sub _ _).symm
  rw [e, norm_neg, shifted_D_sub, norm_vec3_zero, norm_mul, norm_sc_sub_one]
  exact mul_le_mul_of_nonneg_left (norm_c0_le y) (perturbMesh_pos n).le

theorem tendsto_perturbMesh : Tendsto perturbMesh atTop (𝓝 0) := by
  unfold perturbMesh; exact tendsto_one_div_add_atTop_nhds_zero_nat

variable (𝕜) in
/-- **The approximating family with a nonzero cochain defect** (constraint `K`): admissible states
`D(L)`, core `D(L²)` (here the whole space), graph-norm approximation by `w = y` and the cochain
defect bound `(cₙ - 1) ‖y‖`, through `ApproxComplexCrime.ofCochainDefect`. -/
abbrev shifted (K : Submodule 𝕜 (PiLp 2 (W3 𝕜 𝕜 PUnit)))
    (hK : IsClosed (K : Set (PiLp 2 (W3 𝕜 𝕜 PUnit)))) : ApproxComplexCrime (idComplex 𝕜) ℕ :=
  ofCochainDefect (shiftedFamily 𝕜) K hK atTop (idComplex 𝕜).wave.domain (fun _ hy => hy)
    (idComplex 𝕜).wave.domainSq le_rfl
    (fun x _ t _ => ⟨mem_idComplex_wave_domain _, mem_idComplex_wave_domain _⟩)
    (by simp only [shifted_J, sub_self, norm_zero]; exact tendsto_const_nhds)
    (fun y _ ε hε => by
      have hev := (tendsto_perturbMesh.mul_const ‖y‖).eventually
        (gt_mem_nhds (show (0 : ℝ) * ‖y‖ < ε by rw [zero_mul]; exact hε))
      filter_upwards [hev] with n hn
      refine ⟨y, ?_⟩
      change ‖y - y‖ + ‖(idComplex 𝕜).totalD ⟨y, _⟩ -
        (shiftedFamily 𝕜).incl n ((shiftedFamily 𝕜).D n y)‖ < ε
      rw [sub_self, norm_zero, zero_add]
      exact (norm_idTotalD_sub_shifted_le n y).trans_lt hn)
    (fun y hy ε hε => by
      have hev := (tendsto_perturbMesh.mul_const ‖y‖).eventually
        (gt_mem_nhds (show (0 : ℝ) * ‖y‖ < ε by rw [zero_mul]; exact hε))
      filter_upwards [hev] with n hn v
      refine (norm_inner_shifted_cochainDefect_le n ⟨y, hy⟩ v).trans ?_
      exact mul_le_mul_of_nonneg_right hn.le (by positivity))

variable (Q : Submodule 𝕜 (PiLp 2 (W3 𝕜 𝕜 PUnit))) (hQ : IsClosed (Q : Set (PiLp 2 (W3 𝕜 𝕜 PUnit))))

/-- **The scheme is inexact**: from `(0, 1, 0)` the discrete solution differs from the exact one
at some time (`(Lₙ x)₀ = -cₙ ≠ -1 = (L x)₀`). -/
theorem shifted_exists_sol_ne (n : ℕ) :
    ∃ t, (ofComplexCrime (shifted 𝕜 Q hQ)).sol n (secondDatum 𝕜) t ≠
      (idComplex 𝕜).waveGroup.S t (secondDatum 𝕜) := by
  set S := shiftedFamily 𝕜
  refine (ofComplexCrime (shifted 𝕜 Q hQ)).exists_sol_ne (mem_idComplex_wave_domain _) n _
    fun he => ?_
  have he0 := congrArg c0 he
  change c0 (S.L n (secondDatum 𝕜)) = c0 (idWave 𝕜 (secondDatum 𝕜)) at he0
  have a1 : c0 (S.L n (secondDatum 𝕜)) = -sc n := by
    have sk : ⟪firstDatum 𝕜, S.L n (secondDatum 𝕜)⟫_𝕜 =
        -⟪S.L n (firstDatum 𝕜), secondDatum 𝕜⟫_𝕜 := by
      rw [diffWave_skew, neg_neg]
    rw [← inner_firstDatum_left, sk, inner_diffWave, inner_secondDatum_right]
    change -(starRingEnd 𝕜 (c1 ((scaledFamily 𝕜).D n (firstDatum 𝕜))) -
      ⟪firstDatum 𝕜, (scaledFamily 𝕜).D n (secondDatum 𝕜)⟫_𝕜) = _
    rw [c1_scaled_D_firstDatum, scaled_D_secondDatum, inner_zero_right, sub_zero, sc_conj]
  have a2 : c0 (idWave 𝕜 (secondDatum 𝕜)) = -1 := by
    have sk : ⟪firstDatum 𝕜, idWave 𝕜 (secondDatum 𝕜)⟫_𝕜 =
        -⟪idWave 𝕜 (firstDatum 𝕜), secondDatum 𝕜⟫_𝕜 := by
      rw [idWave_skew, neg_neg]
    rw [← inner_firstDatum_left, sk, inner_secondDatum_right, c1_idWave_firstDatum, map_one]
  rw [a1, a2, neg_inj] at he0
  have hn := one_lt_norm_sc (𝕜 := 𝕜) n
  rw [he0, norm_one] at hn
  exact lt_irrefl _ hn

/-! ### Rates -/

/-- The class norm `‖x‖ + ‖L x‖ + ‖L² x‖` (the graph norm of `L²`). -/
def l2Norm (x : PiLp 2 (W3 𝕜 𝕜 PUnit)) : ℝ :=
  ‖x‖ + ‖waveExt (idComplex 𝕜) x‖ + ‖waveExt (idComplex 𝕜) (waveExt (idComplex 𝕜) x)‖

theorem norm_le_l2Norm_of_mem {x y : PiLp 2 (W3 𝕜 𝕜 PUnit)} {t : ℝ}
    (hy : y ∈ insert ((idComplex 𝕜).waveGroup.S t x)
      ({(idComplex 𝕜).waveGroup.S t (waveExt (idComplex 𝕜) x)} : Set (PiLp 2 (W3 𝕜 𝕜 PUnit)))) :
    ‖y‖ + ‖waveExt (idComplex 𝕜) y‖ ≤ l2Norm x := by
  have hx := mem_idComplex_wave_domain (𝕜 := 𝕜) x
  have hLx := mem_idComplex_wave_domain (𝕜 := 𝕜) (waveExt (idComplex 𝕜) x)
  have i1 := (idComplex 𝕜).isIsometric_waveGroup t x
  have i2 := (idComplex 𝕜).isIsometric_waveGroup t (waveExt (idComplex 𝕜) x)
  have i3 := (idComplex 𝕜).isIsometric_waveGroup t
    (waveExt (idComplex 𝕜) (waveExt (idComplex 𝕜) x))
  have n0 := norm_nonneg x
  have n1 := norm_nonneg (waveExt (idComplex 𝕜) x)
  have n2 := norm_nonneg (waveExt (idComplex 𝕜) (waveExt (idComplex 𝕜) x))
  unfold l2Norm
  rcases hy with rfl | hy
  · rw [waveExt_waveGroup _ hx, i1, i2]; linarith
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [waveExt_waveGroup _ hLx, i2, i3]; linarith

/-- **The rate class of the shifted family**: order `1` in `hₙ = cₙ - 1`, class norm
`‖x‖ + ‖L x‖ + ‖L² x‖`, from the split rates (graph-norm error and cochain defect `O(hₙ)`,
inner-product defect `0`). -/
def shiftedRate (T : ℝ) : (ofComplexCrime (shifted 𝕜 Q hQ)).RateClass T :=
  (shifted 𝕜 Q hQ).rateClass T Set.univ (fun x _ => mem_idComplex_domainSq x) l2Norm
    perturbMesh 1 (2 * (1 + (shiftedFamily 𝕜).boundConst)) fun x _ n t _ y hy => by
      set S := shiftedFamily 𝕜
      have hC := S.boundConst_nonneg
      have hyx := norm_le_l2Norm_of_mem hy
      have hy1 := mem_idComplex_wave_domain (𝕜 := 𝕜) y
      have hm := (perturbMesh_pos n).le
      have hnorm : ‖y‖ ≤ l2Norm x := by linarith [norm_nonneg (waveExt (idComplex 𝕜) y)]
      obtain ⟨h1, h2, h3⟩ := S.rateData_of_split n ⟨y, hy1⟩ y (Ea := perturbMesh n * ‖y‖)
        (Ew := ‖y‖ + ‖S.D n y‖) (Eg := perturbMesh n * ‖y‖)
        (by
          change ‖y - y‖ + _ ≤ _
          rw [sub_self, norm_zero, zero_add]; exact norm_idTotalD_sub_shifted_le n y)
        le_rfl (norm_inner_shifted_cochainDefect_le n ⟨y, hy1⟩)
      rw [Real.rpow_one]
      have hmy : perturbMesh n * ‖y‖ ≤ perturbMesh n * l2Norm x :=
        mul_le_mul_of_nonneg_left hnorm hm
      have hpos : 0 ≤ perturbMesh n * l2Norm x := (mul_nonneg hm (norm_nonneg y)).trans hmy
      refine ⟨y, ?_, ?_, fun v => ?_⟩
      · change ‖y - y‖ ≤ _
        rw [sub_self, norm_zero]; nlinarith
      · show ‖(1 - S.J n) y‖ ≤ _
        refine ((1 - S.J n).le_opNorm y).trans ?_
        rw [shifted_J, sub_self, norm_zero, zero_mul]; nlinarith
      · have h4 := h3 v
        rw [shifted_J, sub_self, norm_zero, zero_mul, zero_add, ← waveExt_of_mem hy1] at h4
        refine h4.trans (mul_le_mul_of_nonneg_right ?_
          (add_nonneg (norm_nonneg _) (norm_nonneg _)))
        nlinarith

/-- **The rate of the shifted family**: from the comparison initial value `Rₙ x`,
`‖e^{tL} x - iₙ e^{tLₙ} Rₙ x‖ ≤ (C + C_ι C' t) (cₙ - 1) (‖x‖ + ‖L x‖ + ‖L² x‖)` on `[0, T]`, a rate
given by the cochain defect `cₙ - 1`. -/
theorem shifted_rate (T : ℝ) (x : PiLp 2 (W3 𝕜 𝕜 PUnit)) (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖(idComplex 𝕜).waveGroup.S t x - (ofComplexCrime (shifted 𝕜 Q hQ)).sol n
        ((shiftedRate Q hQ T).p x n 0) t‖ ≤
      ((shiftedRate Q hQ T).C + ‖(ofComplexCrime (shifted 𝕜 Q hQ)).incl n‖ *
        (shiftedRate Q hQ T).C' * t) * ((perturbScale n - 1) * l2Norm x) := by
  have h := dissipFEEC_rate _ (shiftedRate Q hQ T) (Set.mem_univ x) n
    ((shiftedRate Q hQ T).p x n 0) ht
  rw [ApproxFEEC.S_apply _ ht.1, sub_self, norm_zero, mul_zero, add_zero] at h
  refine h.trans_eq ?_
  change _ * (perturbMesh n ^ (1 : ℝ) * l2Norm x) = _
  rw [Real.rpow_one]
  unfold perturbScale; ring_nf

/-- **Non-vacuity of `ApproxFEEC.ofComplexCrime` with a nonzero cochain defect.** On
`𝕜 --id--> 𝕜 → 0`, the family `shifted` (differential `cₙ·d`, isometric reading map `iₙ = 1`,
`cₙ = 1 + 1/(n+1)`) satisfies: the approximating FEEC theorem with every core hypothesis derived;
`Jₙ = 1`; the reading map is not a cochain map at any level; the cochain defect at `(0, 1, 0)` is
nonzero at every level; the scheme is inexact; the rate is `O(cₙ - 1)`. -/
theorem shifted_nonvacuous :
    (ofComplexCrime (shifted 𝕜 Q hQ)).Verdict (ofComplexCrimeCore (shifted 𝕜 Q hQ)) ∧
    (∀ n, (shiftedFamily 𝕜).J n = 1) ∧
    (∀ n, (idComplex 𝕜).totalD ⟨firstDatum 𝕜, mem_idComplex_totalD_domain _⟩ ≠
      (shiftedFamily 𝕜).incl n ((shiftedFamily 𝕜).D n (firstDatum 𝕜))) ∧
    (∀ n, (shiftedFamily 𝕜).cochainDefect n ⟨secondDatum 𝕜, mem_idComplex_wave_domain _⟩ ≠ 0) ∧
    (∀ n, ∃ t, (ofComplexCrime (shifted 𝕜 Q hQ)).sol n (secondDatum 𝕜) t ≠
      (idComplex 𝕜).waveGroup.S t (secondDatum 𝕜)) ∧
    (∀ T x n, ∀ t ∈ Icc 0 T, ‖(idComplex 𝕜).waveGroup.S t x -
      (ofComplexCrime (shifted 𝕜 Q hQ)).sol n ((shiftedRate Q hQ T).p x n 0) t‖ ≤
        ((shiftedRate Q hQ T).C + ‖(ofComplexCrime (shifted 𝕜 Q hQ)).incl n‖ *
          (shiftedRate Q hQ T).C' * t) * ((perturbScale n - 1) * l2Norm x)) :=
  ⟨(approxFEEC_ofComplexCrime _).1, shifted_J, shifted_not_cochain,
    shifted_cochainDefect_ne_zero, shifted_exists_sol_ne Q hQ,
    fun T x n _ ht => shifted_rate Q hQ T x n ht⟩

/-! ### The rate of the inner-product crime `scaled` -/

/-- **The rate class of `scaled` through `toCrime`**: order `1` in `cₙ² - 1` (its inner-product
defect), class norm `‖x‖ + ‖L x‖ + ‖L² x‖`: exact graph-norm approximation by `πₙ y`, zero cochain
defect, `‖1 - Jₙ‖ ≤ cₙ² - 1`. -/
def scaledRate (T : ℝ) : (ofComplexCrime (scaled 𝕜 Q hQ).toCrime).RateClass T :=
  (scaled 𝕜 Q hQ).toCrime.rateClass T Set.univ (fun x _ => mem_idComplex_domainSq x) l2Norm
    (fun n => perturbScale n ^ 2 - 1) 1
    (2 * (1 + (scaledFamily 𝕜).toCrimeFamily.boundConst) ^ 2) fun x _ n t _ y hy => by
      set S := (scaledFamily 𝕜).toCrimeFamily
      have hC := S.boundConst_nonneg
      have hyx := norm_le_l2Norm_of_mem hy
      have hy1 := mem_idComplex_wave_domain (𝕜 := 𝕜) y
      set w : S.X n := (scaledFamily 𝕜).projL n y
      have hg := scaled_graphIncl_projL (𝕜 := 𝕜) n (waveLift (idComplex 𝕜) ⟨y, hy1⟩)
      rw [graphFst_waveLift] at hg
      have hiw : S.incl n w = y := by
        have := congrArg (idComplex 𝕜).totalD.graphFst hg
        rw [(scaledFamily 𝕜).graphFst_graphIncl] at this
        exact this
      have hiDw : S.incl n (S.D n w) = (idComplex 𝕜).totalD ⟨y, hy1.1⟩ := by
        have := congrArg (idComplex 𝕜).totalD.graphSnd hg
        rw [(scaledFamily 𝕜).graphSnd_graphIncl] at this
        exact this
      have hJ : ‖1 - S.J n‖ ≤ perturbScale n ^ 2 - 1 := scaled_innerDefect_le n
      have hJ0 : 0 ≤ perturbScale n ^ 2 - 1 := (norm_nonneg _).trans hJ
      have hw : ‖w‖ + ‖S.D n w‖ ≤ S.boundConst * l2Norm x := by
        have a1 := S.norm_le_norm_incl n w
        have a2 := S.norm_le_norm_incl n (S.D n w)
        rw [hiw] at a1
        rw [hiDw] at a2
        have a3 : ‖(idComplex 𝕜).totalD ⟨y, hy1.1⟩‖ ≤ ‖waveExt (idComplex 𝕜) y‖ := by
          rw [waveExt_of_mem hy1]; exact norm_totalD_le_norm_wave (idComplex 𝕜) ⟨y, hy1⟩
        nlinarith [mul_le_mul_of_nonneg_left a3 hC, mul_le_mul_of_nonneg_left hyx hC]
      obtain ⟨h1, h2, h3⟩ := S.rateData_of_split n ⟨y, hy1⟩ w (Ea := 0)
        (Ew := S.boundConst * l2Norm x) (Eg := 0)
        (by dsimp only; rw [hiw, hiDw, sub_self, sub_self, norm_zero, add_zero])
        hw (fun v => by
          rw [(scaledFamily 𝕜).cochainDefect_toCrimeFamily, inner_zero_left, norm_zero,
            zero_mul])
      rw [Real.rpow_one]
      have hl : 0 ≤ l2Norm x := by unfold l2Norm; positivity
      have key : ‖1 - S.J n‖ * (S.boundConst * l2Norm x) ≤
          2 * (1 + S.boundConst) ^ 2 * (perturbScale n ^ 2 - 1) * l2Norm x := by
        have := mul_le_mul_of_nonneg_right hJ (mul_nonneg hC hl)
        nlinarith [mul_nonneg hJ0 hl, mul_nonneg (mul_nonneg hJ0 hl) hC,
          mul_nonneg (mul_nonneg hJ0 hl) (sq_nonneg S.boundConst)]
      refine ⟨w, ?_, h2.trans key, fun v => ?_⟩
      · show ‖y - S.incl n w‖ ≤ _
        rw [hiw, sub_self, norm_zero]
        exact mul_nonneg (mul_nonneg (by positivity) hJ0) hl
      have h4 := h3 v
      rw [mul_zero, add_zero, add_zero, ← waveExt_of_mem hy1] at h4
      exact h4.trans (mul_le_mul_of_nonneg_right key (add_nonneg (norm_nonneg _) (norm_nonneg _)))

/-- **The rate of `scaled` is given by its inner-product defect**: from the comparison initial
value (the modified elliptic projection `Rₙ (x, 𝐝 x)` of `ofComplexCore`),
`‖e^{tL} x - iₙ e^{tLₙ} Rₙ x‖ ≤ (C + C_ι C' t) (cₙ² - 1) (‖x‖ + ‖L x‖ + ‖L² x‖)` on `[0, T]`. -/
theorem scaled_rate (T : ℝ) (x : PiLp 2 (W3 𝕜 𝕜 PUnit)) (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖(idComplex 𝕜).waveGroup.S t x - (ofComplex (scaled 𝕜 Q hQ)).sol n
        (((ofComplexCore (scaled 𝕜 Q hQ)).cmp T).p x n 0) t‖ ≤
      ((scaledRate Q hQ T).C + ‖(ofComplex (scaled 𝕜 Q hQ)).incl n‖ *
        (scaledRate Q hQ T).C' * t) * ((perturbScale n ^ 2 - 1) * l2Norm x) := by
  have h := dissipFEEC_rate _ (scaledRate Q hQ T) (Set.mem_univ x) n
    ((scaledRate Q hQ T).p x n 0) ht
  rw [ApproxFEEC.S_apply _ ht.1, sub_self, norm_zero, mul_zero, add_zero] at h
  have hp : (scaledRate Q hQ T).p x n 0 = ((ofComplexCore (scaled 𝕜 Q hQ)).cmp T).p x n 0 :=
    ofComplexCrimeCore_toCrime_p (scaled 𝕜 Q hQ) T (mem_idComplex_domainSq x) n 0
  rw [hp] at h
  refine h.trans_eq ?_
  change _ * ((perturbScale n ^ 2 - 1) ^ (1 : ℝ) * l2Norm x) = _
  rw [Real.rpow_one]
  rfl


/-! ### Distinct orders: an inner-product defect `O(h)` with a cochain defect `O(h²)` -/

/-- The scale `bₙ = cₙ + hₙ²` of the differential of `mixedFamily`. -/
abbrev mc (n : ℕ) : 𝕜 := ((perturbScale n + perturbMesh n ^ 2 : ℝ) : 𝕜)

theorem mc_sub_sc (n : ℕ) : mc (𝕜 := 𝕜) n - sc n = ((perturbMesh n ^ 2 : ℝ) : 𝕜) := by
  push_cast; ring

theorem norm_mc_le (n : ℕ) : ‖mc (𝕜 := 𝕜) n‖ ≤ 3 := by
  have h1 := perturbMesh_pos n
  have h2 := perturbMesh_le_one n
  rw [RCLike.norm_ofReal, abs_of_pos (by unfold perturbScale; positivity)]
  unfold perturbScale; nlinarith

variable (𝕜) in
/-- **Discrete differential spaces with both crimes, at different orders** for
`𝕜 --id--> 𝕜 → 0`: at level `n`, `Xₙ = 𝕜 × 𝕜 × 0` with the differential `𝐝ₙ = bₙ·d`,
`bₙ = cₙ + hₙ²`, read in `W` by the non-isometric `iₙ = diag(cₙ, 1, 1)` of `scaledFamily`
(`cₙ = 1 + hₙ`, `hₙ = 1/(n+1)`). The inner-product defect is `cₙ² - 1 = O(hₙ)`, the cochain defect
`(bₙ - cₙ) = hₙ²`. -/
abbrev mixedFamily : ApproxComplexCrime.Family (idComplex 𝕜) ℕ where
  X _ := PiLp 2 (W3 𝕜 𝕜 PUnit)
  D n := (scaledShort 𝕜 (mc n)).toHilbertComplex.totalDL
  D_D n v := (scaledShort 𝕜 (mc n)).toHilbertComplex.totalDL_totalDL v
  incl n := (scaledFamily 𝕜).inclL n
  proj n := (scaledFamily 𝕜).projL n
  proj_incl n v := (scaledFamily 𝕜).projL_inclL n v
  bound := (scaledFamily 𝕜).toCrimeFamily.bound

theorem c0_mixed_D (n : ℕ) (u : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    c0 ((mixedFamily 𝕜).D n u) = 0 := by
  set E := (scaledShort 𝕜 (mc n)).toHilbertComplex
  change (E.totalDL u) 0 = 0
  rw [totalDL_apply _ u (E.mem_totalD_domain_of_finiteDimensional u), totalD_apply,
    Fin.sum_univ_three]
  simp only [apply_eq_zero_of_eq_zero (show E.d 0 0 = 0 from rfl),
    apply_eq_zero_of_eq_zero (show E.d 1 0 = 0 from rfl),
    apply_eq_zero_of_eq_zero (show E.d 2 0 = 0 from rfl), add_zero]

theorem c1_mixed_D (n : ℕ) (u : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    c1 ((mixedFamily 𝕜).D n u) = mc n * c0 u := by
  set E := (scaledShort 𝕜 (mc n)).toHilbertComplex
  change (E.totalDL u) 1 = _
  rw [totalDL_apply _ u (E.mem_totalD_domain_of_finiteDimensional u), totalD_apply,
    Fin.sum_univ_three]
  simp only [apply_eq_zero_of_eq_zero (show E.d 1 1 = 0 from rfl),
    apply_eq_zero_of_eq_zero (show E.d 2 1 = 0 from rfl), add_zero]
  rfl

/-- `‖𝐝ₙ u‖ ≤ 3 ‖u‖`. -/
theorem norm_mixed_D_le (n : ℕ) (u : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    ‖(mixedFamily 𝕜).D n u‖ ≤ 3 * ‖u‖ := by
  have e : (mixedFamily 𝕜).D n u = vec3 0 (mc n * c0 u) :=
    ext3 (c0_mixed_D n u) (c1_mixed_D n u)
  rw [e, norm_vec3_zero, norm_mul]
  exact mul_le_mul (norm_mc_le n) (norm_c0_le u) (norm_nonneg _) (by norm_num)

/-- The inner-product defect of `mixedFamily` is that of `scaledFamily`: `‖1 - Jₙ‖ ≤ cₙ² - 1`. -/
theorem mixed_innerDefect_le (n : ℕ) :
    ‖1 - (mixedFamily 𝕜).J n‖ ≤ perturbScale n ^ 2 - 1 := scaled_innerDefect_le n

/-- **The inner-product defect is nonzero at every level** (`iₙ` is not isometric). -/
theorem mixed_innerDefect_pos (n : ℕ) : 0 < ‖1 - (mixedFamily 𝕜).J n‖ := scaled_innerDefect_pos n

/-- **The inner-product defect is `O(hₙ)`**: `‖1 - Jₙ‖ ≤ 3 hₙ`. -/
theorem mixed_innerDefect_le_mesh (n : ℕ) : ‖1 - (mixedFamily 𝕜).J n‖ ≤ 3 * perturbMesh n := by
  refine (mixed_innerDefect_le n).trans ?_
  have h1 := perturbMesh_pos n
  have h2 := perturbMesh_le_one n
  unfold perturbScale; nlinarith

/-- `iₙ 𝐝ₙ v - 𝐝 iₙ v = (0, hₙ² v₀, 0)`. -/
theorem mixed_incl_D_sub (n : ℕ) (v : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    (mixedFamily 𝕜).incl n ((mixedFamily 𝕜).D n v) -
        (idComplex 𝕜).totalD ⟨_, mem_idComplex_totalD_domain ((mixedFamily 𝕜).incl n v)⟩ =
      vec3 0 (((perturbMesh n ^ 2 : ℝ) : 𝕜) * c0 v) := by
  refine ext3 ?_ ?_
  · change c0 ((scaledFamily 𝕜).inclL n ((mixedFamily 𝕜).D n v)) -
      c0 ((idComplex 𝕜).totalD _) = 0
    rw [c0_scaled_inclL, c0_mixed_D, c0_idTotalD, mul_zero, sub_zero]
  · change c1 ((scaledFamily 𝕜).inclL n ((mixedFamily 𝕜).D n v)) -
      c1 ((idComplex 𝕜).totalD _) = _
    rw [c1_scaled_inclL, c1_mixed_D, c1_idTotalD, c1_vec3]
    change mc n * c0 v - c0 ((scaledFamily 𝕜).inclL n v) = _
    rw [c0_scaled_inclL, ← mc_sub_sc]
    ring

/-- **The cochain defect** `⟪κₙ(y), v⟫ = hₙ² ȳ₁ v₀`. -/
theorem inner_mixed_cochainDefect (n : ℕ) (y : (idComplex 𝕜).wave.domain)
    (v : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    ⟪(mixedFamily 𝕜).cochainDefect n y, v⟫_𝕜 =
      starRingEnd 𝕜 (c1 (y : PiLp 2 (W3 𝕜 𝕜 PUnit))) * (((perturbMesh n ^ 2 : ℝ) : 𝕜) * c0 v) := by
  rw [(mixedFamily 𝕜).inner_cochainDefect_of_mem n y v
    (mem_idComplex_totalD_domain ((mixedFamily 𝕜).incl n v)), mixed_incl_D_sub, inner_W3,
    c0_vec3, c1_vec3, mul_zero, zero_add]

/-- **The cochain defect is exactly of order `hₙ²`**: `⟪κₙ(0, 1, 0), (1, 0, 0)⟫ = hₙ²`, in
particular nonzero at every level. -/
theorem inner_mixed_cochainDefect_secondDatum (n : ℕ) :
    ⟪(mixedFamily 𝕜).cochainDefect n ⟨secondDatum 𝕜, mem_idComplex_wave_domain _⟩,
      firstDatum 𝕜⟫_𝕜 = ((perturbMesh n ^ 2 : ℝ) : 𝕜) := by
  rw [inner_mixed_cochainDefect]
  change starRingEnd 𝕜 1 * (_ * 1) = _
  rw [map_one, one_mul, mul_one]

theorem mixed_cochainDefect_ne_zero (n : ℕ) :
    (mixedFamily 𝕜).cochainDefect n ⟨secondDatum 𝕜, mem_idComplex_wave_domain _⟩ ≠ 0 :=
  fun h => by
    have e := inner_mixed_cochainDefect_secondDatum (𝕜 := 𝕜) n
    rw [h, inner_zero_left] at e
    have hm := perturbMesh_pos n
    have : (perturbMesh n ^ 2 : ℝ) = 0 := by exact_mod_cast e.symm
    exact (pow_pos hm 2).ne' this

/-- **The cochain defect is at most `hₙ² ‖y‖`** in the dual discrete graph norm. -/
theorem norm_inner_mixed_cochainDefect_le (n : ℕ) (y : (idComplex 𝕜).wave.domain)
    (v : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    ‖⟪(mixedFamily 𝕜).cochainDefect n y, v⟫_𝕜‖ ≤
      perturbMesh n ^ 2 * ‖(y : PiLp 2 (W3 𝕜 𝕜 PUnit))‖ * (‖v‖ + ‖(mixedFamily 𝕜).D n v‖) := by
  rw [inner_mixed_cochainDefect, norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_ofReal,
    abs_of_nonneg (by positivity)]
  have h1 := norm_c1_le (y : PiLp 2 (W3 𝕜 𝕜 PUnit))
  have h2 := norm_c0_le v
  have hm : 0 ≤ perturbMesh n ^ 2 := by positivity
  have := norm_nonneg ((mixedFamily 𝕜).D n v)
  calc _ ≤ ‖(y : PiLp 2 (W3 𝕜 𝕜 PUnit))‖ * (perturbMesh n ^ 2 * ‖v‖) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 hm) (by positivity) (norm_nonneg _)
    _ ≤ _ := by
      have hh := mul_nonneg (mul_nonneg hm (norm_nonneg (y : PiLp 2 (W3 𝕜 𝕜 PUnit)))) this
      nlinarith [hh]

/-- `iₙ πₙ = 1`. -/
theorem mixed_incl_proj (n : ℕ) (y : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    (mixedFamily 𝕜).incl n ((mixedFamily 𝕜).proj n y) = y :=
  PiLp.ext fun i => scaleMap_scaleMap (sc_mul_inv n) i _

/-- **The graph-norm error of `w = πₙ y` is at most `hₙ² ‖y‖`**:
`𝐝 y - iₙ 𝐝ₙ πₙ y = (0, (1 - bₙ/cₙ) y₀, 0)` and `|1 - bₙ/cₙ| = hₙ²/cₙ ≤ hₙ²`. -/
theorem norm_idTotalD_sub_mixed_le (n : ℕ) (y : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    ‖(idComplex 𝕜).totalD ⟨y, mem_idComplex_totalD_domain y⟩ -
      (mixedFamily 𝕜).incl n ((mixedFamily 𝕜).D n ((mixedFamily 𝕜).proj n y))‖ ≤
        perturbMesh n ^ 2 * ‖y‖ := by
  have hc0 : c0 ((mixedFamily 𝕜).proj n y) = (sc n)⁻¹ * c0 y := rfl
  have e : (idComplex 𝕜).totalD ⟨y, mem_idComplex_totalD_domain y⟩ -
      (mixedFamily 𝕜).incl n ((mixedFamily 𝕜).D n ((mixedFamily 𝕜).proj n y)) =
        vec3 0 (-((sc n)⁻¹ * ((perturbMesh n ^ 2 : ℝ) : 𝕜)) * c0 y) := by
    refine ext3 ?_ ?_
    · change c0 ((idComplex 𝕜).totalD _) -
        c0 ((scaledFamily 𝕜).inclL n ((mixedFamily 𝕜).D n ((mixedFamily 𝕜).proj n y))) = 0
      rw [c0_idTotalD, c0_scaled_inclL, c0_mixed_D, mul_zero, sub_zero]
    · change c1 ((idComplex 𝕜).totalD _) -
        c1 ((scaledFamily 𝕜).inclL n ((mixedFamily 𝕜).D n ((mixedFamily 𝕜).proj n y))) = _
      rw [c1_idTotalD, c1_scaled_inclL, c1_mixed_D, hc0, c1_vec3]
      change c0 y - mc n * ((sc n)⁻¹ * c0 y) = _
      have hs : sc (𝕜 := 𝕜) n ≠ 0 := perturbScale_ne_zero n
      rw [show mc (𝕜 := 𝕜) n = sc n + ((perturbMesh n ^ 2 : ℝ) : 𝕜) by
        rw [← mc_sub_sc]; ring]
      field_simp
      ring
  rw [e, norm_vec3_zero, norm_mul, norm_neg, norm_mul, norm_inv, RCLike.norm_ofReal,
    RCLike.norm_ofReal, abs_of_pos (perturbScale_pos n), abs_of_nonneg (by positivity)]
  have hi : (perturbScale n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_lt_perturbScale n).le
  have hm : 0 ≤ perturbMesh n ^ 2 := by positivity
  have hpi : 0 ≤ (perturbScale n)⁻¹ := inv_nonneg.2 (perturbScale_pos n).le
  calc (perturbScale n)⁻¹ * perturbMesh n ^ 2 * ‖c0 y‖ ≤ 1 * perturbMesh n ^ 2 * ‖y‖ :=
        mul_le_mul (mul_le_mul_of_nonneg_right hi hm) (norm_c0_le y) (norm_nonneg _)
          (by positivity)
    _ = _ := by ring

theorem tendsto_perturbMesh_sq_mul (a : ℝ) :
    Tendsto (fun n => perturbMesh n ^ 2 * a) atTop (𝓝 0) := by
  simpa using (tendsto_perturbMesh.pow 2).mul_const a

variable (𝕜) in
/-- **The approximating family with both crimes** (constraint `K`), through
`ApproxComplexCrime.ofCochainDefect`: graph-norm approximation by `w = πₙ y` (error `hₙ² ‖y‖`),
cochain defect `≤ hₙ² ‖y‖`, inner-product defect `‖1 - Jₙ‖ ≤ cₙ² - 1 → 0`. -/
abbrev mixed (K : Submodule 𝕜 (PiLp 2 (W3 𝕜 𝕜 PUnit)))
    (hK : IsClosed (K : Set (PiLp 2 (W3 𝕜 𝕜 PUnit)))) : ApproxComplexCrime (idComplex 𝕜) ℕ :=
  ofCochainDefect (mixedFamily 𝕜) K hK atTop (idComplex 𝕜).wave.domain (fun _ hy => hy)
    (idComplex 𝕜).wave.domainSq le_rfl
    (fun x _ t _ => ⟨mem_idComplex_wave_domain _, mem_idComplex_wave_domain _⟩)
    (scaled 𝕜 K hK).tendsto_innerDefect
    (fun y _ ε hε => by
      have hev := (tendsto_perturbMesh_sq_mul ‖y‖).eventually (gt_mem_nhds hε)
      filter_upwards [hev] with n hn
      refine ⟨(mixedFamily 𝕜).proj n y, ?_⟩
      rw [mixed_incl_proj, sub_self, norm_zero, zero_add]
      exact (norm_idTotalD_sub_mixed_le n y).trans_lt hn)
    (fun y hy ε hε => by
      have hev := (tendsto_perturbMesh_sq_mul ‖y‖).eventually (gt_mem_nhds hε)
      filter_upwards [hev] with n hn v
      refine (norm_inner_mixed_cochainDefect_le n ⟨y, hy⟩ v).trans ?_
      exact mul_le_mul_of_nonneg_right hn.le (by positivity))

/-- **The rate class of `mixed` at order `min(2, 1, 2) = 1`**, through
`ApproxComplexCrime.rateClass_of_split`: mesh size `hₙ = 1/(n+1)`, class norm
`‖x‖ + ‖L x‖ + ‖L² x‖`, graph-norm best approximation `O(hₙ²)` (`Cₐ = 1`, approximant `πₙ y` of
discrete graph norm `≤ 4 C_ι ‖y‖`), inner-product defect `O(hₙ)` (`C_β = 3`), cochain defect
`O(hₙ²)` (`C_γ = 1`). -/
def mixedRate (T : ℝ) : (ofComplexCrime (mixed 𝕜 Q hQ)).RateClass T :=
  (mixed 𝕜 Q hQ).rateClass_of_split T Set.univ (fun x _ => mem_idComplex_domainSq x) l2Norm
    perturbMesh 2 1 2 1 (4 * (mixedFamily 𝕜).boundConst) 3 1
    (fun n => (perturbMesh_pos n).le) perturbMesh_le_one (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by positivity [(mixedFamily 𝕜).boundConst_nonneg])
    (by norm_num) (by norm_num) (fun x _ => by unfold l2Norm; positivity)
    (fun n => by rw [Real.rpow_one]; exact mixed_innerDefect_le_mesh n)
    fun x _ n t _ y hy hyD => by
      set S := mixedFamily 𝕜
      have hC := S.boundConst_nonneg
      have hyx := norm_le_l2Norm_of_mem hy
      have hnorm : ‖y‖ ≤ l2Norm x := by linarith [norm_nonneg (waveExt (idComplex 𝕜) y)]
      have hm : 0 ≤ perturbMesh n ^ 2 := by positivity
      rw [Real.rpow_two]
      refine ⟨S.proj n y, ?_, ?_, fun v => ?_⟩
      · change ‖y - S.incl n (S.proj n y)‖ + ‖(idComplex 𝕜).totalD ⟨y, _⟩ -
          S.incl n (S.D n (S.proj n y))‖ ≤ _
        rw [mixed_incl_proj, sub_self, norm_zero, zero_add, one_mul]
        exact (norm_idTotalD_sub_mixed_le n y).trans (mul_le_mul_of_nonneg_left hnorm hm)
      · have h1 : ‖S.proj n y‖ ≤ S.boundConst * ‖y‖ :=
          ((S.proj n).le_opNorm y).trans
            (mul_le_mul_of_nonneg_right (S.norm_proj_le n) (norm_nonneg _))
        have h2 := norm_mixed_D_le n (S.proj n y)
        have h3 := mul_le_mul_of_nonneg_left hnorm hC
        change ‖S.proj n y‖ + ‖S.D n (S.proj n y)‖ ≤ _
        nlinarith [norm_nonneg (S.proj n y)]
      · refine (norm_inner_mixed_cochainDefect_le n ⟨y, hyD⟩ v).trans ?_
        rw [one_mul]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm hm)
          (add_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The order of `mixedRate` is `min(2, 1, 2) = 1`: the inner-product defect is the binding
crime. -/
theorem mixedRate_α (T : ℝ) : (mixedRate Q hQ T).α = 1 := by
  change min (2 : ℝ) (min 1 2) = 1; norm_num

/-- **The rate of `mixed`**: from the comparison initial value `Rₙ x`,
`‖e^{tL} x - iₙ e^{tLₙ} Rₙ x‖ ≤ (C + C_ι C' t) hₙ (‖x‖ + ‖L x‖ + ‖L² x‖)` on `[0, T]`, with
`C = (1 + 8 C_ι) (2 + 13 C_ι)` (`rateClass_of_split_C` with `Cₐ = 1`, `C_w = 4 C_ι`, `C_β = 3`,
`C_γ = 1`). -/
theorem mixed_rate (T : ℝ) (x : PiLp 2 (W3 𝕜 𝕜 PUnit)) (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖(idComplex 𝕜).waveGroup.S t x - (ofComplexCrime (mixed 𝕜 Q hQ)).sol n
        ((mixedRate Q hQ T).p x n 0) t‖ ≤
      ((mixedRate Q hQ T).C + (mixedFamily 𝕜).boundConst * (mixedRate Q hQ T).C' * t) *
        (perturbMesh n * l2Norm x) := by
  have h := (mixed 𝕜 Q hQ).error_le_of_rateClass (mixedRate Q hQ T) (Set.mem_univ x) n ht
  rw [mixedRate_α, Real.rpow_one] at h
  exact h

/-- **Non-vacuity of `rateClass_of_split` with distinct orders.** On `𝕜 --id--> 𝕜 → 0`, the
family `mixed` (differential `bₙ·d`, `bₙ = cₙ + hₙ²`, reading map `diag(cₙ, 1, 1)`) satisfies: the
approximating FEEC theorem with every core hypothesis derived; a positive inner-product defect
`≤ 3 hₙ`; a cochain defect of exact order `hₙ²` at `(0, 1, 0)`; and the rate class of order
`min(2, 1, 2) = 1` with error `O(hₙ)`. -/
theorem mixed_nonvacuous :
    (ofComplexCrime (mixed 𝕜 Q hQ)).Verdict (ofComplexCrimeCore (mixed 𝕜 Q hQ)) ∧
    (∀ n, 0 < ‖1 - (mixedFamily 𝕜).J n‖ ∧ ‖1 - (mixedFamily 𝕜).J n‖ ≤ 3 * perturbMesh n) ∧
    (∀ n, ⟪(mixedFamily 𝕜).cochainDefect n ⟨secondDatum 𝕜, mem_idComplex_wave_domain _⟩,
      firstDatum 𝕜⟫_𝕜 = ((perturbMesh n ^ 2 : ℝ) : 𝕜)) ∧
    (∀ T, (mixedRate Q hQ T).α = 1) ∧
    (∀ T x n, ∀ t ∈ Icc 0 T, ‖(idComplex 𝕜).waveGroup.S t x -
      (ofComplexCrime (mixed 𝕜 Q hQ)).sol n ((mixedRate Q hQ T).p x n 0) t‖ ≤
        ((mixedRate Q hQ T).C + (mixedFamily 𝕜).boundConst * (mixedRate Q hQ T).C' * t) *
          (perturbMesh n * l2Norm x)) :=
  ⟨(approxFEEC_ofComplexCrime _).1, fun n => ⟨mixed_innerDefect_pos n, mixed_innerDefect_le_mesh n⟩,
    inner_mixed_cochainDefect_secondDatum, mixedRate_α Q hQ,
    fun T x n _ ht => mixed_rate Q hQ T x n ht⟩

end ApproxComplexCrime

end Feec.HilbertComplex
