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
  have h := approxFEEC_rate (ofComplexCrime (shifted 𝕜 Q hQ)) (shiftedRate Q hQ T) (Set.mem_univ x) n
    ((shiftedRate Q hQ T).p x n 0) ht
  rw [sub_self, norm_zero, mul_zero, add_zero] at h
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
  have h := approxFEEC_rate (ofComplexCrime (scaled 𝕜 Q hQ).toCrime) (scaledRate Q hQ T) (Set.mem_univ x) n
    ((scaledRate Q hQ T).p x n 0) ht
  rw [sub_self, norm_zero, mul_zero, add_zero] at h
  have hp : (scaledRate Q hQ T).p x n 0 = ((ofComplexCore (scaled 𝕜 Q hQ)).cmp T).p x n 0 :=
    ofComplexCrimeCore_toCrime_p (scaled 𝕜 Q hQ) T (mem_idComplex_domainSq x) n 0
  rw [hp] at h
  refine h.trans_eq ?_
  change _ * ((perturbScale n ^ 2 - 1) ^ (1 : ℝ) * l2Norm x) = _
  rw [Real.rpow_one]
  rfl

end ApproxComplexCrime

end Feec.HilbertComplex
