module

public import Feec.HilbertComplex.Approximation.ApproxComplex
public import Feec.HilbertComplex.Approximation.ApproxFEECWitness

/-!
# Non-vacuity of `ApproxFEEC.ofComplex`: a non-conforming discrete complex

On the complex `𝕜 --id--> 𝕜 → 0` (`Feec.HilbertComplex.ConstrainedFEEC.idComplex`), the
approximating family `Feec.HilbertComplex.ApproxComplex.scaled` has, at level `n` with
`cₙ = 1 + 1/(n+1)`,

* the discrete complex `𝕜 --cₙ·id--> 𝕜 → 0` (`scaledShort`), with the standard inner product;
* the cochain map `iₙ = diag(cₙ, 1, 1)` (`𝐝 iₙ = iₙ 𝐝ₙ`), not isometric and not a multiple of the
  identity, with `πₙ = diag(cₙ⁻¹, 1, 1) = iₙ⁻¹`, which commutes with `𝐝`: the graph-norm
  approximation is exact (`scaled_graphIncl_projL`).

`iₙ` is a cochain isomorphism onto `W` (so `𝐝ₙ = cₙ·id` is `𝐝` in other coordinates): the
variational crime is the **inner product** alone, in the sense of [HolstStern2012], §3:
`Jₙ = iₙ* iₙ = diag(cₙ², 1, 1)` and the inner-product defect satisfies
`0 < ‖1 - Jₙ‖ ≤ cₙ² - 1 → 0` (`scaled_innerDefect_pos`, `scaled_innerDefect_le`). Through
`Feec.HilbertComplex.ApproxFEEC.ofComplex`, the approximating FEEC theorem applies, the consistency
defect of the comparison (the modified elliptic projection of the exact orbit) is nonzero along
`(1, 0, 0)` at every level (`scaled_defect_ne_zero`), and the scheme is inexact
(`scaled_exists_sol_ne`); the bundle is `scaled_nonvacuous`. The defect is not assumed: it is
derived by `ofComplexCore` from the inner-product defect and the approximation property.

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3 (an inner-product crime: cochain maps that are not isometric)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap Metric

@[expose] public noncomputable section

namespace Feec.HilbertComplex

namespace ApproxComplex

open ConstrainedFEEC ShortHilbertComplex ApproxFEEC

variable {𝕜 : Type*} [RCLike 𝕜]

variable (𝕜) in
/-- The short complex `𝕜 --a·id--> 𝕜 → 0`. -/
def scaledShort (a : 𝕜) : ShortHilbertComplex 𝕜 𝕜 𝕜 PUnit :=
  ShortHilbertComplex.ofOp (((a • ContinuousLinearMap.id 𝕜 𝕜 : 𝕜 →L[𝕜] 𝕜) : 𝕜 →ₗ[𝕜] 𝕜).toPMap ⊤)
    (by simp [dense_univ]) (a • ContinuousLinearMap.id 𝕜 𝕜).isClosed_toPMap_top

variable (𝕜) in
/-- The degreewise map `diag(a, 1, 1)` on `𝕜 × 𝕜 × 0`. -/
def scaleMap (a : 𝕜) : ∀ i : Fin 3, W3 𝕜 𝕜 PUnit i →L[𝕜] W3 𝕜 𝕜 PUnit i
  | 0 => a • ContinuousLinearMap.id 𝕜 𝕜
  | 1 => ContinuousLinearMap.id 𝕜 𝕜
  | 2 => ContinuousLinearMap.id 𝕜 PUnit

theorem norm_scaleMap_le (a : 𝕜) (i : Fin 3) : ‖scaleMap 𝕜 a i‖ ≤ max ‖a‖ 1 := by
  fin_cases i
  · exact (norm_smul_le _ _).trans (by
      have := ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := 𝕜)
      have ha := norm_nonneg a
      calc ‖a‖ * ‖ContinuousLinearMap.id 𝕜 𝕜‖ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left this ha
        _ ≤ _ := by rw [mul_one]; exact le_max_left _ _)
  · exact (ContinuousLinearMap.norm_id_le).trans (le_max_right _ _)
  · exact (ContinuousLinearMap.norm_id_le).trans (le_max_right _ _)

theorem scaleMap_scaleMap {a b : 𝕜} (hab : a * b = 1) (i : Fin 3) (x : W3 𝕜 𝕜 PUnit i) :
    scaleMap 𝕜 a i (scaleMap 𝕜 b i x) = x := by
  fin_cases i
  · change a • b • (x : 𝕜) = x
    rw [smul_smul, hab, one_smul]
  · rfl
  · rfl

/-- The scale `cₙ = 1 + hₙ` as a scalar. -/
abbrev sc (n : ℕ) : 𝕜 := (perturbScale n : 𝕜)

theorem sc_mul_inv (n : ℕ) : sc (𝕜 := 𝕜) n * (sc n)⁻¹ = 1 :=
  mul_inv_cancel₀ (perturbScale_ne_zero n)

theorem inv_mul_sc (n : ℕ) : (sc (𝕜 := 𝕜) n)⁻¹ * sc n = 1 :=
  inv_mul_cancel₀ (perturbScale_ne_zero n)

variable (𝕜) in
/-- **A family of discrete complexes with an inner-product crime** for `𝕜 --id--> 𝕜 → 0`: at
level `n`, the discrete complex `𝕜 --cₙ·id--> 𝕜 → 0`, read in `W` through the non-isometric
cochain map `iₙ = diag(cₙ, 1, 1)` (`𝐝 iₙ = iₙ 𝐝ₙ`: `cₙ = 1 · cₙ`), with `πₙ = diag(cₙ⁻¹, 1, 1)`. -/
abbrev scaledFamily : ApproxComplex.Family (idComplex 𝕜) ℕ where
  V _ := W3 𝕜 𝕜 PUnit
  cpx n := (scaledShort 𝕜 (sc n)).toHilbertComplex
  incl n := scaleMap 𝕜 (sc n)
  incl_mem _ i j _ := by rw [idComplex_domain]; trivial
  incl_d n i j v := by
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | exact (apply_eq_zero_of_eq_zero rfl _).trans
          ((congrArg _ (apply_eq_zero_of_eq_zero rfl _)).trans (_root_.map_zero _)).symm
  proj n := scaleMap 𝕜 (sc n)⁻¹
  proj_incl n i v := scaleMap_scaleMap (inv_mul_sc n) i v
  bound := ⟨2, fun n i => by
    have h1 := one_lt_perturbScale n
    have h2 : perturbScale n ≤ 2 := by unfold perturbScale; linarith [perturbMesh_le_one n]
    have hi : (perturbScale n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1.le
    have hc := perturbScale_pos n
    constructor
    · refine (norm_scaleMap_le _ i).trans (max_le ?_ (by norm_num))
      rw [RCLike.norm_ofReal, abs_of_pos hc]; exact h2
    · refine (norm_scaleMap_le _ i).trans (max_le ?_ (by norm_num))
      rw [norm_inv, RCLike.norm_ofReal, abs_of_pos hc]; linarith⟩

/-- The degree-`0` component of a point of `𝕜 × 𝕜 × 0`, in `𝕜`. -/
abbrev c0 (u : PiLp 2 (W3 𝕜 𝕜 PUnit)) : 𝕜 := u 0

/-- The degree-`1` component of a point of `𝕜 × 𝕜 × 0`, in `𝕜`. -/
abbrev c1 (u : PiLp 2 (W3 𝕜 𝕜 PUnit)) : 𝕜 := u 1

/-- The point `(a, b, 0)`. -/
def vec3 (a b : 𝕜) : PiLp 2 (W3 𝕜 𝕜 PUnit) :=
  WithLp.toLp 2 fun i => match i with
    | 0 => a
    | 1 => b
    | 2 => PUnit.unit

omit [RCLike 𝕜] in
@[simp] theorem c0_vec3 (a b : 𝕜) : c0 (vec3 a b) = a := rfl

omit [RCLike 𝕜] in
@[simp] theorem c1_vec3 (a b : 𝕜) : c1 (vec3 a b) = b := rfl

omit [RCLike 𝕜] in
theorem ext3 {u w : PiLp 2 (W3 𝕜 𝕜 PUnit)} (h0 : c0 u = c0 w) (h1 : c1 u = c1 w) : u = w :=
  PiLp.ext fun i => by fin_cases i; exacts [h0, h1, rfl]

theorem inner_W3 (u w : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    ⟪u, w⟫_𝕜 = starRingEnd 𝕜 (c0 u) * c0 w + starRingEnd 𝕜 (c1 u) * c1 w := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  have h2 : ⟪u 2, w 2⟫_𝕜 = 0 := rfl
  rw [h2, add_zero]
  change ⟪c0 u, c0 w⟫_𝕜 + ⟪c1 u, c1 w⟫_𝕜 = _
  rw [RCLike.inner_apply', RCLike.inner_apply']

theorem norm_W3_le (u : PiLp 2 (W3 𝕜 𝕜 PUnit)) {C : ℝ} (hC : 0 ≤ C) (v : PiLp 2 (W3 𝕜 𝕜 PUnit))
    (h0 : ‖c0 u‖ ≤ C * ‖c0 v‖) (h1 : ‖c1 u‖ ≤ C * ‖c1 v‖) : ‖u‖ ≤ C * ‖v‖ := by
  refine norm_piLp_le_of_le hC fun i => ?_
  fin_cases i
  · exact h0
  · exact h1
  · exact (show ‖(u 2 : PUnit)‖ = 0 from norm_zero).trans_le (mul_nonneg hC (norm_nonneg _))

theorem sc_conj (n : ℕ) : starRingEnd 𝕜 (sc (𝕜 := 𝕜) n) = sc n := RCLike.conj_ofReal _

theorem one_lt_norm_sc (n : ℕ) : 1 < ‖sc (𝕜 := 𝕜) n‖ := by
  rw [RCLike.norm_ofReal, abs_of_pos (perturbScale_pos n)]; exact one_lt_perturbScale n

theorem sc_sq_ne_one (n : ℕ) : sc (𝕜 := 𝕜) n ^ 2 ≠ 1 := fun h => by
  have := congrArg norm h
  rw [norm_pow, norm_one] at this
  nlinarith [one_lt_norm_sc (𝕜 := 𝕜) n]

/-- `iₙ` on components: `(iₙ v)₀ = cₙ v₀`, `(iₙ v)₁ = v₁`. -/
theorem c0_scaled_inclL (n : ℕ) (v : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    c0 ((scaledFamily 𝕜).inclL n v) = sc n * c0 v := rfl

theorem c1_scaled_inclL (n : ℕ) (v : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    c1 ((scaledFamily 𝕜).inclL n v) = c1 v := rfl

/-- `Jₙ = diag(cₙ², 1, 1)`. -/
theorem inner_scaled_J (n : ℕ) (v w : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    ⟪(scaledFamily 𝕜).J n v, w⟫_𝕜 =
      sc n ^ 2 * (starRingEnd 𝕜 (c0 v) * c0 w) + starRingEnd 𝕜 (c1 v) * c1 w := by
  rw [ApproxComplex.Family.inner_J, inner_W3, c0_scaled_inclL, c0_scaled_inclL,
    c1_scaled_inclL, c1_scaled_inclL, map_mul, sc_conj]
  ring

/-- `(1 - Jₙ) v = ((1 - cₙ²) v₀, 0, 0)`. -/
theorem scaled_one_sub_J (n : ℕ) (v : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    (1 - (scaledFamily 𝕜).J n) v = vec3 ((1 - sc n ^ 2) * c0 v) 0 := by
  refine ext_inner_right 𝕜 fun w => ?_
  rw [_root_.sub_apply, one_apply_eq_self, inner_sub_left, inner_scaled_J, inner_W3, inner_W3,
    c0_vec3, c1_vec3, map_mul, _root_.map_sub, _root_.map_one, map_pow, sc_conj,
    _root_.map_zero]
  ring

theorem norm_scaled_one_sub_J_apply_le (n : ℕ) (v : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    ‖(1 - (scaledFamily 𝕜).J n) v‖ ≤ (perturbScale n ^ 2 - 1) * ‖v‖ := by
  have h1 := one_lt_perturbScale n
  have hC : 0 ≤ perturbScale n ^ 2 - 1 := by nlinarith
  rw [scaled_one_sub_J]
  refine norm_W3_le _ hC v ?_ (by rw [c1_vec3, norm_zero]; exact mul_nonneg hC (norm_nonneg _))
  rw [c0_vec3, norm_mul]
  refine mul_le_mul_of_nonneg_right (le_of_eq ?_) (norm_nonneg _)
  rw [show (1 : 𝕜) - sc n ^ 2 = ((1 - perturbScale n ^ 2 : ℝ) : 𝕜) by push_cast; rfl,
    RCLike.norm_ofReal, abs_of_nonpos (by linarith)]
  ring

/-- **The inner-product defect is nonzero at every level**: `‖1 - Jₙ‖ > 0` (`iₙ` is not
isometric). -/
theorem scaled_innerDefect_pos (n : ℕ) : 0 < ‖1 - (scaledFamily 𝕜).J n‖ := by
  refine norm_pos_iff.2 fun h0 => ?_
  have e := congrArg c0 (scaled_one_sub_J (𝕜 := 𝕜) n (firstDatum 𝕜))
  rw [h0, _root_.zero_apply, c0_vec3] at e
  have e1 : c0 (firstDatum 𝕜) = 1 := rfl
  rw [e1, mul_one] at e
  exact sc_sq_ne_one n (sub_eq_zero.1 e.symm).symm

theorem scaled_innerDefect_le (n : ℕ) :
    ‖1 - (scaledFamily 𝕜).J n‖ ≤ perturbScale n ^ 2 - 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by nlinarith [one_lt_perturbScale n])
    (norm_scaled_one_sub_J_apply_le n)

theorem tendsto_perturbScale_sq_sub_one :
    Tendsto (fun n : ℕ => perturbScale n ^ 2 - 1) atTop (𝓝 0) := by
  have hm : Tendsto perturbMesh atTop (𝓝 0) := by
    unfold perturbMesh; exact tendsto_one_div_add_atTop_nhds_zero_nat
  have : Tendsto (fun n : ℕ => 2 * perturbMesh n + perturbMesh n ^ 2) atTop (𝓝 0) := by
    simpa using (hm.const_mul 2).add (hm.pow 2)
  refine this.congr fun n => ?_
  unfold perturbScale; ring

/-- `iₙ πₙ = 1`: the lifts `(iₙ πₙ ζ₁, 𝐝 iₙ πₙ ζ₁)` reproduce every `ζ ∈ Γ(𝐝)` (`πₙ` commutes
with `𝐝`). -/
theorem scaled_graphIncl_projL (n : ℕ) (ζ : (idComplex 𝕜).totalD.GraphSpace) :
    (scaledFamily 𝕜).graphIncl n ((scaledFamily 𝕜).projL n ((idComplex 𝕜).totalD.graphFst ζ)) =
      ζ :=
  (idComplex 𝕜).totalD.graphFst_injective (PiLp.ext fun i =>
    scaleMap_scaleMap (sc_mul_inv n) i _)

variable (𝕜) in
/-- **The non-conforming approximating family**: `scaledFamily` with a closed constraint `K`;
inner-product defect `‖1 - Jₙ‖ ≤ cₙ² - 1 → 0`, exact graph-norm approximation. -/
abbrev scaled (K : Submodule 𝕜 (PiLp 2 (W3 𝕜 𝕜 PUnit)))
    (hK : IsClosed (K : Set (PiLp 2 (W3 𝕜 𝕜 PUnit)))) : ApproxComplex (idComplex 𝕜) ℕ where
  toFamily := scaledFamily 𝕜
  K := K
  isClosed_K := hK
  l := atTop
  tendsto_innerDefect := squeeze_zero (fun _ => norm_nonneg _) scaled_innerDefect_le
    tendsto_perturbScale_sq_sub_one
  graphApprox ζ ε hε := Eventually.of_forall fun n =>
    ⟨(scaledFamily 𝕜).projL n ((idComplex 𝕜).totalD.graphFst ζ), by
      rw [scaled_graphIncl_projL, sub_self, norm_zero]; exact hε⟩

/-! #### Components of the discrete and continuous operators -/

variable (𝕜) in
/-- The datum `(0, 1, 0)`. -/
abbrev secondDatum : PiLp 2 (W3 𝕜 𝕜 PUnit) := vec3 0 1

theorem inner_firstDatum_left (u : PiLp 2 (W3 𝕜 𝕜 PUnit)) : ⟪firstDatum 𝕜, u⟫_𝕜 = c0 u := by
  rw [inner_W3]
  change starRingEnd 𝕜 1 * c0 u + starRingEnd 𝕜 0 * c1 u = _
  simp

theorem inner_secondDatum_right (u : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    ⟪u, secondDatum 𝕜⟫_𝕜 = starRingEnd 𝕜 (c1 u) := by
  rw [inner_W3, c0_vec3, c1_vec3]; simp

theorem c0_scaled_D (n : ℕ) (u : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    c0 ((scaledFamily 𝕜).D n u) = 0 := by
  set E := (scaledShort 𝕜 (sc n)).toHilbertComplex
  change (E.totalDL u) 0 = 0
  rw [totalDL_apply _ u (E.mem_totalD_domain_of_finiteDimensional u), totalD_apply,
    Fin.sum_univ_three]
  simp only [apply_eq_zero_of_eq_zero (show E.d 0 0 = 0 from rfl),
    apply_eq_zero_of_eq_zero (show E.d 1 0 = 0 from rfl),
    apply_eq_zero_of_eq_zero (show E.d 2 0 = 0 from rfl), add_zero]

theorem c1_scaled_D (n : ℕ) (u : PiLp 2 (W3 𝕜 𝕜 PUnit)) :
    c1 ((scaledFamily 𝕜).D n u) = sc n * c0 u := by
  set E := (scaledShort 𝕜 (sc n)).toHilbertComplex
  change (E.totalDL u) 1 = _
  rw [totalDL_apply _ u (E.mem_totalD_domain_of_finiteDimensional u), totalD_apply,
    Fin.sum_univ_three]
  simp only [apply_eq_zero_of_eq_zero (show E.d 1 1 = 0 from rfl),
    apply_eq_zero_of_eq_zero (show E.d 2 1 = 0 from rfl), add_zero]
  rfl

theorem scaled_D_secondDatum (n : ℕ) : (scaledFamily 𝕜).D n (secondDatum 𝕜) = 0 :=
  ext3 (c0_scaled_D n _) ((c1_scaled_D n _).trans (mul_zero (sc n)))

theorem c1_scaled_D_firstDatum (n : ℕ) : c1 ((scaledFamily 𝕜).D n (firstDatum 𝕜)) = sc n :=
  (c1_scaled_D n _).trans (mul_one _)

theorem c1_idWave (y : PiLp 2 (W3 𝕜 𝕜 PUnit)) : c1 (idWave 𝕜 y) = c0 y := by
  have e := (idShort 𝕜).wave_apply_one ⟨y, mem_idComplex_wave_domain y⟩
  have e2 : (idShort 𝕜).d₁† ⟨(y : PiLp 2 (W3 𝕜 𝕜 PUnit)) 2,
      (mem_idComplex_wave_domain y).2 2 1⟩ = 0 :=
    LinearPMap.adjoint_apply_eq_zero_of_eq_zero rfl _
  rw [e2, sub_zero] at e
  exact e

theorem c0_idWave_firstDatum : c0 (idWave 𝕜 (firstDatum 𝕜)) = 0 := by
  have e := (idShort 𝕜).wave_apply_zero ⟨firstDatum 𝕜, mem_idComplex_wave_domain _⟩
  have e2 : (idShort 𝕜).d₀† ⟨(firstDatum 𝕜 : PiLp 2 (W3 𝕜 𝕜 PUnit)) 1,
      (mem_idComplex_wave_domain (firstDatum 𝕜)).2 1 0⟩ = 0 :=
    LinearPMap.apply_mk_eq_zero _ _ rfl
  rw [e2, neg_zero] at e
  exact e

theorem c1_idWave_firstDatum : c1 (idWave 𝕜 (firstDatum 𝕜)) = 1 :=
  (c1_idWave _).trans rfl

theorem scaled_inclL_secondDatum (n : ℕ) :
    (scaledFamily 𝕜).inclL n (secondDatum 𝕜) = secondDatum 𝕜 :=
  ext3 ((c0_scaled_inclL n _).trans (mul_zero (sc n))) (c1_scaled_inclL n _)

theorem scaled_projL_secondDatum (n : ℕ) :
    (scaledFamily 𝕜).projL n (secondDatum 𝕜) = secondDatum 𝕜 :=
  ext3 ((show c0 ((scaledFamily 𝕜).projL n (secondDatum 𝕜)) = (sc n)⁻¹ * 0 from rfl).trans
    (mul_zero _)) rfl

/-! #### The defects are nonzero -/

variable (Q : Submodule 𝕜 (PiLp 2 (W3 𝕜 𝕜 PUnit))) (hQ : IsClosed (Q : Set (PiLp 2 (W3 𝕜 𝕜 PUnit))))

theorem waveOrbit_zero {x : PiLp 2 (W3 𝕜 𝕜 PUnit)} (hx : x ∈ (idComplex 𝕜).wave.domain) :
    waveOrbit (idComplex 𝕜) x 0 = waveLift (idComplex 𝕜) ⟨x, hx⟩ := by
  rw [waveOrbit_of_mem _ hx]
  exact congrArg (waveLift (idComplex 𝕜)) (Subtype.ext (C0Group.S_zero_apply _ _))

/-- **The consistency defect of the comparison (the modified elliptic projection) is nonzero**
along `(1, 0, 0)` at `t = 0`, at every level (if it vanished, `iₙ*` would intertwine `L` and
`Lₙ` on `x - L x`; testing against `(0, 1, 0)` gives `1 = cₙ²`). -/
theorem scaled_defect_ne_zero (T : ℝ) (n : ℕ) :
    ((ofComplexCore (scaled 𝕜 Q hQ)).cmp T).defect (firstDatum 𝕜) n 0 ≠ 0 := by
  set S := scaledFamily 𝕜
  have hx := mem_idComplex_wave_domain (firstDatum 𝕜)
  set y : (idComplex 𝕜).wave.domain := ⟨firstDatum 𝕜, hx⟩
  have hy := mem_idComplex_wave_domain ((idComplex 𝕜).wave y)
  have e : ((ofComplexCore (scaled 𝕜 Q hQ)).cmp T).defect (firstDatum 𝕜) n 0 =
      S.ellProj n (waveLift (idComplex 𝕜) ⟨_, hy⟩) - S.L n (S.ellProj n (waveLift _ y)) := by
    change S.ellProj n (waveOrbit _ (waveExt _ (firstDatum 𝕜)) 0) -
      S.L n (S.ellProj n (waveOrbit _ (firstDatum 𝕜) 0)) = _
    rw [waveOrbit_zero hx]
    rw [waveExt_of_mem hx, waveOrbit_zero hy]
  rw [e]
  intro h00
  have h0 : S.ellProj n (waveLift (idComplex 𝕜) ⟨_, hy⟩) =
      S.L n (S.ellProj n (waveLift _ y)) := sub_eq_zero.1 h00
  have ex := S.ellProj_sub n (waveLift _ y)
  have ey := S.ellProj_sub n (waveLift (idComplex 𝕜) ⟨_, hy⟩)
  rw [S.G_waveLift] at ex ey
  rw [h0] at ey
  have key : (S.inclL n).adjoint ((idComplex 𝕜).wave y - (idComplex 𝕜).wave ⟨_, hy⟩) =
      S.L n ((S.inclL n).adjoint ((y : PiLp 2 (W3 𝕜 𝕜 PUnit)) - (idComplex 𝕜).wave y)) := by
    rw [← ey, ← ex, (S.L n).map_sub]
  have hL : ⟪(S.inclL n).adjoint ((idComplex 𝕜).wave y - (idComplex 𝕜).wave ⟨_, hy⟩),
      secondDatum 𝕜⟫_𝕜 = ⟪S.L n ((S.inclL n).adjoint ((y : PiLp 2 (W3 𝕜 𝕜 PUnit)) -
        (idComplex 𝕜).wave y)), secondDatum 𝕜⟫_𝕜 := by rw [key]
  rw [ContinuousLinearMap.adjoint_inner_left, scaled_inclL_secondDatum, inner_secondDatum_right,
    inner_waveL, scaled_D_secondDatum, inner_zero_right, sub_zero, inner_secondDatum_right,
    c1_scaled_D] at hL
  have h1 : c1 ((idComplex 𝕜).wave y - (idComplex 𝕜).wave ⟨_, hy⟩) = 1 := by
    change c1 (idWave 𝕜 (firstDatum 𝕜)) - c1 (idWave 𝕜 (idWave 𝕜 (firstDatum 𝕜))) = 1
    rw [c1_idWave_firstDatum, c1_idWave, c0_idWave_firstDatum, sub_zero]
  have h2 : c0 ((S.inclL n).adjoint ((y : PiLp 2 (W3 𝕜 𝕜 PUnit)) - (idComplex 𝕜).wave y)) =
      sc n := by
    rw [← inner_firstDatum_left, ContinuousLinearMap.adjoint_inner_right, inner_W3,
      c0_scaled_inclL, c1_scaled_inclL]
    change starRingEnd 𝕜 (sc n * 1) * (1 - c0 (idWave 𝕜 (firstDatum 𝕜))) +
      starRingEnd 𝕜 0 * c1 ((y : PiLp 2 (W3 𝕜 𝕜 PUnit)) - (idComplex 𝕜).wave y) = _
    rw [c0_idWave_firstDatum, _root_.map_zero, zero_mul, add_zero, sub_zero, mul_one, mul_one,
      sc_conj]
  rw [h1, h2, map_mul, sc_conj, map_one] at hL
  exact sc_sq_ne_one (𝕜 := 𝕜) n (by rw [sq]; exact hL.symm)

/-- **The scheme is inexact**: from `πₙ (0, 1, 0)` the discrete solution differs from the exact
one at some time (`(iₙ Lₙ πₙ x)₀ = -cₙ² ≠ -1 = (L x)₀`). -/
theorem scaled_exists_sol_ne (n : ℕ) :
    ∃ t, (ofComplex (scaled 𝕜 Q hQ)).sol n ((ofComplex (scaled 𝕜 Q hQ)).proj n (secondDatum 𝕜))
      t ≠ (idComplex 𝕜).waveGroup.S t (secondDatum 𝕜) := by
  set S := scaledFamily 𝕜
  refine (ofComplex (scaled 𝕜 Q hQ)).exists_sol_ne (mem_idComplex_wave_domain _) n _
    fun he => ?_
  have he0 := congrArg c0 he
  change c0 (S.inclL n (S.L n (S.projL n (secondDatum 𝕜)))) = c0 (idWave 𝕜 (secondDatum 𝕜))
    at he0
  rw [scaled_projL_secondDatum, c0_scaled_inclL] at he0
  have a1 : c0 (S.L n (secondDatum 𝕜)) = -sc n := by
    have sk : ⟪firstDatum 𝕜, S.L n (secondDatum 𝕜)⟫_𝕜 =
        -⟪S.L n (firstDatum 𝕜), secondDatum 𝕜⟫_𝕜 := by
      rw [(S.cpx n).waveL_skew, neg_neg]
    rw [← inner_firstDatum_left, sk, inner_waveL, inner_secondDatum_right, c1_scaled_D_firstDatum, scaled_D_secondDatum,
      inner_zero_right, sub_zero, sc_conj]
  have a2 : c0 (idWave 𝕜 (secondDatum 𝕜)) = -1 := by
    have sk : ⟪firstDatum 𝕜, idWave 𝕜 (secondDatum 𝕜)⟫_𝕜 =
        -⟪idWave 𝕜 (firstDatum 𝕜), secondDatum 𝕜⟫_𝕜 := by
      rw [idWave_skew, neg_neg]
    rw [← inner_firstDatum_left, sk,
      inner_secondDatum_right, c1_idWave_firstDatum, map_one]
  rw [a1, a2, mul_neg, neg_inj, ← sq] at he0
  exact sc_sq_ne_one n he0

/-- **Non-vacuity of `ApproxFEEC.ofComplex` for a genuinely non-conforming discrete complex.**
On `𝕜 --id--> 𝕜 → 0` the family `scaled` (discrete complex `𝕜 --cₙ·id--> 𝕜 → 0`, cochain map
`iₙ = diag(cₙ, 1, 1)`, `cₙ = 1 + 1/(n+1)`) goes through `ofComplex`: the approximating FEEC
theorem applies; the inner-product defect is positive and at most `cₙ² - 1` at every level; the
consistency defect of the comparison along `(1, 0, 0)` is nonzero at every level; the scheme is
inexact. -/
theorem scaled_nonvacuous :
    (ofComplex (scaled 𝕜 Q hQ)).Verdict (ofComplexCore (scaled 𝕜 Q hQ)) ∧
    (∀ n, 0 < ‖1 - (scaledFamily 𝕜).J n‖ ∧ ‖1 - (scaledFamily 𝕜).J n‖ ≤ perturbScale n ^ 2 - 1) ∧
    (∀ T n, 0 < ‖((ofComplexCore (scaled 𝕜 Q hQ)).cmp T).defect (firstDatum 𝕜) n 0‖) ∧
    (∀ n, ∃ t, (ofComplex (scaled 𝕜 Q hQ)).sol n
      ((ofComplex (scaled 𝕜 Q hQ)).proj n (secondDatum 𝕜)) t ≠
        (idComplex 𝕜).waveGroup.S t (secondDatum 𝕜)) :=
  ⟨(approxFEEC_ofComplex _).1, fun n => ⟨scaled_innerDefect_pos n, scaled_innerDefect_le n⟩,
    fun T n => norm_pos_iff.2 (scaled_defect_ne_zero Q hQ T n), scaled_exists_sol_ne Q hQ⟩

end ApproxComplex

end Feec.HilbertComplex
