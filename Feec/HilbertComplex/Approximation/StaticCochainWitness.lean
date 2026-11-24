module

public import Feec.HilbertComplex.Approximation.StaticCochain
public import Feec.HilbertComplex.Approximation.StaticCrimeWitness
public import Feec.HilbertComplex.ReducedSystem

/-!
# Non-vacuity of the cochain case with harmonic forms

The cochain case of the static theory with crimes
(`Feec.HilbertComplex.Approximation.StaticCochain`) on a complex with **nonzero harmonic forms**,
read by cochain maps that are **not isometric** and do not map the discrete harmonic forms onto
the continuous ones.

* **Shear families** (`ApproxComplexCrime.shearFamily`): on a finite-dimensional complex `E`, with
  a cochain operator `N` (`N 𝐝 = 𝐝 N`) of square `0`, the discrete spaces `Xₙ = W` with
  `𝐝ₙ = 𝐝`, read by `iₙ = 1 + hₙ N` with left inverses `πₙ = 1 - hₙ N`, `hₙ = 1/(n+1)`. The
  reading maps are cochain maps (`shear_isCochain`), the `πₙ` are cochain projections bounded by
  `1 + ‖N‖` (`shearCochainProj`), `iₙ πₙ = 1` (`shear_incl_proj`), and the inner-product defect
  is `‖1 - Jₙ‖ ≤ hₙ ‖N‖ (2 + ‖N‖)` (`norm_one_sub_shear_J_le`). So the uniform discrete Poincaré
  inequality holds, the static errors tend to `0` for every datum (`shear_tendsto_staticError`)
  and the maps on cohomology are eventually isomorphisms
  (`shear_eventually_bijective_cohomologyMap`), and the heat FEEC theorem with crimes applies
  (`shearHeat`, `shear_heat`). With `iₙ πₙ = 1` only the inner-product defect enters the static
  error: the static rate `e(f) ≤ K ‖f‖ hₙ` (`shear_staticError_le`) and the heat rate
  `O(L hₙ)` on the orbits with `‖f‖ ≤ L` regular states (`shear_rate_heat`).
* **The witness** on `𝕜 --id--> 𝕜 --0--> 𝕜` (`idZeroComplex`, `𝐝 (a, b, c) = (0, a, 0)`, harmonic
  forms `ℌ = 𝕜 (0, 0, 1)`, cohomology `≠ 0`) with `N (a, b, c) = (0, c, 0)` (`idZeroN`): `p =
  (0, 0, 1)` is harmonic, continuous and discrete, but `iₙ p = (0, hₙ, 1)` is not harmonic; the
  harmonic gap of `IsCochain.norm_sub_incl_harmonic_le` is `‖p - iₙ P_ℌₙ πₙ p‖ = hₙ > 0` while
  `‖p - iₙ πₙ p‖ = 0`, so the gap is carried by the inner-product term alone (and `Jₙ ≠ 1`); the
  static error at the datum `p` is positive at every level. Summary: `shear_nonvacuous`.

## References

* [M. Holst, A. Stern, *Geometric variational crimes: Hilbert complexes, finite element exterior calculus, and problems on hypersurfaces*][HolstStern2012],
  §3 (Thm 3.3, Cor 3.4, Thm 3.5, Cor 3.11)

Bibliography: [references.bib](../../../docs/references.bib)
-/

open scoped InnerProductSpace
open Set Filter Topology LinearPMap

@[expose] public noncomputable section

namespace Feec.HilbertComplex

namespace ApproxComplexCrime

open ShortHilbertComplex ApproxFEEC

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Shear families -/

section Shear

variable {ι : Type*} [Fintype ι] {c : ComplexShape ι} {V : ι → Type*}
  [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)] [∀ i, CompleteSpace (V i)]
  [∀ i, FiniteDimensional 𝕜 (V i)] [∀ i, NormedSpace ℝ (V i)] [∀ i, IsScalarTower ℝ 𝕜 (V i)]
  (E : HilbertComplex 𝕜 c V) (N : PiLp 2 V →L[𝕜] PiLp 2 V) (hNN : ∀ v, N (N v) = 0)
  (hND : ∀ v, N (E.totalDL v) = E.totalDL (N v))

omit [∀ i, CompleteSpace (V i)] [∀ i, FiniteDimensional 𝕜 (V i)] [∀ i, NormedSpace ℝ (V i)]
  [∀ i, IsScalarTower ℝ 𝕜 (V i)] in
theorem norm_perturbMesh_smul_le (n : ℕ) : ‖(perturbMesh n : 𝕜) • N‖ ≤ ‖N‖ := by
  have hm : ‖((perturbMesh n : ℝ) : 𝕜)‖ ≤ 1 := by
    rw [RCLike.norm_ofReal, abs_of_pos (perturbMesh_pos n)]; exact perturbMesh_le_one n
  calc ‖(perturbMesh n : 𝕜) • N‖ ≤ ‖(perturbMesh n : 𝕜)‖ * ‖N‖ := norm_smul_le (perturbMesh n : 𝕜) N
    _ ≤ 1 * ‖N‖ := mul_le_mul_of_nonneg_right hm (norm_nonneg _)
    _ = ‖N‖ := one_mul _

/-- **The shear family** of a finite-dimensional complex `E` along a cochain operator `N` of square
`0`: `Xₙ = W`, `𝐝ₙ = 𝐝`, read by `iₙ = 1 + hₙ N`, with the left inverses `πₙ = 1 - hₙ N`,
`hₙ = 1/(n+1)`. -/
abbrev shearFamily : ApproxComplexCrime.Family E ℕ where
  X _ := PiLp 2 V
  D _ := E.totalDL
  D_D _ := E.totalDL_totalDL
  incl n := 1 + (perturbMesh n : 𝕜) • N
  proj n := 1 - (perturbMesh n : 𝕜) • N
  proj_incl n v := by
    change v + (perturbMesh n : 𝕜) • N v - (perturbMesh n : 𝕜) • N (v + (perturbMesh n : 𝕜) • N v) =
      v
    rw [_root_.map_add, _root_.map_smul, hNN, smul_zero, add_zero, add_sub_cancel_right]
  bound := ⟨1 + ‖N‖, fun n =>
    ⟨(norm_add_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le
      (norm_perturbMesh_smul_le N n)),
    (norm_sub_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le
      (norm_perturbMesh_smul_le N n))⟩⟩

theorem shear_incl_apply (n : ℕ) (v : PiLp 2 V) :
    (shearFamily E N hNN).incl n v = v + (perturbMesh n : 𝕜) • N v :=
  rfl

theorem shear_proj_apply (n : ℕ) (v : PiLp 2 V) :
    (shearFamily E N hNN).proj n v = v - (perturbMesh n : 𝕜) • N v :=
  rfl

/-- `iₙ πₙ = 1`. -/
theorem shear_incl_proj (n : ℕ) (v : PiLp 2 V) :
    (shearFamily E N hNN).incl n ((shearFamily E N hNN).proj n v) = v := by
  rw [shear_incl_apply, shear_proj_apply, _root_.map_sub, _root_.map_smul, hNN, smul_zero,
    sub_zero, sub_add_cancel]

include hND in
/-- **The reading maps of a shear family are cochain maps.** -/
theorem shear_isCochain : (shearFamily E N hNN).IsCochain :=
  ⟨fun _ _ => E.mem_totalD_domain_of_finiteDimensional _, fun n v => by
    rw [← E.totalDL_apply]
    change E.totalDL (v + (perturbMesh n : 𝕜) • N v) =
      E.totalDL v + (perturbMesh n : 𝕜) • N (E.totalDL v)
    rw [_root_.map_add, _root_.map_smul, hND]⟩

/-- **The cochain projections of a shear family**: `πₙ = 1 - hₙ N`, bounded by `1 + ‖N‖`. -/
def shearCochainProj : (shearFamily E N hNN).CochainProj (1 + ‖N‖) :=
  .ofNormLe (shearFamily E N hNN).proj (shearFamily E N hNN).proj_incl (by positivity)
    (fun n => (norm_sub_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le
      (norm_perturbMesh_smul_le N n))) fun n z => by
    rw [← E.totalDL_apply]
    change E.totalDL z - (perturbMesh n : 𝕜) • N (E.totalDL z) =
      E.totalDL (z - (perturbMesh n : 𝕜) • N z)
    rw [_root_.map_sub, _root_.map_smul, hND]

/-- **The inner-product defect of a shear family**: `‖1 - Jₙ‖ ≤ hₙ ‖N‖ (2 + ‖N‖)`, from
`1 - Jₙ = -(A + A* + A* A)`, `A = hₙ N`. -/
theorem norm_one_sub_shear_J_le (n : ℕ) :
    ‖1 - (shearFamily E N hNN).J n‖ ≤ perturbMesh n * (‖N‖ * (2 + ‖N‖)) := by
  set A := (perturbMesh n : 𝕜) • N
  have e : 1 - (shearFamily E N hNN).J n = -(A + A.adjoint + A.adjoint ∘L A) := by
    change 1 - (1 + A).adjoint ∘L (1 + A) = _
    rw [_root_.map_add, ContinuousLinearMap.adjoint_one]
    ext v
    simp only [_root_.sub_apply, _root_.neg_apply, _root_.add_apply, one_apply_eq_self,
      ContinuousLinearMap.comp_apply, _root_.map_add]
    abel_nf
  have hA : ‖A‖ ≤ perturbMesh n * ‖N‖ := by
    refine (norm_smul_le (perturbMesh n : 𝕜) N).trans_eq ?_
    rw [RCLike.norm_ofReal, abs_of_pos (perturbMesh_pos n)]
  have hA' : ‖A.adjoint‖ = ‖A‖ := ContinuousLinearMap.adjoint.norm_map A
  have hm := perturbMesh_le_one n
  have hm0 := (perturbMesh_pos n).le
  have hN := norm_nonneg N
  rw [e, norm_neg]
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _)
    (ContinuousLinearMap.opNorm_comp_le _ _)).trans ?_)
  rw [hA']
  have hAA : ‖A‖ * ‖A‖ ≤ perturbMesh n * ‖N‖ * ‖N‖ :=
    (mul_le_mul hA hA (norm_nonneg _) (by positivity)).trans
      (by nlinarith [mul_nonneg hm0 hN, mul_nonneg (mul_nonneg hm0 hN) hN])
  nlinarith

theorem shear_tendsto_innerDefect :
    Tendsto (fun n => ‖1 - (shearFamily E N hNN).J n‖) atTop (𝓝 0) :=
  squeeze_zero (fun _ => norm_nonneg _) (norm_one_sub_shear_J_le E N hNN)
    (by simpa using tendsto_perturbMesh.mul_const (‖N‖ * (2 + ‖N‖)))

omit [Fintype ι] [∀ i, NormedSpace ℝ (V i)] [∀ i, IsScalarTower ℝ 𝕜 (V i)] in
/-- A finite-dimensional complex has closed range. -/
theorem closedRangeAt_of_finiteDimensional (i : ι) : E.ClosedRangeAt i :=
  Submodule.closed_of_finiteDimensional _

include hND in
/-- **The uniform discrete Poincaré inequality for a shear family**
(`ApproxComplexCrime.Family.IsCochain.isPoincare`). -/
theorem shear_isPoincare : ∃ cP, 1 ≤ cP ∧ (shearFamily E N hNN).IsPoincare cP := by
  obtain ⟨c₀, hc₀⟩ := E.exists_poincare_totalD (closedRangeAt_of_finiteDimensional E)
  have h := (shear_isCochain E N hNN hND).isPoincare (shearCochainProj E N hNN hND)
    hc₀
  exact ⟨_, le_max_right _ 1, h.mono (le_max_left _ _)⟩

include hND in
/-- **The static errors of a shear family tend to `0` for every datum**
(`ApproxComplexCrime.Family.IsCochain.tendsto_staticError`: `iₙ πₙ = 1`, `‖1 - Jₙ‖ → 0`). -/
theorem shear_tendsto_staticError (f : PiLp 2 V) :
    Tendsto (fun n => (shearFamily E N hNN).staticError
      (closedRangeAt_of_finiteDimensional E) n f) atTop (𝓝 0) :=
  let ⟨_, hcP, hP⟩ := shear_isPoincare E N hNN hND
  (shear_isCochain E N hNN hND).tendsto_staticError _ (shearCochainProj E N hNN hND) hP hcP
    ((shearFamily E N hNN).tendsto_graphDefect_of_tendsto (shear_tendsto_innerDefect E N hNN))
    (fun x _ => tendsto_const_nhds.congr fun n => by
      change (0 : ℝ) = ‖x - (shearFamily E N hNN).incl n
        ((shearFamily E N hNN).proj n x)‖
      rw [shear_incl_proj, sub_self, norm_zero]) f

include hND in
/-- **The maps of a shear family on cohomology are eventually isomorphisms**
(`ApproxComplexCrime.Family.IsCochain.eventually_bijective_cohomologyMap`). -/
theorem shear_eventually_bijective_cohomologyMap :
    ∀ᶠ n in atTop, Function.Bijective ((shearCochainProj E N hNN hND).cohomologyMap n) :=
  (shear_isCochain E N hNN hND).eventually_bijective_cohomologyMap _
    (closedRangeAt_of_finiteDimensional E) fun q _ => tendsto_const_nhds.congr fun n => by
      change (0 : ℝ) = ‖q - (shearFamily E N hNN).incl n
        ((shearFamily E N hNN).proj n q)‖
      rw [shear_incl_proj, sub_self, norm_zero]

/-- **The heat family of a shear family**: with no constraint (`K = W`) along `atTop`. -/
def shearHeat : ApproxComplexCrime.HeatFamily E ℕ where
  toFamily := shearFamily E N hNN
  K := ⊤
  isClosed_K := by rw [Submodule.top_coe]; exact isClosed_univ
  l := atTop
  tendsto_graphDefect :=
    (shearFamily E N hNN).tendsto_graphDefect_of_tendsto (shear_tendsto_innerDefect E N hNN)

include hND in
/-- **The heat FEEC theorem with crimes applies to a shear family**: closed range, the uniform
discrete Poincaré inequality and static convergence for every datum. -/
theorem shear_heat : ∃ (cP : ℝ) (hcP : 1 ≤ cP) (hP : (shearFamily E N hNN).IsPoincare cP),
    (shearHeat E N hNN).toHeat.Verdict ((shearHeat E N hNN).heatCore
      (closedRangeAt_of_finiteDimensional E) hcP hP (shear_tendsto_staticError E N hNN hND)) :=
  let ⟨cP, hcP, hP⟩ := shear_isPoincare E N hNN hND
  ⟨cP, hcP, hP, (shearHeat E N hNN).heatFEEC _ hcP hP _⟩

/-- `iₙ πₙ = 1` for the cochain projections of a shear family (`iₙ = 1 + hₙ N`). -/
theorem shear_incl_π (n : ℕ) (v : PiLp 2 V) :
    (1 + (perturbMesh n : 𝕜) • N) ((shearCochainProj E N hNN hND).π n v) = v :=
  shear_incl_proj E N hNN n v

include hND in
/-- **The static rate of a shear family**: `e(f) ≤ K ‖f‖ hₙ`. Since `iₙ πₙ = 1`, only the
inner-product defect `‖1 - Jₙ‖ ≤ hₙ ‖N‖ (2 + ‖N‖)` enters the estimate at the projected
approximants (`ApproxComplexCrime.Family.IsCochain.staticError_le_projError`). -/
theorem shear_staticError_le : ∃ K, 0 ≤ K ∧ ∀ n f,
    (shearFamily E N hNN).staticError (closedRangeAt_of_finiteDimensional E) n f ≤
      K * ‖f‖ * perturbMesh n := by
  obtain ⟨cP, hcP, hP⟩ := shear_isPoincare E N hNN hND
  set C := (shearFamily E N hNN).boundConst
  set Cπ := 1 + ‖N‖
  set T := E.totalMixedSolution (closedRangeAt_of_finiteDimensional E)
  have hC : 0 ≤ C := (shearFamily E N hNN).boundConst_nonneg
  have hCπ : 0 ≤ Cπ := by positivity
  set A := C * Cπ + 240 * C * cP ^ 2 * (51 * Cπ + C * (C * Cπ))
  have hA : 0 ≤ A := by positivity
  refine ⟨A * (‖N‖ * (2 + ‖N‖)) * ‖T‖, by positivity, fun n f => ?_⟩
  have h := (shear_isCochain E N hNN hND).staticError_le_projError
    (closedRangeAt_of_finiteDimensional E) (shearCochainProj E N hNN hND) hP hcP n f
  have hz : ∀ v, ‖v - (shearFamily E N hNN).incl n ((shearCochainProj E N hNN hND).π n v)‖ = 0 :=
    fun v => by rw [shear_incl_π, sub_self, norm_zero]
  have hpe : (shearCochainProj E N hNN hND).projError n (T f) = 0 := by
    rw [ApproxComplexCrime.Family.CochainProj.projError, hz, hz, hz, hz, hz]; norm_num
  rw [hpe, hz] at h
  simp only [mul_zero, zero_add, add_zero] at h
  have hJ := ((shearFamily E N hNN).graphDefect_le n).trans (norm_one_sub_shear_J_le E N hNN n)
  have hX : ‖T f‖ ≤ ‖T‖ * ‖f‖ := T.le_opNorm f
  have hm := (perturbMesh_pos n).le
  have h1 := mul_le_mul hJ hX (norm_nonneg _) (by positivity)
  refine h.trans ?_
  have e : C * Cπ * (shearFamily E N hNN).graphDefect n * ‖T f‖ + 240 * C * cP ^ 2 *
      (51 * Cπ * (shearFamily E N hNN).graphDefect n * ‖T f‖ +
        C * (C * Cπ * (shearFamily E N hNN).graphDefect n * ‖T f‖)) =
      A * ((shearFamily E N hNN).graphDefect n * ‖T f‖) := by ring
  rw [e]
  calc A * ((shearFamily E N hNN).graphDefect n * ‖T f‖) ≤
        A * (perturbMesh n * (‖N‖ * (2 + ‖N‖)) * (‖T‖ * ‖f‖)) := mul_le_mul_of_nonneg_left h1 hA
    _ = _ := by ring

include hND in
/-- **The heat rate of a shear family**: the static-rate hypothesis of
`ApproxComplexCrime.HeatFamily.rate_heat_of_static` holds with the regular data `‖f‖ ≤ L`, the
mesh `hₙ` and the order `1` (`shear_staticError_le`, `norm_one_sub_shear_J_le`), so
`‖S(t) x - iₙ e^{-tΔₙ} Rₙ ℓ x‖ ≤ (2 K + C (3 C + 16 c_P² C) K t) L hₙ` on the orbits that stay in
the regular states with bound `L`. -/
theorem shear_rate_heat : ∃ cP K : ℝ, 0 ≤ K ∧ ∀ {L : ℝ}, 0 ≤ L → ∀ {T : ℝ} {x : PiLp 2 V},
    x ∈ (-E.hodgeLaplacian).sqDomain →
    (∀ t ∈ Icc 0 T, (shearHeat E N hNN).toHeat.S t x ∈ E.heatReg (fun L => {f | ‖f‖ ≤ L}) L) →
    ∀ (n : ℕ) {t : ℝ}, t ∈ Icc 0 T →
    ‖(shearHeat E N hNN).toHeat.S t x - (shearHeat E N hNN).toHeat.sol n
        ((shearHeat E N hNN).ritzR n (x, DissipFEEC.genExt (-E.hodgeLaplacian) x)) t‖ ≤
      (2 * K + (shearFamily E N hNN).boundConst * ((3 * (shearFamily E N hNN).boundConst +
        16 * cP ^ 2 * (shearFamily E N hNN).boundConst) * K) * t) * L * perturbMesh n := by
  obtain ⟨cP, hcP, hP⟩ := shear_isPoincare E N hNN hND
  obtain ⟨K, hK0, hK⟩ := shear_staticError_le E N hNN hND
  set K' := max K (‖N‖ * (2 + ‖N‖))
  refine ⟨cP, K', le_max_of_le_left hK0, fun {L} hL {T x} hx hreg n {t} ht => ?_⟩
  have h := (shearHeat E N hNN).rate_heat_of_static (closedRangeAt_of_finiteDimensional E) hcP hP
    (m := perturbMesh) (α := 1) (fun n => (perturbMesh_pos n).le) (le_max_of_le_left hK0)
    (fun {L f} _ hf n => by
      rw [Real.rpow_one]
      refine (hK n f).trans ?_
      have := (perturbMesh_pos n).le
      have : K * ‖f‖ ≤ K' * L := mul_le_mul (le_max_left _ _) hf (norm_nonneg _)
        (le_max_of_le_left hK0)
      nlinarith)
    (fun n => by
      rw [Real.rpow_one]
      exact ((shearFamily E N hNN).graphDefect_le n).trans
        ((norm_one_sub_shear_J_le E N hNN n).trans_eq (by rw [mul_comm])
          |>.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (perturbMesh_pos n).le)))
    hL hx hreg n ht
  rwa [Real.rpow_one] at h

end Shear

/-! ### The witness `𝕜 --id--> 𝕜 --0--> 𝕜` -/

section Witness

instance instFiniteDimensionalW3Self : ∀ i, FiniteDimensional 𝕜 (W3 𝕜 𝕜 𝕜 i)
  | 0 => inferInstanceAs (FiniteDimensional 𝕜 𝕜)
  | 1 => inferInstanceAs (FiniteDimensional 𝕜 𝕜)
  | 2 => inferInstanceAs (FiniteDimensional 𝕜 𝕜)

variable (𝕜) in
/-- The short complex `𝕜 --id--> 𝕜 --0--> 𝕜`. -/
def idZeroShort : ShortHilbertComplex 𝕜 𝕜 𝕜 𝕜 :=
  ShortHilbertComplex.ofBounded (ContinuousLinearMap.id 𝕜 𝕜) 0 fun _ => rfl

variable (𝕜) in
/-- **The complex `𝕜 --id--> 𝕜 --0--> 𝕜`** on `Fin 3`: `𝐝 (a, b, c) = (0, a, 0)`, harmonic forms
`𝕜 (0, 0, 1)`. -/
abbrev idZeroComplex : HilbertComplex 𝕜 ComplexShape.fin3 (W3 𝕜 𝕜 𝕜) :=
  (idZeroShort 𝕜).toHilbertComplex

/-- The degree-`0` component of a point of `𝕜 × 𝕜 × 𝕜`, in `𝕜`. -/
abbrev coord0 (u : PiLp 2 (W3 𝕜 𝕜 𝕜)) : 𝕜 := u 0

/-- The degree-`2` component of a point of `𝕜 × 𝕜 × 𝕜`, in `𝕜`. -/
abbrev coord2 (u : PiLp 2 (W3 𝕜 𝕜 𝕜)) : 𝕜 := u 2

theorem norm_mk3_zero (b : 𝕜) : ‖(mk3 (0 : 𝕜) b (0 : 𝕜) : PiLp 2 (W3 𝕜 𝕜 𝕜))‖ = ‖b‖ := by
  have h := norm_sq_mk3 (𝕜 := 𝕜) (0 : 𝕜) b (0 : 𝕜)
  rw [norm_zero] at h
  have := norm_nonneg (mk3 (0 : 𝕜) b (0 : 𝕜) : PiLp 2 (W3 𝕜 𝕜 𝕜))
  nlinarith [norm_nonneg b]

theorem idZero_totalDL_zero (v : PiLp 2 (W3 𝕜 𝕜 𝕜)) : ((idZeroComplex 𝕜).totalDL v) 0 = 0 := by
  change ((idZeroComplex 𝕜).totalD ⟨v, _⟩) 0 = 0
  rw [totalD_apply, Fin.sum_univ_three]
  simp only [apply_eq_zero_of_eq_zero (show (idZeroComplex 𝕜).d 0 0 = 0 from rfl),
    apply_eq_zero_of_eq_zero (show (idZeroComplex 𝕜).d 1 0 = 0 from rfl),
    apply_eq_zero_of_eq_zero (show (idZeroComplex 𝕜).d 2 0 = 0 from rfl), add_zero]

theorem idZero_totalDL_one (v : PiLp 2 (W3 𝕜 𝕜 𝕜)) :
    ((idZeroComplex 𝕜).totalDL v) 1 = coord0 v := by
  change ((idZeroComplex 𝕜).totalD ⟨v, _⟩) 1 = _
  rw [totalD_apply, Fin.sum_univ_three]
  simp only [apply_eq_zero_of_eq_zero (show (idZeroComplex 𝕜).d 1 1 = 0 from rfl),
    apply_eq_zero_of_eq_zero (show (idZeroComplex 𝕜).d 2 1 = 0 from rfl), add_zero]
  rfl

theorem idZero_totalDL_two (v : PiLp 2 (W3 𝕜 𝕜 𝕜)) : ((idZeroComplex 𝕜).totalDL v) 2 = 0 := by
  change ((idZeroComplex 𝕜).totalD ⟨v, _⟩) 2 = 0
  rw [totalD_apply, Fin.sum_univ_three]
  simp only [apply_eq_zero_of_eq_zero (show (idZeroComplex 𝕜).d 0 2 = 0 from rfl),
    apply_eq_zero_of_eq_zero (show (idZeroComplex 𝕜).d 2 2 = 0 from rfl), add_zero, zero_add]
  rfl

/-- `𝐝 (a, b, c) = (0, a, 0)`. -/
theorem idZero_totalDL (v : PiLp 2 (W3 𝕜 𝕜 𝕜)) :
    (idZeroComplex 𝕜).totalDL v = mk3 0 (coord0 v) 0 := by
  refine PiLp.ext fun j => ?_
  fin_cases j
  exacts [idZero_totalDL_zero v, idZero_totalDL_one v, idZero_totalDL_two v]

variable (𝕜) in
/-- **The shear** `N (a, b, c) = (0, c, 0)`: `N² = 0`, `N 𝐝 = 𝐝 N = 0`, and `N` maps the
harmonic form `(0, 0, 1)` to the boundary `(0, 1, 0) = 𝐝 (1, 0, 0)`. -/
def idZeroN : PiLp 2 (W3 𝕜 𝕜 𝕜) →L[𝕜] PiLp 2 (W3 𝕜 𝕜 𝕜) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => mk3 0 (coord2 v) 0
      map_add' := fun v w => PiLp.ext fun i => by
        fin_cases i
        exacts [(add_zero (0 : 𝕜)).symm, rfl, (add_zero (0 : 𝕜)).symm]
      map_smul' := fun a v => PiLp.ext fun i => by
        fin_cases i
        exacts [(mul_zero a).symm, rfl, (mul_zero a).symm] }

theorem idZeroN_apply (v : PiLp 2 (W3 𝕜 𝕜 𝕜)) : idZeroN 𝕜 v = mk3 0 (coord2 v) 0 :=
  rfl

theorem idZeroN_idZeroN (v : PiLp 2 (W3 𝕜 𝕜 𝕜)) : idZeroN 𝕜 (idZeroN 𝕜 v) = 0 :=
  mk3_zero

theorem idZeroN_totalDL (v : PiLp 2 (W3 𝕜 𝕜 𝕜)) :
    idZeroN 𝕜 ((idZeroComplex 𝕜).totalDL v) = (idZeroComplex 𝕜).totalDL (idZeroN 𝕜 v) := by
  rw [idZero_totalDL, idZero_totalDL]
  rfl

variable (𝕜) in
/-- **The shear family of `𝕜 --id--> 𝕜 --0--> 𝕜`**: `iₙ (a, b, c) = (a, b + hₙ c, c)`. -/
abbrev shearIdZero : ApproxComplexCrime.Family (idZeroComplex 𝕜) ℕ :=
  shearFamily (idZeroComplex 𝕜) (idZeroN 𝕜) idZeroN_idZeroN

variable (𝕜) in
/-- Its cochain projections `πₙ = 1 - hₙ N`. -/
abbrev shearIdZeroProj : (shearIdZero 𝕜).CochainProj (1 + ‖idZeroN 𝕜‖) :=
  shearCochainProj (idZeroComplex 𝕜) (idZeroN 𝕜) idZeroN_idZeroN idZeroN_totalDL

variable (𝕜) in
/-- The harmonic form `p = (0, 0, 1)`. -/
abbrev harmonicDatum : PiLp 2 (W3 𝕜 𝕜 𝕜) := mk3 0 0 1

theorem idZeroN_harmonicDatum :
    idZeroN 𝕜 (harmonicDatum 𝕜) = (idZeroComplex 𝕜).totalDL (mk3 1 0 0) := by
  rw [idZero_totalDL]
  rfl

/-- The boundaries of `𝕜 --id--> 𝕜 --0--> 𝕜` are orthogonal to `(0, 0, 1)`. -/
theorem inner_totalDL_harmonicDatum (v : PiLp 2 (W3 𝕜 𝕜 𝕜)) :
    ⟪(idZeroComplex 𝕜).totalDL v, harmonicDatum 𝕜⟫_𝕜 = 0 := by
  rw [idZero_totalDL, inner_mk3, RCLike.inner_apply', RCLike.inner_apply',
    RCLike.inner_apply']
  simp

/-- **`(0, 0, 1)` is harmonic.** -/
theorem harmonicDatum_mem_harmonic :
    harmonicDatum 𝕜 ∈ (idZeroComplex 𝕜).total.harmonic () := by
  refine (idZeroComplex 𝕜).total.mem_harmonic_iff.2 ⟨LinearPMap.mem_ker_iff.2
    ⟨⟨_, (idZeroComplex 𝕜).mem_totalD_domain_of_finiteDimensional _⟩, rfl, ?_⟩,
    (Submodule.mem_orthogonal _ _).2 ?_⟩
  · change (idZeroComplex 𝕜).totalDL (harmonicDatum 𝕜) = 0
    rw [idZero_totalDL]
    exact mk3_zero
  · rintro _ ⟨y, rfl⟩
    change ⟪(idZeroComplex 𝕜).totalDL y, harmonicDatum 𝕜⟫_𝕜 = 0
    exact inner_totalDL_harmonicDatum _

/-- **`(0, 0, 1)` is a discrete harmonic form** at every level (`𝐝ₙ = 𝐝`). -/
theorem harmonicDatum_mem_cpx_harmonic (n : ℕ) :
    harmonicDatum 𝕜 ∈ ((shearIdZero 𝕜).cpx n).harmonic () := by
  refine (mem_diffComplex_harmonic _ _).2 ⟨?_, ext_inner_left 𝕜 fun w => ?_⟩
  · change (idZeroComplex 𝕜).totalDL (harmonicDatum 𝕜) = 0
    rw [idZero_totalDL]
    exact mk3_zero
  · rw [ContinuousLinearMap.adjoint_inner_right, inner_zero_right]
    exact inner_totalDL_harmonicDatum w

/-- `iₙ* p = p`: `⟪N w, p⟫ = 0`. -/
theorem adjoint_shear_incl_harmonicDatum (n : ℕ) :
    ((shearIdZero 𝕜).incl n).adjoint (harmonicDatum 𝕜) = harmonicDatum 𝕜 :=
  ext_inner_left 𝕜 fun w => by
    rw [ContinuousLinearMap.adjoint_inner_right, shear_incl_apply, inner_add_left,
      inner_smul_left, idZeroN_apply, inner_mk3, RCLike.inner_apply', RCLike.inner_apply',
      RCLike.inner_apply']
    simp

/-- `P_ℌₙ πₙ p = p`: `πₙ p = p - hₙ 𝐝 (1, 0, 0)` and `𝐝ₙ = 𝐝`. -/
theorem harmonicProj_shear_proj_harmonicDatum (n : ℕ) :
    (((shearIdZero 𝕜).cpx n).harmonic ()).starProjection
      ((shearIdZero 𝕜).proj n (harmonicDatum 𝕜)) = harmonicDatum 𝕜 := by
  have hb : (idZeroComplex 𝕜).totalDL (mk3 1 0 0) ∈ (((shearIdZero 𝕜).cpx n).harmonic ())ᗮ :=
    (Submodule.mem_orthogonal _ _).2 fun q hq => by
      obtain ⟨-, hq0⟩ := (mem_diffComplex_harmonic _ _).1 hq
      change ⟪q, (shearIdZero 𝕜).D n (mk3 1 0 0)⟫_𝕜 = 0
      rw [← ContinuousLinearMap.adjoint_inner_left, hq0, inner_zero_left]
  rw [shear_proj_apply, idZeroN_harmonicDatum, _root_.map_sub, _root_.map_smul,
    (Submodule.starProjection_apply_eq_zero_iff _).2 hb, smul_zero, sub_zero,
    Submodule.starProjection_eq_self_iff.2 (harmonicDatum_mem_cpx_harmonic n)]

theorem norm_harmonicDatum_sub_shear_incl (n : ℕ) :
    ‖harmonicDatum 𝕜 - (shearIdZero 𝕜).incl n (harmonicDatum 𝕜)‖ = perturbMesh n := by
  rw [shear_incl_apply, sub_add_cancel_left, norm_neg, norm_smul, idZeroN_apply,
    norm_mk3_zero]
  change ‖((perturbMesh n : ℝ) : 𝕜)‖ * ‖(1 : 𝕜)‖ = _
  rw [norm_one, mul_one, RCLike.norm_ofReal, abs_of_pos (perturbMesh_pos n)]

/-- **The harmonic gap is positive**: `‖p - iₙ P_ℌₙ πₙ p‖ = hₙ`. -/
theorem norm_harmonicDatum_sub_shear_gap (n : ℕ) :
    ‖harmonicDatum 𝕜 - (shearIdZero 𝕜).incl n
      ((((shearIdZero 𝕜).cpx n).harmonic ()).starProjection
        ((shearIdZero 𝕜).proj n (harmonicDatum 𝕜)))‖ = perturbMesh n := by
  rw [harmonicProj_shear_proj_harmonicDatum, norm_harmonicDatum_sub_shear_incl]

/-- **The read discrete harmonic form `iₙ p = (0, hₙ, 1)` is not harmonic**: it is not orthogonal
to the boundary `𝐝 (1, 0, 0) = (0, 1, 0)`. -/
theorem shear_incl_harmonicDatum_not_mem_harmonic (n : ℕ) :
    (shearIdZero 𝕜).incl n (harmonicDatum 𝕜) ∉ (idZeroComplex 𝕜).total.harmonic () := by
  intro h
  have hb : (idZeroComplex 𝕜).totalDL (mk3 1 0 0) ∈ (idZeroComplex 𝕜).total.boundaries () :=
    ⟨⟨mk3 1 0 0, (idZeroComplex 𝕜).mem_totalD_domain_of_finiteDimensional _⟩, rfl⟩
  have h0 := Submodule.inner_right_of_mem_orthogonal hb
    ((idZeroComplex 𝕜).total.mem_harmonic_iff.1 h).2
  rw [shear_incl_apply, idZeroN_harmonicDatum, inner_add_right, inner_smul_right,
    inner_totalDL_harmonicDatum, zero_add, idZero_totalDL, inner_mk3] at h0
  simp only [RCLike.inner_apply', _root_.map_zero, zero_mul, zero_add, add_zero] at h0
  rw [show coord0 (mk3 (1 : 𝕜) 0 0) = 1 from rfl, _root_.map_one, mul_one, mul_one] at h0
  exact (perturbMesh_pos n).ne' (by exact_mod_cast h0)

/-- **The method is not exact**: the static error at the harmonic datum is at least `hₙ`
(`‖P_ℌ p - iₙ P_ℌₙ iₙ* p‖ = ‖p - iₙ p‖`, `ApproxComplexCrime.Family.norm_harmonicProj_sub_le`). -/
theorem shear_staticError_pos (n : ℕ) :
    0 < (shearIdZero 𝕜).staticError (closedRangeAt_of_finiteDimensional _) n
      (harmonicDatum 𝕜) := by
  refine (perturbMesh_pos n).trans_le ?_
  have h := (shearIdZero 𝕜).norm_harmonicProj_sub_le (closedRangeAt_of_finiteDimensional _) n
    (harmonicDatum 𝕜)
  rwa [Submodule.starProjection_eq_self_iff.2 harmonicDatum_mem_harmonic,
    adjoint_shear_incl_harmonicDatum, Family.harmonicProj,
    Submodule.starProjection_eq_self_iff.2 (harmonicDatum_mem_cpx_harmonic n),
    norm_harmonicDatum_sub_shear_incl] at h

/-- **The reading maps are not isometric**: `Jₙ ≠ 1`, since the gap
`‖p - iₙ P_ℌₙ πₙ p‖ = hₙ > 0` is bounded by `C C_π ‖1 - Jₙ‖_{Vₙ} ‖p‖` alone (`iₙ πₙ = 1`;
`ApproxComplexCrime.Family.IsCochain.norm_sub_incl_harmonic_le`). -/
theorem shear_J_ne_one (n : ℕ) : (shearIdZero 𝕜).J n ≠ 1 := fun hJ => by
  have h : perturbMesh n ≤ _ := (norm_harmonicDatum_sub_shear_gap n).symm.le.trans
    ((shear_isCochain (idZeroComplex 𝕜) (idZeroN 𝕜) idZeroN_idZeroN
      idZeroN_totalDL).norm_sub_incl_harmonic_le (shearIdZeroProj 𝕜) n harmonicDatum_mem_harmonic)
  have e : ‖harmonicDatum 𝕜 - (shearIdZero 𝕜).incl n
      ((shearIdZeroProj 𝕜).π n (harmonicDatum 𝕜))‖ = 0 := by
    change ‖harmonicDatum 𝕜 - (shearIdZero 𝕜).incl n
      ((shearIdZero 𝕜).proj n (harmonicDatum 𝕜))‖ = 0
    rw [shear_incl_proj, sub_self, norm_zero]
  rw [e, (shearIdZero 𝕜).graphDefect_eq_zero hJ] at h
  simp only [mul_zero, zero_mul, add_zero] at h
  exact (perturbMesh_pos n).not_ge h

/-- **The cohomology is not zero**: `H(𝐝) ≅ ℌ ∋ (0, 0, 1)`. -/
theorem nontrivial_idZero_cohomology : Nontrivial ((idZeroComplex 𝕜).total.cohomology ()) := by
  have : Nontrivial ((idZeroComplex 𝕜).total.harmonic ()) :=
    ⟨⟨⟨_, harmonicDatum_mem_harmonic⟩, 0, fun h => by
      have := congrArg (fun x : (idZeroComplex 𝕜).total.harmonic () =>
        coord2 (x : PiLp 2 (W3 𝕜 𝕜 𝕜))) h
      exact one_ne_zero (α := 𝕜) this⟩⟩
  exact ((idZeroComplex 𝕜).total.cohomologyEquivHarmonic
    ((idZeroComplex 𝕜).closedRangeAt_total (closedRangeAt_of_finiteDimensional _)
      ())).toEquiv.nontrivial

variable (𝕜) in
/-- **Non-vacuity of the cochain case with harmonic forms**: for the shear family of
`𝕜 --id--> 𝕜 --0--> 𝕜` (cochain reading maps `iₙ = 1 + hₙ N` that are not isometric,
`‖1 - Jₙ‖ → 0`), closed range and the uniform discrete Poincaré inequality hold, the static errors
tend to `0` for every datum and are positive at the harmonic datum `p = (0, 0, 1)`; `p` is a
continuous and a discrete harmonic form but `iₙ p` is not harmonic, the harmonic gap
`‖p - iₙ P_ℌₙ πₙ p‖ = hₙ` is positive while `iₙ πₙ p = p`; the cohomology is not zero and the
maps `[z] ↦ [πₙ z]` are eventually isomorphisms; and the heat FEEC theorem with crimes applies. -/
theorem shear_nonvacuous :
    (∀ i, (idZeroComplex 𝕜).ClosedRangeAt i) ∧
      (∃ cP, 1 ≤ cP ∧ (shearIdZero 𝕜).IsPoincare cP) ∧ (shearIdZero 𝕜).IsCochain ∧
      (∀ n, (shearIdZero 𝕜).J n ≠ 1) ∧
      Tendsto (fun n => ‖1 - (shearIdZero 𝕜).J n‖) atTop (𝓝 0) ∧
      (∀ f, Tendsto (fun n => (shearIdZero 𝕜).staticError
        (closedRangeAt_of_finiteDimensional _) n f) atTop (𝓝 0)) ∧
      (∀ n, 0 < (shearIdZero 𝕜).staticError (closedRangeAt_of_finiteDimensional _) n
        (harmonicDatum 𝕜)) ∧
      harmonicDatum 𝕜 ∈ (idZeroComplex 𝕜).total.harmonic () ∧
      (∀ n, harmonicDatum 𝕜 ∈ ((shearIdZero 𝕜).cpx n).harmonic () ∧
        (shearIdZero 𝕜).incl n (harmonicDatum 𝕜) ∉ (idZeroComplex 𝕜).total.harmonic ()) ∧
      (∀ n, ‖harmonicDatum 𝕜 - (shearIdZero 𝕜).incl n
          ((((shearIdZero 𝕜).cpx n).harmonic ()).starProjection
            ((shearIdZero 𝕜).proj n (harmonicDatum 𝕜)))‖ = perturbMesh n ∧
        (shearIdZero 𝕜).incl n ((shearIdZero 𝕜).proj n (harmonicDatum 𝕜)) =
          harmonicDatum 𝕜) ∧
      Nontrivial ((idZeroComplex 𝕜).total.cohomology ()) ∧
      (∀ᶠ n in atTop, Function.Bijective ((shearIdZeroProj 𝕜).cohomologyMap n)) ∧
      ∃ (cP : ℝ) (hcP : 1 ≤ cP) (hP : (shearIdZero 𝕜).IsPoincare cP),
        (shearHeat (idZeroComplex 𝕜) (idZeroN 𝕜) idZeroN_idZeroN).toHeat.Verdict
          ((shearHeat (idZeroComplex 𝕜) (idZeroN 𝕜) idZeroN_idZeroN).heatCore
            (closedRangeAt_of_finiteDimensional _) hcP hP
            (shear_tendsto_staticError _ _ idZeroN_idZeroN idZeroN_totalDL)) :=
  ⟨closedRangeAt_of_finiteDimensional _, shear_isPoincare _ _ _ idZeroN_totalDL,
    shear_isCochain _ _ _ idZeroN_totalDL, shear_J_ne_one, shear_tendsto_innerDefect _ _ _,
    shear_tendsto_staticError _ _ _ idZeroN_totalDL, shear_staticError_pos,
    harmonicDatum_mem_harmonic,
    fun n => ⟨harmonicDatum_mem_cpx_harmonic n, shear_incl_harmonicDatum_not_mem_harmonic n⟩,
    fun n => ⟨norm_harmonicDatum_sub_shear_gap n, shear_incl_proj _ _ _ n _⟩,
    nontrivial_idZero_cohomology, shear_eventually_bijective_cohomologyMap _ _ _ idZeroN_totalDL,
    shear_heat _ _ _ idZeroN_totalDL⟩

end Witness

end ApproxComplexCrime

end Feec.HilbertComplex
